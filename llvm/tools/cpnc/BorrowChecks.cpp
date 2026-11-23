#include "Sema.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/MathExtras.h"

using namespace cpn;
namespace {
struct Slot {
  llvm::Value *Base;
  int64_t Offset;
};
struct Invocation {
  llvm::CallBase &Call;
  const Invocation *Caller;
};

// Trace a pointer through native spills. Only a reaching store to the same
// slot establishes its source. An intervening possible alias makes it unknown.
class EscapeCheck {
  const llvm::DataLayout &DL;
  llvm::SmallPtrSet<llvm::Value *, 8> Automatic;
  llvm::SmallPtrSet<llvm::Value *, 8> NoRetention, NoPublication;
  llvm::Value *Result;
  llvm::Type *ResultType;
  const std::map<llvm::Value *, llvm::Type *> &Globals;
  const llvm::SmallPtrSetImpl<llvm::Function *> &Definitions;
  const llvm::SmallPtrSetImpl<llvm::Function *> &TrivialDrops;
  llvm::SmallPtrSet<llvm::BasicBlock *, 32> Reachable;

  Slot slot(llvm::Value *P) const {
    int64_t Offset = 0;
    auto *Base = llvm::GetPointerBaseWithConstantOffset(P, Offset, DL);
    return {Base, Offset};
  }
  bool disjoint(Slot A, Slot B, uint64_t Size) const {
    if (A.Base == B.Base) {
      if (B.Offset >= A.Offset)
        return uint64_t(B.Offset) - uint64_t(A.Offset) >= DL.getPointerSize();
      return uint64_t(A.Offset) - uint64_t(B.Offset) >= Size;
    }
    if (llvm::isa<llvm::AllocaInst>(A.Base) ||
        llvm::isa<llvm::AllocaInst>(B.Base)) {
      auto Known = [&](llvm::Value *V) {
        return llvm::isa<llvm::AllocaInst, llvm::GlobalVariable,
                         llvm::Argument>(V);
      };
      return Known(A.Base) && Known(B.Base);
    }
    return llvm::isa<llvm::GlobalVariable>(A.Base) &&
           llvm::isa<llvm::GlobalVariable>(B.Base);
  }
  bool mayChange(llvm::Instruction &I, Slot Target) const {
    if (!I.mayWriteToMemory())
      return false;
    if (auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto Dest = slot(S->getPointerOperand());
      // Pointer bounds occupy independent compiler-owned sidecar storage.
      if (auto *G = llvm::dyn_cast<llvm::GlobalVariable>(Dest.Base);
          G && (G->getName() == "cpn.pointer.call" ||
                G->getName() == "cpn.pointer.objects"))
        return false;
      if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Dest.Base))
        if (auto *F = Call->getCalledFunction();
            F && F->getName() == "cpn.pointer.field")
          return false;
      return !disjoint(Target, Dest,
                       DL.getTypeStoreSize(S->getValueOperand()->getType()));
    }
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I))
      if (auto *F = Call->getCalledFunction()) {
        const auto Name = F->getName();
        if (Name == "cpn.static.read" || Name == "cpn.pointer.field" ||
            Name == "cpn.slot.begin" || Name == "cpn.slot.link" ||
            Name == "cpn.slot.find" || Name == "cpn.slot.child" ||
            Name == "cpn.slot.release" || Name == "cpn.generation" ||
            Name == "cpn.borrow.valid" || Name == "cpn.whole.epoch")
          return false;
        if (F->getIntrinsicID() == llvm::Intrinsic::lifetime_start ||
            F->getIntrinsicID() == llvm::Intrinsic::lifetime_end)
          return false;
        if (Name == "cpn.slot.retire" && !TrivialDrops.empty())
          if (auto *Registration =
                  llvm::dyn_cast<llvm::AllocaInst>(Call->getArgOperand(0)))
            for (auto *Use : Registration->users())
              if (auto *Begin = llvm::dyn_cast<llvm::CallBase>(Use))
                if (auto *Callee = Begin->getCalledFunction();
                    Callee && Callee->getName() == "cpn.slot.begin" &&
                    Begin->getArgOperand(0) == Registration &&
                    TrivialDrops.contains(llvm::dyn_cast<llvm::Function>(
                        Begin->getArgOperand(3))))
                  return false;
      }
    return true;
  }
  using Prohibited = llvm::function_ref<bool(llvm::Value *)>;

  bool originatesFrom(llvm::Value *V, unsigned &Budget, Prohibited Denied,
                      const Invocation *Activation = nullptr) const {
    if (!Budget)
      return false;
    --Budget;
    auto *Base = llvm::getUnderlyingObject(V);
    if (Denied(Base))
      return true;
    if (auto *A = llvm::dyn_cast<llvm::Argument>(Base); A && Activation)
      return originatesFrom(Activation->Call.getArgOperand(A->getArgNo()),
                            Budget, Denied, Activation->Caller);
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Base)) {
      auto *Callee = Call->getCalledFunction();
      if (!Callee || !Definitions.contains(Callee))
        return false;
      Invocation Nested{*Call, Activation};
      llvm::SmallPtrSet<llvm::BasicBlock *, 8> Visited;
      llvm::SmallVector<llvm::BasicBlock *> Work{&Callee->getEntryBlock()};
      while (Budget && !Work.empty()) {
        --Budget;
        auto *Block = Work.pop_back_val();
        if (!Visited.insert(Block).second)
          continue;
        if (auto *Ret =
                llvm::dyn_cast<llvm::ReturnInst>(Block->getTerminator()))
          if (originatesFrom(Ret->getReturnValue(), Budget, Denied, &Nested))
            return true;
        if (auto *Next = successor(Block))
          Work.push_back(Next);
        else
          llvm::append_range(Work, llvm::successors(Block));
      }
      return false;
    }
    if (auto *Select = llvm::dyn_cast<llvm::SelectInst>(Base)) {
      if (auto *Known =
              llvm::dyn_cast<llvm::ConstantInt>(Select->getCondition()))
        return originatesFrom(Select->getOperand(Known->isZero() ? 2 : 1),
                              Budget, Denied, Activation);
      return originatesFrom(Select->getTrueValue(), Budget, Denied,
                            Activation) ||
             originatesFrom(Select->getFalseValue(), Budget, Denied,
                            Activation);
    }
    auto *L = llvm::dyn_cast<llvm::LoadInst>(Base);
    if (!L || !L->getType()->isPointerTy() || L->isVolatile())
      return false;
    return reachingOrigin(slot(L->getPointerOperand()), L->getParent(),
                          L->getIterator(), Budget, Denied, Activation);
  }

  bool reachingOrigin(Slot Target, llvm::BasicBlock *BB,
                      llvm::BasicBlock::iterator It, unsigned &Budget,
                      Prohibited Denied, const Invocation *Activation) const {
    while (Budget) {
      --Budget;
      if (It == BB->begin()) {
        // An unchanged capture field at callee entry still designates the
        // value stored in the receiver before the call.
        if (Activation && BB == &BB->getParent()->getEntryBlock()) {
          auto *A = llvm::dyn_cast<llvm::Argument>(Target.Base);
          if (!A)
            return false;
          auto &Call = Activation->Call;
          auto Actual = slot(Call.getArgOperand(A->getArgNo()));
          if (llvm::AddOverflow(Actual.Offset, Target.Offset, Actual.Offset))
            return false;
          return reachingOrigin(Actual, Call.getParent(), Call.getIterator(),
                                Budget, Denied, Activation->Caller);
        }
        BB = BB->getSinglePredecessor();
        if (!BB)
          break;
        It = BB->end();
        continue;
      }
      auto &I = *--It;
      if (auto *S = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto Dest = slot(S->getPointerOperand());
        if (Dest.Base == Target.Base && Dest.Offset == Target.Offset &&
            S->getValueOperand()->getType()->isPointerTy())
          return originatesFrom(S->getValueOperand(), Budget, Denied,
                                Activation);
      }
      if (mayChange(I, Target))
        break;
    }
    return false;
  }
  bool pointerAt(llvm::Type *T, uint64_t Offset) const {
    while (Offset < DL.getTypeAllocSize(T)) {
      if (T->isPointerTy())
        return !Offset;
      if (auto *S = llvm::dyn_cast<llvm::StructType>(T)) {
        auto *Layout = DL.getStructLayout(S);
        unsigned I = Layout->getElementContainingOffset(Offset);
        Offset -= Layout->getElementOffset(I);
        T = S->getElementType(I);
      } else if (auto *A = llvm::dyn_cast<llvm::ArrayType>(T)) {
        T = A->getElementType();
        Offset %= DL.getTypeAllocSize(T);
      } else
        break;
    }
    return false;
  }
  llvm::BasicBlock *successor(llvm::BasicBlock *BB) const {
    if (auto *Next = BB->getUniqueSuccessor())
      return Next;
    if (auto *B = llvm::dyn_cast<llvm::CondBrInst>(BB->getTerminator()))
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(B->getCondition()))
        return B->getSuccessor(C->isZero() ? 1 : 0);
    return nullptr;
  }
  bool survivesReturn(llvm::StoreInst &S, Slot Target, unsigned &Budget) const {
    llvm::SmallPtrSet<llvm::BasicBlock *, 8> Visited;
    llvm::SmallVector<llvm::Instruction *, 8> Work{S.getNextNode()};
    while (Budget && !Work.empty()) {
      auto *I = Work.pop_back_val();
      for (; I && Budget; I = I->getNextNode()) {
        --Budget;
        if (llvm::isa<llvm::ReturnInst>(I))
          return true;
        if (mayChange(*I, Target))
          break;
        if (!I->isTerminator())
          continue;
        auto Push = [&](llvm::BasicBlock *Block) {
          if (Visited.insert(Block).second)
            Work.push_back(&Block->front());
        };
        if (auto *Next = successor(I->getParent()))
          Push(Next);
        else
          for (auto *Next : llvm::successors(I->getParent()))
            Push(Next);
      }
    }
    return false;
  }

public:
  EscapeCheck(Context &U, Function &D, llvm::Function &F,
              const std::map<llvm::Value *, llvm::Type *> &Globals,
              const llvm::SmallPtrSetImpl<llvm::Function *> &Definitions,
              const llvm::SmallPtrSetImpl<llvm::Function *> &TrivialDrops)
      : DL(U.M.getDataLayout()), Result(nullptr), ResultType(nullptr),
        Globals(Globals), Definitions(Definitions), TrivialDrops(TrivialDrops) {
    unsigned I = 0;
    if (U.aggregate(D.Result)) {
      Result = F.getArg(I++);
      ResultType = U.ir(D.Result);
    }
    if (!D.Owner.empty() && !D.isStatic())
      ++I;
    for (unsigned P = 0; P < D.Params.size(); ++P) {
      auto *A = F.getArg(I++);
      if (U.aggregate(D.Params[P]))
        Automatic.insert(A);
      if (D.NoEscape.count(P))
        NoRetention.insert(A);
      if ((D.NoEscape.count(P) || !D.BorrowedResult.empty()) &&
          !D.BorrowedResult.count(P))
        NoPublication.insert(A);
    }
    llvm::SmallVector<llvm::BasicBlock *> Work{&F.getEntryBlock()};
    while (!Work.empty()) {
      auto *BB = Work.pop_back_val();
      if (!Reachable.insert(BB).second)
        continue;
      if (auto *Next = successor(BB)) {
        Work.push_back(Next);
        continue;
      }
      llvm::append_range(Work, llvm::successors(BB));
    }
  }
  void verify(const Token &At) const {
    auto IsAutomatic = [&](llvm::Value *V) {
      return llvm::isa<llvm::AllocaInst>(V) || Automatic.contains(V);
    };
    auto Check = [&](llvm::Value *V, bool Returning, bool Direct) {
      unsigned Budget = 256;
      if (originatesFrom(V, Budget, IsAutomatic))
        fail(At, Direct ? "borrow of automatic storage escapes the function"
                        : "borrow of automatic storage escapes through the "
                          "result or static object");
      const auto &Restricted = Returning ? NoPublication : NoRetention;
      if (Restricted.empty())
        return;
      Budget = 256;
      if (originatesFrom(V, Budget, [&](llvm::Value *Source) {
            return Restricted.contains(Source);
          }))
        fail(At, "escaping borrow violates the declared parameter contract");
    };
    for (auto *BB : Reachable)
      for (auto &I : *BB) {
        if (auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I))
          if (auto *V = R->getReturnValue(); V && V->getType()->isPointerTy())
            Check(V, true, true);
        auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!S || !S->getValueOperand()->getType()->isPointerTy())
          continue;
        auto Dest = slot(S->getPointerOperand());
        auto G = Globals.find(Dest.Base);
        auto *Type = Dest.Base == Result  ? ResultType
                     : G != Globals.end() ? G->second
                                          : nullptr;
        unsigned Budget = 256;
        if (Type && Dest.Offset >= 0 && pointerAt(Type, Dest.Offset) &&
            survivesReturn(*S, Dest, Budget))
          Check(S->getValueOperand(), Dest.Base == Result, false);
      }
  }
};
} // namespace

void Context::checkBorrowEscapes() {
  std::map<llvm::Value *, llvm::Type *> StaticObjects;
  for (const auto &[Name, V] : Globals)
    if (auto *G = llvm::dyn_cast_or_null<llvm::GlobalVariable>(V.Address))
      StaticObjects[G] = G->getValueType();
  llvm::SmallPtrSet<llvm::Function *, 32> Definitions;
  for (auto &D : Functions)
    for (auto *F : {D.IR, D.BaseIR})
      if (F && !F->empty())
        Definitions.insert(F);
  // When no extent can be replaced, an implicit closure drop with scalar
  // captures only updates the compiler's lifetime sidecars.
  llvm::SmallPtrSet<llvm::Function *, 8> TrivialDrops;
  auto *ExtentCheck = M.getFunction("cpn.extent.valid");
  if (!ExtentCheck || ExtentCheck->use_empty())
    for (const auto &[Type, Drop] : CleanupEntries)
      if (auto R = Records.find(Type);
          R != Records.end() && R->second.Decl.K == Node::Lambda &&
          llvm::none_of(R->second.Fields,
                        [&](const Field &F) { return aggregate(F.Type); }))
        TrivialDrops.insert(Drop);
  for (auto &D : Functions)
    for (auto *F : {D.IR, D.BaseIR})
      if (Definitions.contains(F))
        EscapeCheck(*this, D, *F, StaticObjects, Definitions, TrivialDrops)
            .verify(D.Decl.At);
}
