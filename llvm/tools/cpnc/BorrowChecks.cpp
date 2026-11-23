#include "Sema.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/MathExtras.h"

using namespace cpn;
namespace {
constexpr llvm::StringRef BorrowMetadata = "cpn.borrow.call";
constexpr llvm::StringRef TemporaryEnd = "cpn.borrow.temporary.end";
enum CallField {
  Line,
  Column,
  Disposition,
  ReadOnly,
  Retainable,
  ResultSources
};
enum Mode { Suppressed, Anomaly, Error };

unsigned callSetting(const llvm::MDNode &Descriptor, unsigned Field) {
  return llvm::mdconst::extract<llvm::ConstantInt>(Descriptor.getOperand(Field))
      ->getZExtValue();
}

llvm::SmallVector<unsigned> positions(const llvm::MDNode *Descriptor,
                                      unsigned Field) {
  llvm::SmallVector<unsigned> Result;
  if (Descriptor)
    for (const auto &Operand :
         llvm::cast<llvm::MDNode>(Descriptor->getOperand(Field))->operands())
      Result.push_back(
          llvm::mdconst::extract<llvm::ConstantInt>(Operand)->getZExtValue());
  return Result;
}

struct Slot {
  llvm::Value *Base;
  int64_t Offset;
  bool operator==(const Slot &Other) const {
    return Base == Other.Base && Offset == Other.Offset;
  }
};
struct Condition {
  Slot Subject;
  const llvm::Constant *Number;
  bool Equal;
  bool Memory = false;
};
using Conditions = llvm::SmallVector<Condition, 4>;
struct Invocation {
  llvm::CallBase &Call;
  const Invocation *Caller;
};
using UnionPayloads =
    std::map<llvm::Type *, llvm::SmallVector<llvm::Type *, 2>>;

// Trace a pointer through native spills. Only a reaching store to the same
// slot establishes its source. An intervening possible alias makes it unknown.
class EscapeCheck {
  const llvm::DataLayout &DL;
  llvm::Function &Root;
  llvm::StringRef Input;
  llvm::SmallPtrSet<llvm::Value *, 8> Automatic;
  llvm::SmallPtrSet<llvm::Value *, 8> NoRetention, NoPublication;
  llvm::Value *Result;
  llvm::Type *ResultType;
  const std::map<llvm::Value *, llvm::Type *> &Globals;
  const UnionPayloads &Payloads;
  const llvm::SmallPtrSetImpl<llvm::Function *> &Definitions;
  const llvm::SmallPtrSetImpl<llvm::Function *> &TrivialDrops;
  bool StableRegistrations;
  llvm::SmallPtrSet<llvm::BasicBlock *, 32> Reachable;

  Slot slot(llvm::Value *P) const {
    int64_t Offset = 0;
    auto *Base = llvm::GetPointerBaseWithConstantOffset(P, Offset, DL);
    return {Base, Offset};
  }
  std::optional<Slot> callerSlot(Slot Target,
                                 const Invocation &Activation) const {
    auto *A = llvm::dyn_cast<llvm::Argument>(Target.Base);
    if (!A)
      return Target;
    auto Actual = slot(Activation.Call.getArgOperand(A->getArgNo()));
    if (llvm::AddOverflow(Actual.Offset, Target.Offset, Actual.Offset))
      return std::nullopt;
    return Actual;
  }
  bool disjoint(Slot A, Slot B, uint64_t Size) const {
    if (A.Base == B.Base) {
      if (B.Offset >= A.Offset)
        return uint64_t(B.Offset) - uint64_t(A.Offset) >= DL.getPointerSize();
      return uint64_t(A.Offset) - uint64_t(B.Offset) >= Size;
    }
    if (llvm::isa<llvm::PHINode, llvm::SelectInst>(A.Base) ||
        llvm::isa<llvm::PHINode, llvm::SelectInst>(B.Base)) {
      llvm::SmallVector<const llvm::Value *, 4> Left, Right;
      llvm::getUnderlyingObjects(A.Base, Left);
      llvm::getUnderlyingObjects(B.Base, Right);
      auto Storage = [](const llvm::Value *V) {
        return llvm::isa<llvm::AllocaInst, llvm::GlobalVariable>(V);
      };
      return !Left.empty() && !Right.empty() && llvm::all_of(Left, Storage) &&
             llvm::all_of(Right, [&](const llvm::Value *V) {
               return Storage(V) && !llvm::is_contained(Left, V);
             });
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
    if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I)) {
      if (auto *Stack = llvm::dyn_cast<llvm::AllocaInst>(Target.Base);
          Stack && Stack->getAllocatedType()->isIntegerTy() &&
          llvm::all_of(Stack->users(), [&](llvm::User *Use) {
            if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(Use))
              return Load->getPointerOperand() == Stack;
            if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(Use))
              return Store->getPointerOperand() == Stack &&
                     Store->getValueOperand() != Stack;
            return false;
          }))
        return false;
      if (auto *Descriptor = Call->getMetadata(BorrowMetadata);
          Descriptor && callSetting(*Descriptor, ReadOnly))
        return false;
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
        if (Name == "cpn.slot.retire") {
          if (auto *Destroy =
                  llvm::dyn_cast<llvm::ConstantInt>(Call->getArgOperand(1));
              Destroy && Destroy->isZero())
            return false;
          if (auto *Registration =
                  llvm::dyn_cast<llvm::AllocaInst>(Call->getArgOperand(0));
              StableRegistrations && Registration)
            for (auto *Use : Registration->users())
              if (auto *Begin = llvm::dyn_cast<llvm::CallBase>(Use))
                if (auto *Callee = Begin->getCalledFunction();
                    Callee && Callee->getName() == "cpn.slot.begin" &&
                    Begin->getArgOperand(0) == Registration) {
                  auto *Drop = Begin->getArgOperand(3);
                  if (llvm::isa<llvm::ConstantPointerNull>(Drop) ||
                      TrivialDrops.contains(
                          llvm::dyn_cast<llvm::Function>(Drop)))
                    return false;
                }
        }
      }
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
      auto *Callee = knownTarget(*Call, Budget, Activation);
      if (!Callee || !Definitions.contains(Callee)) {
        for (auto I :
             positions(Call->getMetadata(BorrowMetadata), ResultSources))
          if (originatesFrom(Call->getArgOperand(I), Budget, Denied,
                             Activation))
            return true;
        return false;
      }
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
    if (auto *Phi = llvm::dyn_cast<llvm::PHINode>(Base))
      for (unsigned I = 0; I < Phi->getNumIncomingValues(); ++I) {
        if (Phi->getIncomingValue(I) == Phi)
          continue;
        if (!Activation && !Reachable.contains(Phi->getIncomingBlock(I)))
          continue;
        if (originatesFrom(Phi->getIncomingValue(I), Budget, Denied,
                           Activation))
          return true;
      }
    auto *L = llvm::dyn_cast<llvm::LoadInst>(Base);
    if (!L || !L->getType()->isPointerTy() || L->isVolatile())
      return false;
    if (auto Stored =
            reachingStore(slot(L->getPointerOperand()), L->getParent(),
                          L->getIterator(), Budget, Activation))
      return originatesFrom(Stored->first->getValueOperand(), Budget, Denied,
                            Stored->second);
    return false;
  }

  std::optional<std::pair<llvm::StoreInst *, const Invocation *>>
  reachingStore(Slot Target, llvm::BasicBlock *BB,
                llvm::BasicBlock::iterator It, unsigned &Budget,
                const Invocation *Activation) const {
    while (Budget) {
      --Budget;
      if (It == BB->begin()) {
        // An unchanged capture field at callee entry still designates the
        // value stored in the receiver before the call.
        if (Activation && BB == &BB->getParent()->getEntryBlock()) {
          auto *A = llvm::dyn_cast<llvm::Argument>(Target.Base);
          if (!A)
            return std::nullopt;
          auto Actual = callerSlot(Target, *Activation);
          if (!Actual)
            return std::nullopt;
          auto &Call = Activation->Call;
          return reachingStore(*Actual, Call.getParent(), Call.getIterator(),
                               Budget, Activation->Caller);
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
          return std::make_pair(S, Activation);
      }
      if (mayChange(I, Target))
        break;
    }
    return std::nullopt;
  }

  llvm::Function *knownTarget(const llvm::CallBase &Call, unsigned &Budget,
                              const Invocation *Activation) const {
    auto *V = Call.getCalledOperand();
    while (Budget) {
      --Budget;
      V = V->stripPointerCasts();
      if (auto *F = llvm::dyn_cast<llvm::Function>(V))
        return F;
      if (auto *A = llvm::dyn_cast<llvm::Argument>(V); A && Activation) {
        V = Activation->Call.getArgOperand(A->getArgNo());
        Activation = Activation->Caller;
        continue;
      }
      auto *Load = llvm::dyn_cast<llvm::LoadInst>(V);
      if (!Load || Load->isVolatile() || Load->isAtomic())
        return nullptr;
      auto Stored =
          reachingStore(slot(Load->getPointerOperand()), Load->getParent(),
                        Load->getIterator(), Budget, Activation);
      if (!Stored)
        return nullptr;
      V = Stored->first->getValueOperand();
      Activation = Stored->second;
    }
    return nullptr;
  }

  bool pointerAt(llvm::Type *T, uint64_t Offset) const {
    while (Offset < DL.getTypeAllocSize(T)) {
      if (T->isPointerTy())
        return !Offset;
      if (auto *S = llvm::dyn_cast<llvm::StructType>(T)) {
        auto *Layout = DL.getStructLayout(S);
        if (auto U = Payloads.find(S); U != Payloads.end()) {
          const uint64_t Start = Layout->getElementOffset(2);
          return Offset >= Start &&
                 llvm::any_of(U->second, [&](llvm::Type *Alternative) {
                   return pointerAt(Alternative, Offset - Start);
                 });
        }
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
  bool survivesReturn(llvm::Instruction &S, Slot Target,
                      unsigned &Budget) const {
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

  Token callSite(const llvm::CallBase &Call, const Token &Fallback) const {
    auto *Descriptor = Call.getMetadata(BorrowMetadata);
    if (!Descriptor)
      return Fallback;
    return {"", callSetting(*Descriptor, Line),
            callSetting(*Descriptor, Column)};
  }

  bool publishedAtReturn(llvm::StoreInst &S, Slot Dest, unsigned &Budget,
                         const Invocation *Activation) const {
    if (!survivesReturn(S, Dest, Budget))
      return false;
    for (; Activation; Activation = Activation->Caller) {
      auto Actual = callerSlot(Dest, *Activation);
      if (!Actual)
        return false;
      Dest = *Actual;
      if (!survivesReturn(Activation->Call, Dest, Budget))
        return false;
    }
    return true;
  }

  void verifyCallBoundaries(llvm::Function &Current, const Token &At,
                            const Invocation *Activation, unsigned &Budget,
                            llvm::SmallPtrSetImpl<llvm::Function *> &Active,
                            std::set<SourcePosition> &Reported) const {
    if (!Active.insert(&Current).second)
      return;
    auto AutomaticHere = [&](llvm::Value *V) {
      if (auto *Local = llvm::dyn_cast<llvm::AllocaInst>(V))
        return Local->getFunction() == &Root;
      return Automatic.contains(V);
    };
    auto Restricted = [&](llvm::Value *V) { return NoRetention.contains(V); };
    auto HasLifetimeObligation = [&](llvm::Value *V) {
      return AutomaticHere(V) || Restricted(V);
    };
    llvm::SmallVector<llvm::BasicBlock *> Work{&Current.getEntryBlock()};
    llvm::SmallPtrSet<llvm::BasicBlock *, 16> Visited;
    while (Budget && !Work.empty()) {
      auto *Block = Work.pop_back_val();
      if (!Visited.insert(Block).second)
        continue;
      for (auto &I : *Block) {
        if (!Budget)
          break;
        --Budget;
        if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I)) {
          unsigned Trace = 256;
          auto *Target = knownTarget(*Call, Trace, Activation);
          if (Target && Definitions.contains(Target)) {
            if (llvm::any_of(Call->args(), [](const llvm::Use &Arg) {
                  return Arg->getType()->isPointerTy();
                })) {
              Invocation Nested{*Call, Activation};
              verifyCallBoundaries(*Target, At, &Nested, Budget, Active,
                                   Reported);
            }
            continue;
          }
          auto *Descriptor = Call->getMetadata(BorrowMetadata);
          if (!Descriptor || !callSetting(*Descriptor, Disposition))
            continue;
          for (auto Index : positions(Descriptor, Retainable)) {
            Trace = 256;
            if (!originatesFrom(Call->getArgOperand(Index), Trace,
                                HasLifetimeObligation, Activation))
              continue;
            auto Site = callSite(*Call, At);
            if (Reported.emplace(Site.Line, Site.Column).second) {
              constexpr llvm::StringRef Message =
                  "MEM002: opaque callable may retain a borrow beyond its "
                  "admitted lifetime";
              if (callSetting(*Descriptor, Disposition) == Error)
                fail(Site, Message.str());
              llvm::errs() << Input << ":" << Site.Line << ":" << Site.Column
                           << ": ANOMALY: " << Message << "\n";
            }
            break;
          }
          continue;
        }
        // A known callee can retain a borrow through a static cell or a field
        // built directly in the caller's result storage.
        auto *Store = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!Activation || !Store ||
            !Store->getValueOperand()->getType()->isPointerTy())
          continue;
        auto Dest = slot(Store->getPointerOperand());
        std::optional<Slot> Published = Dest;
        for (auto *A = Activation; A && Published; A = A->Caller)
          Published = callerSlot(*Published, *A);
        if (!Published || Published->Offset < 0)
          continue;
        const bool Returning = Published->Base == Result;
        auto Global = Globals.find(Published->Base);
        auto *Type = Returning                 ? ResultType
                     : Global != Globals.end() ? Global->second
                                               : nullptr;
        if (!Type || !pointerAt(Type, Published->Offset))
          continue;
        const auto &Prohibited = Returning ? NoPublication : NoRetention;
        auto RestrictedPublication = [&](llvm::Value *V) {
          return Prohibited.contains(V);
        };
        auto *Stored = Store->getValueOperand();
        unsigned Trace = 256;
        if (!originatesFrom(
                Stored, Trace,
                [&](llvm::Value *V) {
                  return AutomaticHere(V) || RestrictedPublication(V);
                },
                Activation))
          continue;
        Trace = 256;
        if (!publishedAtReturn(*Store, Dest, Trace, Activation))
          continue;
        auto *Outermost = Activation;
        while (Outermost->Caller)
          Outermost = Outermost->Caller;
        auto Site = callSite(Outermost->Call, At);
        Trace = 256;
        if (originatesFrom(Stored, Trace, RestrictedPublication, Activation))
          fail(Site,
               "escaping borrow violates the declared parameter contract");
        fail(Site, "borrow of automatic storage escapes through a call");
      }
      if (auto *Next = successor(Block))
        Work.push_back(Next);
      else
        llvm::append_range(Work, llvm::successors(Block));
    }
    Active.erase(&Current);
  }

  static bool constrain(Conditions &Path, Condition Test) {
    if (!Test.Memory && !Test.Subject.Offset) {
      if (llvm::isa<llvm::ConstantInt, llvm::ConstantPointerNull>(
              Test.Subject.Base))
        return (Test.Subject.Base == Test.Number) == Test.Equal;
      if (llvm::isa<llvm::AllocaInst>(Test.Subject.Base) &&
          llvm::isa<llvm::ConstantPointerNull>(Test.Number))
        return !Test.Equal;
    }
    for (const auto &Known : Path) {
      if (Known.Memory != Test.Memory || !(Known.Subject == Test.Subject) ||
          Known.Number->getType() != Test.Number->getType())
        continue;
      if (Known.Number == Test.Number)
        return Known.Equal == Test.Equal;
      if (Known.Equal && Test.Equal)
        return false;
    }
    Path.push_back(Test);
    return true;
  }

  const llvm::ConstantInt *knownOutput(llvm::CallBase &Call,
                                       const Condition &Test) const {
    auto *Callee = Call.getCalledFunction();
    if (!Callee || !Definitions.contains(Callee) || Call.arg_empty() ||
        !Call.getArgOperand(0)->getType()->isPointerTy())
      return nullptr;
    const auto Output = slot(Call.getArgOperand(0));
    int64_t Offset;
    if (Output.Base != Test.Subject.Base ||
        llvm::SubOverflow(Test.Subject.Offset, Output.Offset, Offset) ||
        Offset < 0)
      return nullptr;

    // A native result producer can establish a fixed discriminant in its
    // caller's destination. Inspect each reachable normal return without
    // treating unknown writes or a control-flow merge as an exact constant.
    const Slot Destination{Callee->getArg(0), Offset};
    const llvm::ConstantInt *Value = nullptr;
    unsigned Budget = 128;
    llvm::SmallPtrSet<llvm::BasicBlock *, 8> Seen;
    llvm::SmallVector<llvm::BasicBlock *, 8> Work{&Callee->getEntryBlock()};
    while (!Work.empty()) {
      auto *Block = Work.pop_back_val();
      if (!Seen.insert(Block).second)
        continue;
      if (!Budget--)
        return nullptr;
      if (!llvm::isa<llvm::ReturnInst>(Block->getTerminator())) {
        if (auto *Known = successor(Block))
          Work.push_back(Known);
        else
          llvm::append_range(Work, llvm::successors(Block));
        continue;
      }
      const llvm::ConstantInt *Last = nullptr;
      for (auto *Current = Block; Current && !Last;
           Current = Current->getSinglePredecessor()) {
        for (auto &I : llvm::reverse(*Current)) {
          if (!Budget--)
            return nullptr;
          if (auto *S = llvm::dyn_cast<llvm::StoreInst>(&I);
              S && !S->isVolatile() && !S->isAtomic() &&
              slot(S->getPointerOperand()) == Destination &&
              S->getValueOperand()->getType() == Test.Number->getType()) {
            Last = llvm::dyn_cast<llvm::ConstantInt>(S->getValueOperand());
            if (!Last)
              return nullptr;
            break;
          }
          if (mayChange(I, Destination))
            return nullptr;
        }
      }
      if (!Last || (Value && Last != Value))
        return nullptr;
      Value = Last;
    }
    return Value;
  }

  // Discriminants are frequently extracted from an aggregate load. Retain
  // the relevant byte offset until we cross the actual load, so a write
  // between the load and its branch cannot change the observed value.
  bool
  reverseConditions(llvm::Instruction &I, Conditions &Path,
                    const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors,
                    bool &Uncertain) const {
    auto Later = std::move(Path);
    Path.clear();
    for (auto Test : Later) {
      if (Test.Memory) {
        if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(&I);
            Store && slot(Store->getPointerOperand()) == Test.Subject &&
            Store->getValueOperand()->getType() == Test.Number->getType()) {
          Test.Subject = {Store->getValueOperand(), 0};
          Test.Memory = false;
        } else if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
                   Call && Constructors.contains(Call->getCalledFunction())) {
          if (!disjoint(Test.Subject, slot(Call->getArgOperand(0)),
                        DL.getPointerSize())) {
            Uncertain = true;
            continue;
          }
        } else if (mayChange(I, Test.Subject)) {
          auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
          auto *Fixed = Call ? knownOutput(*Call, Test) : nullptr;
          if (!Fixed)
            Uncertain = true;
          else if ((Fixed == Test.Number) != Test.Equal)
            return false;
          continue;
        }
      } else if (Test.Subject.Base == &I) {
        if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(&I);
            Load && !Load->isVolatile() && !Load->isAtomic()) {
          auto Address = slot(Load->getPointerOperand());
          if (llvm::AddOverflow(Address.Offset, Test.Subject.Offset,
                                Address.Offset)) {
            Uncertain = true;
            continue;
          }
          Test.Subject = Address;
          Test.Memory = true;
        } else if (auto *Extract = llvm::dyn_cast<llvm::ExtractValueInst>(&I);
                   Extract && Extract->getNumIndices() == 1 &&
                   Extract->getAggregateOperand()->getType()->isStructTy()) {
          auto *Type = llvm::cast<llvm::StructType>(
              Extract->getAggregateOperand()->getType());
          auto Offset =
              DL.getStructLayout(Type)->getElementOffset(*Extract->idx_begin());
          if (llvm::AddOverflow(Test.Subject.Offset, int64_t(Offset),
                                Test.Subject.Offset)) {
            Uncertain = true;
            continue;
          }
          Test.Subject.Base = Extract->getAggregateOperand();
        } else if (auto *Compare = llvm::dyn_cast<llvm::ICmpInst>(&I);
                   Compare && Compare->isEquality() && !Test.Subject.Offset) {
          auto *Other = Compare->getOperand(1);
          if (!llvm::isa<llvm::ConstantInt, llvm::ConstantPointerNull>(Other)) {
            Uncertain = true;
            continue;
          }
          const bool Expected = Test.Number->isNullValue() != Test.Equal;
          Test = {{Compare->getOperand(0), 0},
                  llvm::cast<llvm::Constant>(Other),
                  Expected ==
                      (Compare->getPredicate() == llvm::CmpInst::ICMP_EQ)};
        } else if (I.getOpcode() == llvm::Instruction::Xor &&
                   I.getType()->isIntegerTy(1) && !Test.Subject.Offset &&
                   llvm::isa<llvm::ConstantInt>(I.getOperand(1))) {
          if (llvm::cast<llvm::ConstantInt>(I.getOperand(1))->isOne())
            Test.Equal = !Test.Equal;
          Test.Subject.Base = I.getOperand(0);
        } else if (!llvm::isa<llvm::PHINode>(I)) {
          Uncertain = true;
          continue;
        }
      }
      if (!constrain(Path, Test))
        return false;
    }
    return true;
  }

  bool enterPredecessor(llvm::BasicBlock *From, llvm::BasicBlock *To,
                        Conditions &Path, bool &Uncertain) const {
    if (auto *Known = successor(From); Known && Known != To)
      return false;
    auto Later = std::move(Path);
    Path.clear();
    for (auto Test : Later) {
      if (auto *Phi = llvm::dyn_cast<llvm::PHINode>(Test.Subject.Base);
          Phi && Phi->getParent() == To) {
        auto *Incoming = Phi->getIncomingValueForBlock(From);
        if (Test.Memory) {
          auto Address = slot(Incoming);
          if (llvm::AddOverflow(Address.Offset, Test.Subject.Offset,
                                Address.Offset)) {
            Uncertain = true;
            continue;
          }
          Test.Subject = Address;
        } else
          Test.Subject.Base = Incoming;
      }
      if (!constrain(Path, Test))
        return false;
    }
    auto *Terminator = From->getTerminator();
    if (auto *Branch = llvm::dyn_cast<llvm::CondBrInst>(Terminator)) {
      if (Branch->getSuccessor(0) == Branch->getSuccessor(1))
        return true;
      auto *Value =
          llvm::ConstantInt::get(llvm::Type::getInt1Ty(From->getContext()),
                                 Branch->getSuccessor(0) == To);
      return constrain(Path, {{Branch->getCondition(), 0}, Value, true});
    }
    if (auto *Switch = llvm::dyn_cast<llvm::SwitchInst>(Terminator)) {
      Slot Subject{Switch->getCondition(), 0};
      if (Switch->getDefaultDest() == To) {
        for (const auto &Case : Switch->cases())
          if (Case.getCaseSuccessor() != To &&
              !constrain(Path, {Subject, Case.getCaseValue(), false}))
            return false;
      } else {
        const llvm::ConstantInt *Number = nullptr;
        for (const auto &Case : Switch->cases())
          if (Case.getCaseSuccessor() == To) {
            if (Number) {
              Uncertain = true;
              return true;
            }
            Number = Case.getCaseValue();
          }
        if (Number)
          return constrain(Path, {Subject, Number, true});
      }
    }
    return true;
  }

  using TestOrigin = llvm::function_ref<bool(
      llvm::Value *, llvm::ArrayRef<const llvm::Value *>)>;
  enum class BorrowQuestion { ExpiredReferent, ExpiredLoad, PublishedOrigin };

  // Follow pointer storage backwards, through the predecessor-specific value
  // of any result address and through exact copies of the stored pointer.
  // Static borrowing must remain an error only when the relevant flow path
  // is known, including the case guard on a tagged Result payload.
  bool checkStoredOrigins(
      llvm::Instruction &Use, Slot Target, llvm::LoadInst *Pending,
      const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors,
      BorrowQuestion Question, TestOrigin Test) const {
    const bool EveryPath = Question != BorrowQuestion::PublishedOrigin;
    enum class Origin { Search, Matched, Unknown };
    struct Position {
      llvm::BasicBlock *Block;
      llvm::BasicBlock::iterator Cursor;
      Slot Target;
      llvm::LoadInst *PendingLoad;
      Origin Result = Origin::Search;
      bool Uncertain = false;
      Conditions Path;
      llvm::SmallVector<const llvm::Value *, 4> Ended;
      llvm::SmallVector<llvm::BasicBlock *, 8> Visited;
    };
    llvm::SmallVector<Position, 4> Work{
        {Use.getParent(), Use.getIterator(), Target, Pending}};
    bool Proved = false;
    unsigned Budget = 2048;
    while (!Work.empty()) {
      auto P = Work.pop_back_val();
      if (llvm::is_contained(P.Visited, P.Block)) {
        if (EveryPath)
          return false;
        continue;
      }
      P.Visited.push_back(P.Block);
      bool Finished = false;
      while (P.Cursor != P.Block->begin()) {
        if (!Budget--)
          return false;
        auto &I = *--P.Cursor;
        if (!reverseConditions(I, P.Path, Constructors, P.Uncertain)) {
          Finished = true;
          break;
        }
        if (P.Result != Origin::Search)
          continue;
        if (EveryPath)
          if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I))
            if (Call->getMetadata(TemporaryEnd))
              P.Ended.push_back(Call->getArgOperand(0));
        if (Question == BorrowQuestion::ExpiredLoad) {
          if (Test(P.Target.Base, P.Ended))
            P.Result = Origin::Matched;
          else if (mayChange(I, P.Target))
            P.Result = Origin::Unknown;
          continue;
        }
        if (P.PendingLoad) {
          if (&I == P.PendingLoad) {
            P.Target = slot(P.PendingLoad->getPointerOperand());
            P.PendingLoad = nullptr;
          }
          continue;
        }
        llvm::Value *Referent = nullptr;
        if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
            Call && Constructors.contains(Call->getCalledFunction()) &&
            slot(Call->getArgOperand(0)) == P.Target) {
          Referent = Call->getArgOperand(1);
        } else if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(&I);
                   Store && !Store->isVolatile() && !Store->isAtomic() &&
                   Store->getValueOperand()->getType()->isPointerTy() &&
                   slot(Store->getPointerOperand()) == P.Target) {
          if (auto *Load =
                  llvm::dyn_cast<llvm::LoadInst>(Store->getValueOperand());
              Load && !Load->isVolatile() && !Load->isAtomic()) {
            P.PendingLoad = Load;
            continue;
          }
          Referent = Store->getValueOperand();
        }
        if (Referent) {
          P.Result =
              Test(Referent, P.Ended) ? Origin::Matched : Origin::Unknown;
        } else if (mayChange(I, P.Target))
          P.Result = Origin::Unknown;
      }
      if (Finished)
        continue;
      if (llvm::pred_empty(P.Block)) {
        if (EveryPath && P.Result != Origin::Matched)
          return false;
        if (P.Result == Origin::Matched) {
          if (!EveryPath && !P.Uncertain)
            return true;
          Proved |= EveryPath && !P.Uncertain;
        }
        continue;
      }
      for (auto *Pred : llvm::predecessors(P.Block)) {
        auto Previous = P;
        if (!Reachable.contains(Pred) ||
            !enterPredecessor(Pred, P.Block, Previous.Path, Previous.Uncertain))
          continue;
        if (!P.PendingLoad && P.Result == Origin::Search)
          if (auto *Phi = llvm::dyn_cast<llvm::PHINode>(P.Target.Base);
              Phi && Phi->getParent() == P.Block) {
            auto Address = slot(Phi->getIncomingValueForBlock(Pred));
            if (llvm::AddOverflow(Address.Offset, P.Target.Offset,
                                  Address.Offset))
              return false;
            Previous.Target = Address;
          }
        Previous.Block = Pred;
        Previous.Cursor = Pred->end();
        Work.push_back(std::move(Previous));
      }
    }
    return Proved;
  }

  static bool expired(llvm::Value *Referent,
                      llvm::ArrayRef<const llvm::Value *> Ended) {
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(Referent, Objects);
    return !Objects.empty() && llvm::all_of(Objects, [&](auto *Object) {
      return llvm::is_contained(Ended, Object);
    });
  }

  void verifyTemporaryGet(
      llvm::CallBase &Getter, const Token &At,
      const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors) const {
    if (checkStoredOrigins(Getter, slot(Getter.getArgOperand(0)), nullptr,
                           Constructors, BorrowQuestion::ExpiredReferent,
                           expired))
      fail(callSite(Getter, At),
           "Ref designates an ended full-expression temporary");
  }

  void verifyTemporaryLoad(
      llvm::LoadInst &Load, const Token &At,
      const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors) const {
    auto *Address = Load.getPointerOperand();
    llvm::SmallVector<const llvm::Value *, 4> Objects;
    llvm::getUnderlyingObjects(Address, Objects);
    if (Objects.empty() || llvm::any_of(Objects, [](const auto *Object) {
          return !llvm::isa<llvm::AllocaInst>(Object) ||
                 llvm::none_of(Object->users(), [](const auto *User) {
                   auto *I = llvm::dyn_cast<llvm::Instruction>(User);
                   return I && I->getMetadata(TemporaryEnd);
                 });
        }))
      return;
    if (checkStoredOrigins(Load, slot(Address), nullptr, Constructors,
                           BorrowQuestion::ExpiredLoad, expired))
      fail(At, "load designates an ended full-expression temporary");
  }

  bool publishesStoredBorrow(
      llvm::Instruction &Use, llvm::Value *Value, Prohibited Denied,
      const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors) const {
    auto *Load =
        llvm::dyn_cast<llvm::LoadInst>(llvm::getUnderlyingObject(Value));
    if (!Load || Load->isVolatile() || Load->isAtomic() ||
        !Load->getType()->isPointerTy())
      return false;
    auto Exact = [&](llvm::Value *Referent,
                     llvm::ArrayRef<const llvm::Value *>) {
      return Denied(llvm::getUnderlyingObject(Referent));
    };
    return checkStoredOrigins(Use, slot(Load->getPointerOperand()), Load,
                              Constructors, BorrowQuestion::PublishedOrigin,
                              Exact);
  }

public:
  EscapeCheck(Context &U, Function &D, llvm::Function &F,
              const std::map<llvm::Value *, llvm::Type *> &Globals,
              const UnionPayloads &Payloads,
              const llvm::SmallPtrSetImpl<llvm::Function *> &Definitions,
              const llvm::SmallPtrSetImpl<llvm::Function *> &TrivialDrops,
              bool StableRegistrations)
      : DL(U.M.getDataLayout()), Root(F),
        Input(D.Definition.Configuration.Input), Result(nullptr),
        ResultType(nullptr), Globals(Globals), Payloads(Payloads),
        Definitions(Definitions), TrivialDrops(TrivialDrops),
        StableRegistrations(StableRegistrations) {
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
  void
  verify(const Token &At,
         const llvm::SmallPtrSetImpl<llvm::Function *> &RefGetters,
         const llvm::SmallPtrSetImpl<llvm::Function *> &RefConstructors) const {
    auto IsAutomatic = [&](llvm::Value *V) {
      return llvm::isa<llvm::AllocaInst>(V) || Automatic.contains(V);
    };
    auto Check = [&](llvm::Instruction &Use, llvm::Value *V, bool Returning,
                     bool Direct) {
      unsigned Budget = 256;
      if (originatesFrom(V, Budget, IsAutomatic) ||
          publishesStoredBorrow(Use, V, IsAutomatic, RefConstructors))
        fail(At, Direct ? "borrow of automatic storage escapes the function"
                        : "borrow of automatic storage escapes through the "
                          "result or static object");
      const auto &Restricted = Returning ? NoPublication : NoRetention;
      if (Restricted.empty())
        return;
      Budget = 256;
      auto IsRestricted = [&](llvm::Value *Source) {
        return Restricted.contains(Source);
      };
      if (originatesFrom(V, Budget, IsRestricted) ||
          publishesStoredBorrow(Use, V, IsRestricted, RefConstructors))
        fail(At, "escaping borrow violates the declared parameter contract");
    };
    for (auto *BB : Reachable)
      for (auto &I : *BB) {
        if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
            Call && RefGetters.contains(Call->getCalledFunction()))
          verifyTemporaryGet(*Call, At, RefConstructors);
        if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(&I))
          verifyTemporaryLoad(*Load, At, RefConstructors);
        if (auto *R = llvm::dyn_cast<llvm::ReturnInst>(&I))
          if (auto *V = R->getReturnValue(); V && V->getType()->isPointerTy())
            Check(*R, V, true, true);
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
          Check(*S, S->getValueOperand(), Dest.Base == Result, false);
      }
    unsigned Budget = 4096;
    llvm::SmallPtrSet<llvm::Function *, 16> Active;
    std::set<SourcePosition> Reported;
    verifyCallBoundaries(Root, At, nullptr, Budget, Active, Reported);
  }
};
} // namespace

void cpn::describeBorrowCall(
    llvm::CallBase &Call, const Token &At, const Options &Policy,
    llvm::ArrayRef<std::string> Params, unsigned Headers,
    const std::set<unsigned> &NoEscape, const std::set<unsigned> &Returned,
    const EffectBound &Effects, bool MayWriteCallStorage) {
  auto &C = Call.getContext();
  auto Number = [&](unsigned Value) {
    return llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(llvm::Type::getInt32Ty(C), Value));
  };
  llvm::SmallVector<llvm::Metadata *> Inputs, Outputs;
  for (unsigned I = 0; I < Params.size(); ++I)
    if (carriesBorrow(Params[I]) && !NoEscape.count(I))
      Inputs.push_back(Number(Headers + I));
  for (unsigned I : Returned)
    Outputs.push_back(Number(Headers + I));
  bool ReadOnlyCall =
      !MayWriteCallStorage && Effects &&
      llvm::all_of(*Effects, [](llvm::StringRef Item) {
        return Item.starts_with("read:") || Item.starts_with("trap:");
      });
  if (Inputs.empty() && Outputs.empty() && !ReadOnlyCall)
    return;
  Mode Checking = Suppressed;
  if (Policy.Promote.count("MEM002") || Policy.Promote.count("ANOMALY"))
    Checking = Error;
  else if (Policy.Minimum <= Severity::Anomaly &&
           !Policy.Suppress.count("MEM002"))
    Checking = Anomaly;
  Call.setMetadata(BorrowMetadata,
                   llvm::MDNode::get(C, {Number(At.Line), Number(At.Column),
                                         Number(Checking), Number(ReadOnlyCall),
                                         llvm::MDNode::get(C, Inputs),
                                         llvm::MDNode::get(C, Outputs)}));
}

void Context::checkBorrowEscapes() {
  std::map<llvm::Value *, llvm::Type *> StaticObjects;
  for (const auto &[Name, V] : Globals)
    if (auto *G = llvm::dyn_cast_or_null<llvm::GlobalVariable>(V.Address))
      StaticObjects[G] = G->getValueType();
  UnionPayloads Payloads;
  for (const auto &[Name, Alternatives] : Variants) {
    auto &Types = Payloads[Records.at(Name).IR];
    for (const auto &Case : Alternatives)
      Types.push_back(Cases.at(Case).Payload);
  }
  llvm::SmallPtrSet<llvm::Function *, 32> Definitions;
  llvm::SmallPtrSet<llvm::Function *, 8> RefGetters, RefConstructors;
  for (auto &D : Functions)
    for (auto *F : {D.IR, D.BaseIR})
      if (F && !F->empty()) {
        Definitions.insert(F);
        if (!llvm::StringRef(D.Owner).starts_with("std::Ref<"))
          continue;
        const auto &Owner = Records.at(D.Owner);
        if (Owner.Decl.At.Line != 0)
          continue;
        if (D.Decl.Text == "get" && D.Params.empty())
          RefGetters.insert(F);
        if (D.Decl.K == Node::Constructor && D.Params.size() == 1 &&
            D.Params.front() == element(Owner.Fields.front().Type) + "&")
          RefConstructors.insert(F);
      }
  for (const auto &[Name, R] : Records)
    if (R.ClosureEntry && !R.ClosureEntry->empty())
      Definitions.insert(R.ClosureEntry);
  // When no extent can be replaced, implicit cleanup of scalar captures or
  // scalar union payloads only updates the compiler's lifetime sidecars.
  llvm::SmallPtrSet<llvm::Function *, 8> TrivialDrops;
  auto *ExtentCheck = M.getFunction("cpn.extent.valid");
  bool StableRegistrations = !ExtentCheck || ExtentCheck->use_empty();
  if (StableRegistrations) {
    auto ScalarOnly = [&](const std::vector<std::string> &Types) {
      return llvm::none_of(Types, [&](const auto &T) { return aggregate(T); });
    };
    for (const auto &[Type, Drop] : CleanupEntries) {
      auto R = Records.find(Type);
      if (R == Records.end())
        continue;
      if (R->second.Decl.K == Node::Lambda &&
          llvm::none_of(R->second.Fields,
                        [&](const Field &F) { return aggregate(F.Type); }))
        TrivialDrops.insert(Drop);
      auto Alternatives = Variants.find(Type);
      if (Alternatives != Variants.end() &&
          !Overloads.count(Type + "::$drop") &&
          llvm::all_of(Alternatives->second, [&](const auto &Alternative) {
            return ScalarOnly(Cases.at(Alternative).Types);
          }))
        TrivialDrops.insert(Drop);
    }
  }
  for (auto &D : Functions)
    for (auto *F : {D.IR, D.BaseIR})
      if (Definitions.contains(F))
        EscapeCheck(*this, D, *F, StaticObjects, Payloads, Definitions,
                    TrivialDrops, StableRegistrations)
            .verify(D.Decl.At, RefGetters, RefConstructors);
  for (auto &F : M)
    for (auto &I : llvm::make_early_inc_range(llvm::instructions(F))) {
      if (I.getMetadata(TemporaryEnd))
        I.eraseFromParent();
      else
        I.setMetadata(BorrowMetadata, nullptr);
    }
  for (auto &F : llvm::make_early_inc_range(M))
    if (F.getIntrinsicID() == llvm::Intrinsic::lifetime_end && F.use_empty())
      F.eraseFromParent();
}
