#include "Sema.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/MathExtras.h"

using namespace cpn;
namespace {
constexpr llvm::StringRef BorrowMetadata = "cpn.borrow.call";
constexpr llvm::StringRef TemporaryEnd = "cpn.borrow.temporary.end";
constexpr llvm::StringRef OriginalStorageUse = "cpn.storage.original.use";
constexpr llvm::StringRef CheckedStorageUse = "cpn.storage.checked.use";
constexpr llvm::StringRef ConstructStorageUse = "cpn.storage.construct.use";
constexpr llvm::StringRef ExtentStorageUse = "cpn.storage.extent.use";
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

  // A local pointer's sidecar has a known registration and cannot be written
  // via an alias when every use of its address is visible here.
  std::pair<llvm::Value *, llvm::Value *>
  savedGeneration(const llvm::CallBase &Use,
                  const llvm::DominatorTree &Dominance) const {
    auto *SlotLoad = llvm::dyn_cast<llvm::LoadInst>(Use.getArgOperand(0));
    auto *StampLoad = llvm::dyn_cast<llvm::LoadInst>(Use.getArgOperand(1));
    if (!SlotLoad || !StampLoad || !SlotLoad->isSimple() ||
        !StampLoad->isSimple())
      return {};
    const auto Locator = slot(SlotLoad->getPointerOperand());
    const auto Stamp = slot(StampLoad->getPointerOperand());
    auto *Field = llvm::dyn_cast<llvm::CallBase>(Locator.Base);
    auto *Callee = Field ? Field->getCalledFunction() : nullptr;
    if (!Callee || Callee->getName() != "cpn.pointer.field" ||
        Locator.Base != Stamp.Base)
      return {};
    auto *Object = llvm::dyn_cast<llvm::AllocaInst>(Field->getArgOperand(0));
    if (!Object || !Object->getAllocatedType()->isPointerTy() ||
        !Object->getMetadata("cpn.object") || Object->getNumUses() > 128)
      return {};
    llvm::Value *Values[] = {nullptr, nullptr};
    bool Written[] = {false, false};
    for (auto *Access : Object->users()) {
      if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(Access);
          Load && Load->isSimple())
        continue;
      if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(Access);
          Store && Store->isSimple() && Store->getPointerOperand() == Object &&
          Store->getValueOperand() != Object)
        continue;
      auto *Call = llvm::dyn_cast<llvm::CallBase>(Access);
      auto *F = Call ? Call->getCalledFunction() : nullptr;
      if (F && F->getName() == "cpn.slot.begin" &&
          Call->getArgOperand(1) == Object) {
        // A storage view can expose the pointer cell indirectly through the
        // registration even when its own address is never passed anywhere.
        auto *Registration =
            llvm::dyn_cast<llvm::AllocaInst>(Call->getArgOperand(0));
        if (!Registration ||
            !llvm::all_of(Registration->users(), [](const auto *User) {
              const auto *Call = llvm::dyn_cast<llvm::CallBase>(User);
              const auto *F = Call ? Call->getCalledFunction() : nullptr;
              if (!F)
                return false;
              const auto Name = F->getName();
              return Name == "cpn.slot.begin" || Name == "cpn.slot.link" ||
                     Name == "cpn.generation" || Name == "cpn.borrow.valid" ||
                     Name == "cpn.slot.retire" || Name == "cpn.slot.release";
            }))
          return {};
        continue;
      }
      if (!F || F->getName() != "cpn.pointer.field" ||
          Call->getArgOperand(0) != Object || Call->getNumUses() > 128)
        return {};
      for (auto *Address : Call->users()) {
        auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(Address);
        if (!GEP || !GEP->hasAllConstantIndices())
          return {};
        auto Location = slot(GEP);
        if (Location.Base != Call || Location.Offset < 0 ||
            uint64_t(Location.Offset) % DL.getPointerSize() ||
            GEP->getNumUses() > 128)
          return {};
        for (auto *User : GEP->users()) {
          if (auto *Load = llvm::dyn_cast<llvm::LoadInst>(User);
              Load && Load->isSimple())
            continue;
          auto *Store = llvm::dyn_cast<llvm::StoreInst>(User);
          if (!Store || !Store->isSimple() ||
              Store->getPointerOperand() != GEP ||
              (!Store->getValueOperand()->getType()->isPointerTy() &&
               !Store->getValueOperand()->getType()->isIntegerTy(64)))
            return {};
          if (Location.Offset != Locator.Offset &&
              Location.Offset != Stamp.Offset)
            continue;
          unsigned I = Location.Offset == Locator.Offset ? 0 : 1;
          auto *Value = Store->getValueOperand();
          if (Values[I] && Values[I] != Value)
            return {};
          Values[I] = Value;
          Written[I] |=
              Dominance.dominates(Store, I == 0 ? SlotLoad : StampLoad);
        }
      }
    }
    if (Written[0] && Written[1])
      return {Values[0], Values[1]};
    return {};
  }

  bool mayReachBeforeRetirement(
      llvm::CallBase *Capture, const llvm::Instruction &Use,
      llvm::ArrayRef<const llvm::CallBase *> Retirements) const {
    auto *Start = Capture ? Capture->getParent() : &Root.getEntryBlock();
    llvm::SmallVector<llvm::BasicBlock *> Work{Start};
    llvm::SmallPtrSet<llvm::BasicBlock *, 32> Visited;
    unsigned Budget = 4096;
    while (!Work.empty()) {
      auto *BB = Work.pop_back_val();
      if (!Visited.insert(BB).second)
        continue;
      auto Cursor = Capture && BB == Start ? std::next(Capture->getIterator())
                                           : BB->begin();
      for (; Cursor != BB->end(); ++Cursor) {
        if (!Budget-- || &*Cursor == &Use)
          return true;
        if (llvm::is_contained(Retirements, &*Cursor))
          break;
      }
      if (Cursor != BB->end())
        continue;
      if (auto *Next = successor(BB))
        Work.push_back(Next);
      else
        llvm::append_range(Work, llvm::successors(BB));
    }
    return false;
  }

  // Keep all containing extents in a registration key, including layers that
  // start at the same physical address.
  using MemberPath = llvm::SmallVector<std::pair<int64_t, llvm::Value *>, 4>;
  using StorageRegistration =
      std::tuple<llvm::Value *, llvm::Value *, MemberPath>;
  using RetirementsByStorage =
      std::map<StorageRegistration,
               llvm::SmallVector<const llvm::CallBase *, 2>>;
  std::optional<StorageRegistration> storageRegistration(llvm::Value *V) const {
    llvm::Value *Object = nullptr;
    MemberPath Path;
    for (unsigned Depth = 0; Depth != 32; ++Depth) {
      if (llvm::isa_and_nonnull<llvm::AllocaInst, llvm::GlobalVariable>(V)) {
        if (Object && llvm::isa<llvm::AllocaInst>(V) !=
                          llvm::isa<llvm::AllocaInst>(Object))
          break;
        std::reverse(Path.begin(), Path.end());
        return StorageRegistration{V, Object, std::move(Path)};
      }
      auto *Child = llvm::dyn_cast_or_null<llvm::CallBase>(V);
      auto *F = Child ? Child->getCalledFunction() : nullptr;
      if (!F || F->getName() != "cpn.slot.child")
        break;
      auto [Base, Offset] = slot(Child->getArgOperand(1));
      auto *Type = Child->getArgOperand(2);
      if (!llvm::isa<llvm::AllocaInst, llvm::GlobalVariable>(Base) ||
          (Object && Base != Object) || !llvm::isa<llvm::GlobalVariable>(Type))
        break;
      Object = Base;
      Path.emplace_back(Offset, Type);
      V = Child->getArgOperand(0);
    }
    return std::nullopt;
  }

  static llvm::SmallVector<const llvm::CallBase *, 4>
  endingOperations(StorageRegistration Key, const RetirementsByStorage &Ended,
                   bool IncludeSelectedExtent) {
    llvm::SmallVector<const llvm::CallBase *, 4> Operations;
    auto *Parent = std::get<0>(Key);
    auto &Path = std::get<2>(Key);
    if (!IncludeSelectedExtent && !Path.empty())
      Path.pop_back();
    while (!Path.empty()) {
      if (auto It = Ended.find(Key); It != Ended.end())
        llvm::append_range(Operations, It->second);
      Path.pop_back();
    }
    if (auto It = Ended.find({Parent, nullptr, {}}); It != Ended.end())
      llvm::append_range(Operations, It->second);
    return Operations;
  }

  static llvm::CallBase *generationRead(llvm::Value *Value, llvm::Value *Slot) {
    auto *Read = llvm::dyn_cast_or_null<llvm::CallBase>(Value);
    auto *F = Read ? Read->getCalledFunction() : nullptr;
    return F && F->getName() == "cpn.generation" &&
                   Read->getArgOperand(0) == Slot
               ? Read
               : nullptr;
  }

  static bool readsBirth(const llvm::CallBase &Read) {
    auto *Original = llvm::dyn_cast<llvm::ConstantInt>(Read.getArgOperand(1));
    return Original && Original->isOne();
  }

  // A successful parent check fixes the epoch in which the compiler selected
  // the child. Follow the check's success edge only through instructions that
  // cannot change that registration.
  std::optional<llvm::CallBase *>
  checkedParentBirth(const llvm::CallBase &Child, llvm::Value *Parent) const {
    auto *BB = Child.getParent();
    auto Cursor = Child.getIterator();
    unsigned Budget = 32;
    while (Budget--) {
      if (Cursor != BB->begin()) {
        if ((--Cursor)->mayWriteToMemory())
          return std::nullopt;
        continue;
      }
      auto *Predecessor = BB->getSinglePredecessor();
      if (!Predecessor)
        return std::nullopt;
      auto *Branch =
          llvm::dyn_cast<llvm::CondBrInst>(Predecessor->getTerminator());
      if (Branch && Branch->getSuccessor(1) == BB &&
          Branch->getSuccessor(0) != BB) {
        auto *Negated =
            llvm::dyn_cast<llvm::BinaryOperator>(Branch->getCondition());
        auto *Invert =
            Negated && Negated->getOpcode() == llvm::Instruction::Xor
                ? llvm::dyn_cast<llvm::ConstantInt>(Negated->getOperand(1))
                : nullptr;
        const auto *Check =
            Invert && Invert->isOne()
                ? llvm::dyn_cast<llvm::CallBase>(Negated->getOperand(0))
                : nullptr;
        auto *F = Check ? Check->getCalledFunction() : nullptr;
        if (F && F->getName() == "cpn.borrow.valid" &&
            Check->getParent() == Predecessor &&
            Check->getArgOperand(0) == Parent &&
            std::none_of(std::next(Check->getIterator()), Branch->getIterator(),
                         [](const auto &I) { return I.mayWriteToMemory(); })) {
          auto *Stamp = Check->getArgOperand(1);
          if (auto *Read = generationRead(Stamp, Parent);
              Read && readsBirth(*Read))
            return Read;
          if (auto *Original = llvm::dyn_cast<llvm::ConstantInt>(Stamp);
              Original && Original->isZero() &&
              llvm::isa<llvm::GlobalVariable>(Parent))
            return nullptr; // The static original is selected at function
                            // entry.
          return std::nullopt;
        }
      }
      BB = Predecessor;
      Cursor = BB->getTerminator()->getIterator();
    }
    return std::nullopt;
  }

  bool initializedWithoutRetirement(llvm::CallBase &Use,
                                    llvm::Value *Registration,
                                    llvm::Value *Object) const {
    struct Position {
      llvm::BasicBlock *Block;
      llvm::BasicBlock::iterator Cursor;
    };
    llvm::SmallVector<Position> Work{{Use.getParent(), Use.getIterator()}};
    llvm::SmallPtrSet<llvm::BasicBlock *, 16> Visited;
    unsigned Budget = 2048;
    bool Initialized = false;
    while (!Work.empty()) {
      auto [BB, Cursor] = Work.pop_back_val();
      bool AtBirth = false;
      while (Cursor != BB->begin()) {
        if (!Budget--)
          return false;
        auto *Call = llvm::dyn_cast<llvm::CallBase>(&*--Cursor);
        if (!Call || Call->onlyReadsMemory())
          continue;
        auto *F = Call->getCalledFunction();
        if (!F)
          return false;
        auto Name = F->getName();
        if (Name == "cpn.slot.begin" &&
            Call->getArgOperand(0) == Registration &&
            Call->getArgOperand(1) == Object) {
          Initialized = AtBirth = true;
          break;
        }
        // These operations may update internal tables. They do not end a
        // generation or invoke a source-level cleanup operation.
        if (Name != "cpn.slot.begin" && Name != "cpn.slot.link" &&
            Name != "cpn.slot.child" && Name != "cpn.slot.find" &&
            Name != "cpn.slot.linked" && Name != "cpn.generation" &&
            Name != "cpn.borrow.valid" && Name != "cpn.extent.valid" &&
            Name != "cpn.pointer.field")
          return false;
      }
      if (AtBirth)
        continue;
      if (BB == &Root.getEntryBlock())
        return false;
      for (auto *Pred : llvm::predecessors(BB))
        if (auto *Next = successor(Pred); Reachable.contains(Pred) &&
                                          (!Next || Next == BB) &&
                                          Visited.insert(Pred).second)
          Work.push_back({Pred, Pred->end()});
    }
    return Initialized;
  }

  void verifyCheckedStorage(const Token &At) const {
    llvm::SmallVector<llvm::CallBase *> Uses;
    RetirementsByStorage Retirements;
    for (auto &BB : Root)
      if (Reachable.contains(&BB))
        for (auto &I : BB) {
          auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!Call)
            continue;
          if (Call->getMetadata(CheckedStorageUse) ||
              Call->getMetadata(ConstructStorageUse) ||
              Call->getMetadata(ExtentStorageUse))
            Uses.push_back(Call);
          if (auto *F = Call->getCalledFunction();
              F && F->getName() == "cpn.slot.retire")
            if (auto Key = storageRegistration(Call->getArgOperand(0)))
              Retirements[*Key].push_back(Call);
        }
    if (Uses.empty())
      return;
    llvm::DominatorTree Dominance(Root);
    for (auto *Use : Uses) {
      auto *Slot = Use->getArgOperand(0);
      auto *Generation = Use->getArgOperand(1);
      const bool Saved = llvm::isa<llvm::LoadInst>(Slot);
      if (Saved)
        std::tie(Slot, Generation) = savedGeneration(*Use, Dominance);
      auto Key = storageRegistration(Slot);
      if (!Key)
        continue;
      auto &[Parent, Object, Path] = *Key;
      auto *Capture = generationRead(Generation, Slot);
      const auto *Construct = Use->getMetadata(ConstructStorageUse);
      if (const auto *Extent =
              Construct ? Construct : Use->getMetadata(ExtentStorageUse)) {
        if (!Path.empty()) {
          Token Source{At.Text, callSetting(*Extent, 0),
                       callSetting(*Extent, 1)};
          if (Capture && readsBirth(*Capture) &&
              Dominance.dominates(Capture, Use)) {
            auto Ancestors = endingOperations(*Key, Retirements, false);
            if (!Ancestors.empty() &&
                !mayReachBeforeRetirement(Capture, *Use, Ancestors))
              fail(Source,
                   "storage view designates an ended containing generation");
          }
          if (Construct && llvm::isa<llvm::AllocaInst>(Parent) &&
              initializedWithoutRetirement(*Use, Parent, Object))
            fail(Source, "storage contains a live generation");
        }
        continue;
      }
      if (!Capture || Retirements.empty())
        continue;
      if (!Saved) {
        if (Path.empty() || !readsBirth(*Capture))
          continue;
        auto *Child = Slot;
        std::optional<llvm::CallBase *> Birth = Capture;
        for (size_t I = Path.size(); I != 0 && Birth; --I) {
          auto &Selection = *llvm::cast<llvm::CallBase>(Child);
          Child = Selection.getArgOperand(0);
          Birth = checkedParentBirth(Selection, Child);
        }
        if (!Birth)
          continue;
        Capture = *Birth;
      }
      if (Capture && !Dominance.dominates(Capture, Use))
        continue;
      auto Ended = endingOperations(*Key, Retirements, true);
      if (Ended.empty())
        continue;
      if (llvm::isa<llvm::AllocaInst>(Parent) &&
          (!Capture || llvm::none_of(Parent->users(), [&](const auto *User) {
            const auto *Begin = llvm::dyn_cast<llvm::CallBase>(User);
            const auto *F = Begin ? Begin->getCalledFunction() : nullptr;
            return F && F->getName() == "cpn.slot.begin" &&
                   Begin->getArgOperand(0) == Parent &&
                   (!Object || Begin->getArgOperand(1) == Object) &&
                   Dominance.dominates(Begin, Capture);
          })))
        continue;
      if (mayReachBeforeRetirement(Capture, *Use, Ended))
        continue;
      const auto &Location = *Use->getMetadata(CheckedStorageUse);
      Token Source{At.Text, callSetting(Location, 0), callSetting(Location, 1)};
      fail(Source, "ended object generation");
    }
  }

  void verifyOriginalStorage(const Token &At) const {
    auto retirement = [](const llvm::Instruction &I) -> llvm::Value * {
      return I.getMetadata("cpn.storage.original.retire")
                 ? llvm::cast<llvm::CallBase>(I).getArgOperand(0)
                 : nullptr;
    };
    llvm::SmallPtrSet<llvm::Value *, 4> Retired;
    std::map<llvm::Value *, llvm::SmallVector<const llvm::CallBase *, 4>> Uses;
    // Use source emission order for the required diagnostic.
    for (auto &BB : Root) {
      if (!Reachable.contains(&BB))
        continue;
      for (const auto &I : BB) {
        if (auto *Slot = retirement(I))
          Retired.insert(Slot);
        if (I.getMetadata(OriginalStorageUse)) {
          const auto &Call = llvm::cast<llvm::CallBase>(I);
          Uses[Call.getArgOperand(0)].push_back(&Call);
        }
      }
    }
    const llvm::CallBase *First = nullptr;
    for (const auto &[Slot, Accesses] : Uses) {
      if (!Retired.contains(Slot))
        continue;
      // The original generation can only expire. Following the paths on
      // which its slot has not retired handles joins with different exits.
      llvm::SmallPtrSet<llvm::BasicBlock *, 32> Visited;
      llvm::SmallPtrSet<const llvm::Instruction *, 8> MayBeLive;
      llvm::SmallVector<llvm::BasicBlock *> Work{&Root.getEntryBlock()};
      while (!Work.empty()) {
        auto *BB = Work.pop_back_val();
        if (!Visited.insert(BB).second)
          continue;
        bool Ended = false;
        for (const auto &I : *BB) {
          if (retirement(I) == Slot) {
            Ended = true;
            break;
          }
          if (I.getMetadata(OriginalStorageUse) &&
              llvm::cast<llvm::CallBase>(I).getArgOperand(0) == Slot)
            MayBeLive.insert(&I);
        }
        if (!Ended) {
          if (auto *Next = successor(BB))
            Work.push_back(Next);
          else
            llvm::append_range(Work, llvm::successors(BB));
        }
      }
      for (const auto *Access : Accesses) {
        if (MayBeLive.contains(Access))
          continue;
        auto Location = [](const llvm::CallBase &C) {
          const auto &D = *C.getMetadata(OriginalStorageUse);
          return std::pair(callSetting(D, 0), callSetting(D, 1));
        };
        if (!First || Location(*Access) < Location(*First))
          First = Access;
      }
    }
    if (First) {
      const auto &Location = *First->getMetadata(OriginalStorageUse);
      Token Source{At.Text, callSetting(Location, 0), callSetting(Location, 1)};
      fail(Source, "ended object generation");
    }
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
    verifyOriginalStorage(At);
    verifyCheckedStorage(At);
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
