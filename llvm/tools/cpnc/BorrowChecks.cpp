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
};
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

  void verifyTemporaryGet(
      llvm::CallBase &Getter, const Token &At,
      const llvm::SmallPtrSetImpl<llvm::Function *> &Constructors) const {
    const auto Target = slot(Getter.getArgOperand(0));
    auto *Block = Getter.getParent();
    auto Current = Getter.getIterator();
    llvm::SmallPtrSet<llvm::Value *, 4> Expired;
    for (unsigned Budget = 256; Block && Budget; --Budget) {
      if (Current == Block->begin()) {
        Block = Block->getSinglePredecessor();
        if (Block)
          Current = Block->end();
        continue;
      }
      auto &I = *--Current;
      if (auto *C = llvm::dyn_cast<llvm::CallBase>(&I)) {
        if (C->getMetadata(TemporaryEnd))
          Expired.insert(C->getArgOperand(0));
        if (Constructors.contains(C->getCalledFunction())) {
          const auto Output = slot(C->getArgOperand(0));
          if (Output.Base == Target.Base && Output.Offset == Target.Offset) {
            const auto Referent = slot(C->getArgOperand(1));
            if (Expired.contains(Referent.Base))
              fail(callSite(Getter, At),
                   "Ref designates an ended full-expression temporary");
            return;
          }
        }
      }
      if (mayChange(I, Target))
        return;
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
        if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
            Call && RefGetters.contains(Call->getCalledFunction()))
          verifyTemporaryGet(*Call, At, RefConstructors);
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
