#include "Sema.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IntrinsicsX86.h"

using namespace cpn;
using llvm::StringRef;

namespace {
std::string position(unsigned I) { return "#" + std::to_string(I); }

bool covers(const EffectSet &Bound, StringRef Effect) {
  const auto [Kind, Region] = Effect.split(':');
  return Bound.count(Effect.str()) ||
         (!Region.empty() && Bound.count((Kind + ":any").str()));
}

std::string spelling(StringRef Effect) {
  const auto [Kind, Region] = Effect.split(':');
  if (Region.empty())
    return Kind.str();
  if (Region.starts_with("#"))
    return (Kind + "(parameter " + Region.drop_front() + ")").str();
  return (Kind + "(" + Region + ")").str();
}

constexpr StringRef CallEffects = "cpn.call.effects";
constexpr StringRef OperationEffects = "cpn.effect";
constexpr StringRef BoundaryEffects = "cpn.boundary.effects";
constexpr StringRef BoundaryScope = "cpn.boundary";
constexpr StringRef StorageRetire = "cpn.storage.retire";
constexpr StringRef StorageReplace = "cpn.storage.replace";
constexpr StringRef StorageWrite = "cpn.storage.write";
constexpr StringRef StorageView = "cpn.storage.view";

struct RegisteredReplacement {
  unsigned Argument;
  llvm::Value *Type;
  llvm::Value *Cleanup;
  auto key() const { return std::tie(Argument, Type, Cleanup); }
  bool operator==(const RegisteredReplacement &Other) const {
    return key() == Other.key();
  }
  bool operator<(const RegisteredReplacement &Other) const {
    return key() < Other.key();
  }
};

struct Summary {
  EffectSet Effects, Boundary;
  std::set<RegisteredReplacement> Replacements;
  bool Open = false;
  bool operator==(const Summary &Other) const {
    return Effects == Other.Effects && Boundary == Other.Boundary &&
           Replacements == Other.Replacements && Open == Other.Open;
  }
};

// These providers implement the frontend's own state and address metadata.
bool runtimeBookkeeping(StringRef Name) {
  return Name.starts_with("cpn.slot.") || Name.starts_with("cpn.view.") ||
         Name.starts_with("cpn.pointer.") || Name == "cpn.new.generation" ||
         Name == "cpn.generation" || Name == "cpn.borrow.valid" ||
         Name == "cpn.extent.valid" || Name == "cpn.whole.epoch" ||
         Name == "cpn.whole.request" || Name == "cpn.static.read";
}

void addMetadataEffects(const llvm::MDNode *MD, EffectSet &Effects) {
  if (!MD)
    return;
  for (const auto &Operand : MD->operands())
    Effects.insert(llvm::cast<llvm::MDString>(Operand)->getString().str());
}

class Inference {
  using Regions = std::set<std::string>;
  using Cell = std::pair<llvm::Value *, int64_t>;
  const Context &U;
  std::map<const llvm::Function *, const Function *> Declarations;
  llvm::SmallPtrSet<llvm::Value *, 16> SourceGlobals;
  std::map<llvm::Value *, llvm::Value *> GlobalStorageAddresses;
  std::map<llvm::Function *, Summary> Summaries;
  const llvm::Argument *ProbedResult = nullptr;

  llvm::Function *callee(const llvm::CallBase &Call) const {
    return llvm::dyn_cast<llvm::Function>(
        Call.getCalledOperand()->stripPointerCasts());
  }

  unsigned resultHeader(const Function &F) const {
    return U.aggregate(F.Result);
  }

  bool receiverHeader(const Function &F) const {
    return !F.Owner.empty() && !F.isStatic();
  }

  std::string argumentRegion(const llvm::Argument &A, bool Reachable) const {
    unsigned I = A.getArgNo();
    auto D = Declarations.find(A.getParent());
    if (D == Declarations.end())
      return position(I);
    const auto &Decl = *D->second;
    unsigned ResultHeader = resultHeader(Decl);
    if (I < ResultHeader)
      return "local";
    I -= ResultHeader;
    if (receiverHeader(Decl)) {
      if (I == 0)
        return "this";
      --I;
    }
    if (I >= Decl.Params.size())
      return "local"; // Construction continuation metadata.
    if (U.aggregate(Decl.Params[I]) && !Reachable)
      return "local";
    return position(I);
  }

  struct Body {
    struct Registration {
      llvm::Value *Object = nullptr, *Type = nullptr;
    };
    struct Replacement {
      llvm::CallBase *Site;
      llvm::Value *Slot, *Cleanup;
      Cell Location = {nullptr, 0};
      llvm::Value *Type = nullptr;
    };
    const Inference &Analysis;
    llvm::Function &Function;
    llvm::SmallPtrSet<llvm::BasicBlock *, 32> Reachable;
    std::map<Cell, std::vector<llvm::Value *>> PointerValues;
    std::map<llvm::Value *, llvm::SmallVector<llvm::Instruction *>>
        UntrackedStores;
    std::map<llvm::Value *, Registration> StorageAddresses;
    std::vector<Replacement> Replacements;
    mutable std::unique_ptr<llvm::DominatorTree> Dominance;

    Body(const Inference &Analysis, llvm::Function &F, bool Interprocedural)
        : Analysis(Analysis), Function(F) {
      llvm::SmallVector<llvm::BasicBlock *> Pending{&F.getEntryBlock()};
      while (!Pending.empty()) {
        auto *Block = Pending.pop_back_val();
        if (!Reachable.insert(Block).second)
          continue;
        if (auto *Branch =
                llvm::dyn_cast<llvm::CondBrInst>(Block->getTerminator()))
          if (const auto *Cond =
                  llvm::dyn_cast<llvm::ConstantInt>(Branch->getCondition())) {
            Pending.push_back(Branch->getSuccessor(Cond->isZero()));
            continue;
          }
        llvm::append_range(Pending, llvm::successors(Block));
      }
      llvm::SmallVector<llvm::CallBase *> Calls;
      llvm::SmallVector<llvm::CallBase *> Views;
      for (auto *Block : Reachable)
        for (auto &I : *Block) {
          if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            auto Slot = cell(Store->getPointerOperand());
            if (isPointerCell(Slot.first) &&
                Store->getValueOperand()->getType()->isPointerTy())
              PointerValues[Slot].push_back(Store->getValueOperand());
          } else if (auto *Transfer = llvm::dyn_cast<llvm::MemIntrinsic>(&I)) {
            UntrackedStores[llvm::getUnderlyingObject(Transfer->getDest())]
                .push_back(Transfer);
          } else if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I)) {
            auto *Callee = Analysis.callee(*Call);
            if (auto Event = Call->getOperandBundle(StorageReplace))
              Replacements.push_back(
                  {Call, Event->Inputs[1].get(), Event->Inputs[2].get()});
            if (Call->getOperandBundle(StorageView))
              Views.push_back(Call);
            if (Callee && Callee->getName() == "cpn.slot.begin")
              StorageAddresses.emplace(
                  Call->getArgOperand(0),
                  Registration{Call->getArgOperand(1), Call->getArgOperand(2)});
            if (Interprocedural && Callee && Analysis.Summaries.count(Callee))
              Calls.push_back(Call);
            if (Callee && !Analysis.Declarations.count(Callee) &&
                runtimeBookkeeping(Callee->getName()))
              continue;
            for (auto &Arg : Call->args())
              if (Arg->getType()->isPointerTy())
                UntrackedStores[llvm::getUnderlyingObject(Arg)].push_back(Call);
          }
        }
      for (auto *View : Views) {
        auto Origin = *View->getOperandBundle(StorageView);
        StorageAddresses.try_emplace(
            slotIdentity(View->getArgOperand(0)),
            Registration{Origin.Inputs[0].get(), Origin.Inputs[1].get()});
      }
      for (auto &Event : Replacements) {
        auto Extent = registration(Event.Slot);
        if (Extent.Object) {
          Event.Location = cell(Extent.Object);
          Event.Type = Extent.Type;
        }
      }
      for (auto *Call : Calls)
        for (const auto &Event :
             Analysis.Summaries.at(Analysis.callee(*Call)).Replacements) {
          auto Location =
              cell(slotIdentity(Call->getArgOperand(Event.Argument)));
          Replacements.push_back(
              {Call, nullptr, Event.Cleanup, Location, Event.Type});
        }
    }

    Cell cell(llvm::Value *P) const {
      int64_t Offset = 0;
      auto *Base = llvm::GetPointerBaseWithConstantOffset(
          P, Offset, Analysis.U.M.getDataLayout());
      return {Base, Offset};
    }

    bool isPointerCell(llvm::Value *Base) const {
      if (llvm::isa<llvm::AllocaInst>(Base))
        return true;
      auto *Call = llvm::dyn_cast<llvm::CallBase>(Base);
      auto *Callee = Call ? Analysis.callee(*Call) : nullptr;
      return Callee && Callee->getName() == "cpn.pointer.field" &&
             llvm::isa<llvm::AllocaInst>(
                 llvm::getUnderlyingObject(Call->getArgOperand(0)));
    }

    llvm::Value *slotIdentity(llvm::Value *Slot) const {
      // A copied storage view may reload its registration from a local cell.
      for (unsigned Budget = 16; Budget; --Budget) {
        auto *Load = llvm::dyn_cast<llvm::LoadInst>(Slot);
        if (!Load)
          break;
        auto Location = cell(Load->getPointerOperand());
        auto It = PointerValues.find(Location);
        if (It == PointerValues.end() || It->second.size() != 1 ||
            isUntracked(Location.first, *Load))
          break;
        Slot = It->second.front();
      }
      return Slot;
    }

    llvm::Value *storageAddress(Cell Address) const {
      if (!Analysis.U.SlotType ||
          Address.second != int64_t(Analysis.U.M.getDataLayout()
                                        .getStructLayout(Analysis.U.SlotType)
                                        ->getElementOffset(3)))
        return nullptr;
      auto *Slot = slotIdentity(Address.first);
      auto Extent = registration(Slot);
      if (Extent.Object)
        return Extent.Object;
      auto It = Analysis.GlobalStorageAddresses.find(Slot);
      return It == Analysis.GlobalStorageAddresses.end() ? nullptr : It->second;
    }

    Registration registration(llvm::Value *Slot) const {
      Slot = slotIdentity(Slot);
      if (auto It = StorageAddresses.find(Slot); It != StorageAddresses.end())
        return It->second;
      if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Slot)) {
        auto *Callee = Analysis.callee(*Call);
        if (Callee && Callee->getName() == "cpn.slot.find")
          return {Call->getArgOperand(0), Call->getArgOperand(1)};
        if (Callee && Callee->getName() == "cpn.slot.child")
          return {Call->getArgOperand(1), Call->getArgOperand(2)};
      }
      return {};
    }

    bool sameRegistration(llvm::Value *A, llvm::Value *B) const {
      A = slotIdentity(A);
      B = slotIdentity(B);
      if (A == B)
        return true;
      // A member sweep looks up its original registration.
      auto *Lookup = llvm::dyn_cast<llvm::CallBase>(A);
      auto *Child = llvm::dyn_cast<llvm::CallBase>(B);
      if (!Lookup || !Child)
        return false;
      auto *Find = Analysis.callee(*Lookup);
      auto *Register = Analysis.callee(*Child);
      return Find && Find->getName() == "cpn.slot.find" && Register &&
             Register->getName() == "cpn.slot.child" &&
             llvm::isa<llvm::ConstantInt>(Lookup->getArgOperand(3)) &&
             llvm::cast<llvm::ConstantInt>(Lookup->getArgOperand(3))->isOne() &&
             Lookup->getArgOperand(2) == Child->getArgOperand(0) &&
             Lookup->getArgOperand(1) == Child->getArgOperand(2) &&
             cell(Lookup->getArgOperand(0)) == cell(Child->getArgOperand(1));
    }

    std::set<llvm::Function *> cleanupEntries(const llvm::CallBase &Retire,
                                              llvm::Value *Fallback,
                                              bool Reconstructed) const {
      std::set<llvm::Function *> Entries;
      bool Replaced = false;
      if (Reconstructed) {
        auto Extent = registration(Retire.getArgOperand(0));
        auto Location = Extent.Object ? cell(Extent.Object) : Cell{nullptr, 0};
        for (const auto &Event : Replacements) {
          bool Matches =
              Event.Slot ? sameRegistration(Retire.getArgOperand(0), Event.Slot)
                         : Extent.Object && Extent.Type == Event.Type &&
                               Location == Event.Location;
          if (Matches && llvm::isPotentiallyReachable(Event.Site, &Retire)) {
            if (Event.Slot) {
              if (!Dominance)
                Dominance = std::make_unique<llvm::DominatorTree>(Function);
              Replaced |= Dominance->dominates(Event.Site, &Retire);
            }
            if (auto *Entry = llvm::dyn_cast<llvm::Function>(Event.Cleanup))
              Entries.insert(Entry);
          }
        }
      }
      if (!Replaced)
        if (auto *Entry = llvm::dyn_cast<llvm::Function>(Fallback))
          Entries.insert(Entry);
      return Entries;
    }

    bool isUntracked(llvm::Value *Base, const llvm::Instruction &Use) const {
      auto It = UntrackedStores.find(Base);
      return It != UntrackedStores.end() &&
             llvm::any_of(It->second, [&](const llvm::Instruction *Store) {
               return Store != &Use &&
                      llvm::isPotentiallyReachable(Store, &Use);
             });
    }

    void regions(llvm::Value *P, Regions &Out,
                 llvm::SmallPtrSetImpl<llvm::Value *> &Visited,
                 unsigned &Budget, bool ReachThrough = false) const {
      if (!Budget) {
        Out.insert("any");
        return;
      }
      --Budget;
      if (!Visited.insert(P).second)
        return;
      auto *Base = llvm::getUnderlyingObject(P);
      if (Base != P)
        return regions(Base, Out, Visited, Budget, ReachThrough);
      if (auto *A = llvm::dyn_cast<llvm::Argument>(Base)) {
        if (A != Analysis.ProbedResult) {
          Out.insert(Analysis.argumentRegion(*A, ReachThrough));
        } else {
          const auto &Sources =
              Analysis.Declarations.at(A->getParent())->BorrowedResult;
          if (Sources.empty())
            Out.insert("any");
          for (unsigned I : Sources)
            Out.insert(position(I));
        }
      } else if (llvm::isa<llvm::AllocaInst, llvm::ConstantPointerNull,
                           llvm::Function>(Base)) {
        Out.insert("local");
      } else if (auto *Global = llvm::dyn_cast<llvm::GlobalVariable>(Base)) {
        Out.insert(Analysis.SourceGlobals.contains(Global) ? "global"
                                                           : "local");
      } else if (auto *Merge = llvm::dyn_cast<llvm::PHINode>(Base)) {
        for (unsigned I = 0; I < Merge->getNumIncomingValues(); ++I)
          if (Reachable.contains(Merge->getIncomingBlock(I)))
            regions(Merge->getIncomingValue(I), Out, Visited, Budget);
      } else if (auto *Select = llvm::dyn_cast<llvm::SelectInst>(Base)) {
        regions(Select->getTrueValue(), Out, Visited, Budget);
        regions(Select->getFalseValue(), Out, Visited, Budget);
      } else if (auto *Field = llvm::dyn_cast<llvm::ExtractValueInst>(Base)) {
        // A pointer extracted from the compiler's call-transport header
        // designates only the sidecar, never the program's objects.
        auto *Loaded =
            llvm::dyn_cast<llvm::LoadInst>(Field->getAggregateOperand());
        auto *Header = Analysis.U.M.getGlobalVariable("cpn.pointer.call", true);
        if (Loaded && Loaded->getPointerOperand() == Header)
          Out.insert("local");
        else
          Out.insert("any");
      } else if (auto *L = llvm::dyn_cast<llvm::LoadInst>(Base)) {
        auto Address = cell(L->getPointerOperand());
        if (auto *Object = storageAddress(Address)) {
          regions(Object, Out, Visited, Budget);
        } else if (!llvm::isa<llvm::AllocaInst>(Address.first)) {
          regions(L->getPointerOperand(), Out, Visited, Budget, true);
        } else if (auto It = PointerValues.find(Address);
                   It != PointerValues.end() &&
                   !isUntracked(Address.first, *L)) {
          for (auto *V : It->second)
            regions(V, Out, Visited, Budget);
        } else {
          Out.insert("any");
        }
      } else if (auto *Call = llvm::dyn_cast<llvm::CallBase>(Base)) {
        auto *F = Analysis.callee(*Call);
        auto Decl = Analysis.Declarations.find(F);
        if (Decl != Analysis.Declarations.end() &&
            !Decl->second->BorrowedResult.empty()) {
          const auto &D = *Decl->second;
          unsigned Offset =
              Analysis.resultHeader(D) + Analysis.receiverHeader(D);
          for (unsigned I : D.BorrowedResult)
            regions(Call->getArgOperand(Offset + I), Out, Visited, Budget);
        } else {
          Out.insert(F && Decl == Analysis.Declarations.end() &&
                             runtimeBookkeeping(F->getName())
                         ? "local"
                         : "any");
        }
      } else {
        Out.insert("any");
      }
    }

    Regions regions(llvm::Value *P) const {
      Regions Out;
      llvm::SmallPtrSet<llvm::Value *, 16> Visited;
      unsigned Budget = 256;
      regions(P, Out, Visited, Budget);
      if (Out.empty())
        Out.insert("any");
      return Out;
    }

    Regions aggregateRegions(llvm::Value *P, const llvm::CallBase &Call) const {
      auto [Base, Offset] = cell(P);
      if (auto *A = llvm::dyn_cast<llvm::Argument>(Base))
        return {Analysis.argumentRegion(*A, true)};
      auto *Local = llvm::dyn_cast<llvm::AllocaInst>(Base);
      if (!Local)
        return regions(P);
      if (Offset != 0 || isUntracked(Base, Call))
        return {"any"};

      // Resolve the pointers carried by an aggregate passed in its local ABI
      // slot. Also inspect explicit stores into byte-allocated variant
      // payloads.
      Regions Out;
      for (auto It = PointerValues.lower_bound({Base, INT64_MIN});
           It != PointerValues.end() && It->first.first == Base; ++It)
        for (auto *V : It->second) {
          auto Roots = regions(V);
          Out.insert(Roots.begin(), Roots.end());
        }
      llvm::SmallVector<std::pair<llvm::Type *, int64_t>> Pending{
          {Local->getAllocatedType(), 0}};
      const auto &DL = Analysis.U.M.getDataLayout();
      unsigned Budget = 256;
      while (!Pending.empty() && Budget--) {
        auto [T, At] = Pending.pop_back_val();
        if (T->isPointerTy()) {
          if (!PointerValues.count({Base, At}))
            return {"any"};
        } else if (auto *S = llvm::dyn_cast<llvm::StructType>(T)) {
          auto *Layout = DL.getStructLayout(S);
          for (unsigned I = 0; I < S->getNumElements(); ++I)
            Pending.emplace_back(S->getElementType(I),
                                 At + Layout->getElementOffset(I));
        } else if (auto *A = llvm::dyn_cast<llvm::ArrayType>(T)) {
          if (A->getNumElements() > Budget)
            return {"any"};
          auto *Element = A->getElementType();
          auto Stride = DL.getTypeAllocSize(Element).getFixedValue();
          for (uint64_t I = 0; I < A->getNumElements(); ++I)
            Pending.emplace_back(Element, At + I * Stride);
        }
      }
      if (!Pending.empty())
        return {"any"};
      return Out;
    }

    void memory(EffectSet &Out, StringRef Kind, llvm::Value *Address) const {
      for (const auto &Region : regions(Address))
        if (Region != "local")
          Out.insert((Kind + ":" + Region).str());
    }

    // A value observation entirely consumed by a write to that same
    // designation is already covered by its write permission.
    bool computesWrite(llvm::Value *V, llvm::Value *Address, bool &Wrote,
                       llvm::SmallPtrSetImpl<llvm::Value *> &Visited) const {
      if (!Visited.insert(V).second)
        return true;
      if (Visited.size() > 64)
        return false;
      for (auto *Use : V->users()) {
        if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(Use)) {
          if (Store->getValueOperand() != V || Store->isVolatile() ||
              Store->isAtomic() ||
              (Store->getPointerOperand() != Address &&
               cell(Store->getPointerOperand()) != cell(Address)))
            return false;
          Wrote = true;
          continue;
        }
        if (auto *Guard = llvm::dyn_cast<llvm::CondBrInst>(Use)) {
          auto *Failure = Guard->getSuccessor(0);
          if (llvm::isa<llvm::UnreachableInst>(Failure->getTerminator()) &&
              llvm::any_of(*Failure, [](const llvm::Instruction &I) {
                EffectSet Tags;
                addMetadataEffects(I.getMetadata(OperationEffects), Tags);
                return Tags.count("trap:numeric");
              }))
            continue;
        }
        if (!llvm::isa<llvm::BinaryOperator, llvm::CastInst, llvm::CmpInst,
                       llvm::SelectInst, llvm::PHINode>(Use) ||
            !computesWrite(Use, Address, Wrote, Visited))
          return false;
      }
      return true;
    }

    bool computesWrite(llvm::LoadInst &L) const {
      if (L.isVolatile() || L.isAtomic())
        return false;
      llvm::SmallPtrSet<llvm::Value *, 16> Visited;
      bool Wrote = false;
      return computesWrite(&L, L.getPointerOperand(), Wrote, Visited) && Wrote;
    }

    void remap(EffectSet &Out, const EffectSet &Source,
               const llvm::CallBase &Call, unsigned Headers, bool Receiver,
               llvm::ArrayRef<unsigned> ValueAggregates,
               llvm::Value *CleanupObject = nullptr) const {
      for (const auto &Item : Source) {
        const auto [Kind, Region] = StringRef(Item).split(':');
        unsigned Index = 0;
        if (Region == "this" && Receiver) {
          Index = Headers;
        } else if (Region.starts_with("#") &&
                   !Region.drop_front().getAsInteger(10, Index)) {
          Index += Headers + Receiver;
        } else {
          Out.insert(Item);
          continue;
        }
        auto *Actual = CleanupObject && Index == 0 ? CleanupObject
                       : Index < Call.arg_size()   ? Call.getArgOperand(Index)
                                                   : nullptr;
        if (!Actual || !Actual->getType()->isPointerTy())
          Out.insert((Kind + ":any").str());
        else if (Kind == "read" || Kind == "write") {
          if (Region.starts_with("#") &&
              llvm::is_contained(ValueAggregates, Index - Headers - Receiver)) {
            for (const auto &Root : aggregateRegions(Actual, Call))
              if (Root != "local")
                Out.insert((Kind + ":" + Root).str());
          } else
            memory(Out, Kind, Actual);
        } else
          for (auto &Origin : regions(Actual)) {
            StringRef Domain(Origin);
            if (Domain == "local" || Domain == "this")
              Domain = "any";
            Out.insert((Kind + ":" + Domain).str());
          }
      }
    }
  };

  void callEffects(Body &Body, Summary &Out, EffectSet &Effects,
                   llvm::CallBase &Call, bool Interprocedural) const {
    if (auto Write = Call.getOperandBundle(StorageWrite)) {
      Body.memory(Effects, "write", Write->Inputs[0]);
      return;
    }
    if (auto Replacement = Call.getOperandBundle(StorageReplace)) {
      Body.memory(Effects, "write", Replacement->Inputs[0]);
      return;
    }
    if (auto Retirement = Call.getOperandBundle(StorageRetire)) {
      auto Enabled = [&](unsigned Index) {
        return llvm::cast<llvm::ConstantInt>(Retirement->Inputs[Index].get())
            ->isOne();
      };
      auto *Address = Retirement->Inputs[0].get();
      if (Enabled(2))
        Body.memory(Effects, "write", Address);
      Out.Open |= Enabled(4);
      for (auto *Entry :
           Body.cleanupEntries(Call, Retirement->Inputs[1], Enabled(3))) {
        auto It = Summaries.find(Entry);
        if (It == Summaries.end()) {
          Out.Open = true;
          continue;
        }
        Body.remap(Effects, It->second.Effects, Call, 0, false, {}, Address);
        Body.remap(Effects, It->second.Boundary, Call, 0, false, {}, Address);
        Out.Open |= It->second.Open;
      }
      return;
    }
    llvm::Function *F = callee(Call);
    EffectBound Bound;
    EffectSet Predicate;
    unsigned Headers = 0;
    bool Receiver = false;
    llvm::SmallVector<unsigned> ValueAggregates;
    auto *Descriptor = Call.getMetadata(CallEffects);
    if (Descriptor) {
      auto Number = [&](unsigned I) {
        return llvm::mdconst::extract<llvm::ConstantInt>(
                   Descriptor->getOperand(I))
            ->getZExtValue();
      };
      Headers = Number(0);
      Receiver = Number(1);
      if (Number(2)) {
        Bound.emplace();
        for (unsigned I = 6; I < Descriptor->getNumOperands(); ++I)
          Bound->insert(llvm::cast<llvm::MDString>(Descriptor->getOperand(I))
                            ->getString()
                            .str());
      }
      if (auto *V = llvm::dyn_cast_or_null<llvm::ValueAsMetadata>(
              Descriptor->getOperand(3)))
        F = llvm::cast<llvm::Function>(V->getValue());
      for (const auto &I :
           llvm::cast<llvm::MDNode>(Descriptor->getOperand(4))->operands())
        ValueAggregates.push_back(
            llvm::mdconst::extract<llvm::ConstantInt>(I)->getZExtValue());
      addMetadataEffects(llvm::cast<llvm::MDNode>(Descriptor->getOperand(5)),
                         Predicate);
    }

    const Function *D = nullptr;
    if (auto It = Declarations.find(F); It != Declarations.end())
      D = It->second;
    if (!Descriptor && D) {
      Bound = D->Effects;
      Headers = resultHeader(*D);
      Receiver = receiverHeader(*D);
    }
    if (D && ValueAggregates.empty())
      for (unsigned I = 0; I < D->Params.size(); ++I)
        if (U.aggregate(D->Params[I]))
          ValueAggregates.push_back(I);

    if (F && F->isIntrinsic()) {
      if (auto *Transfer = llvm::dyn_cast<llvm::MemTransferInst>(&Call))
        Body.memory(Effects, "read", Transfer->getSource());
      if (auto *Memory = llvm::dyn_cast<llvm::MemIntrinsic>(&Call)) {
        Body.memory(Effects, "write", Memory->getDest());
        if (Memory->isVolatile())
          Effects.insert("volatile");
      }
      if ((F->getIntrinsicID() == llvm::Intrinsic::x86_sse_stmxcsr ||
           F->getIntrinsicID() == llvm::Intrinsic::x86_sse_ldmxcsr) &&
          !Call.getMetadata(OperationEffects))
        Effects.insert({"fp_control", "fp_status"});
      return;
    }
    if (F && !D && runtimeBookkeeping(F->getName()))
      return;

    auto Inferred = Summaries.find(F);
    if (Bound) {
      Body.remap(Effects, *Bound, Call, Headers, Receiver, ValueAggregates);
    } else if (Inferred != Summaries.end() && !Descriptor &&
               (Interprocedural || !D)) {
      Body.remap(Effects, Inferred->second.Effects, Call, Headers, Receiver,
                 ValueAggregates);
      Out.Open |= Inferred->second.Open;
    } else {
      if (D && D->Decl.Foreign && (!F || F->isDeclaration()))
        Effects.insert("foreign");
      Out.Open = true;
    }
    if (Inferred != Summaries.end())
      Body.remap(Effects, Inferred->second.Boundary, Call, Headers, Receiver,
                 ValueAggregates);
    else if (D && (!D->ImportAdapter || F != D->IR))
      Predicate.insert(D->PredicateEffects.begin(), D->PredicateEffects.end());
    Body.remap(Effects, Predicate, Call, Headers, Receiver, ValueAggregates);
  }

  Summary summarize(llvm::Function &F, const Function *D) const {
    Summary S;
    bool Interprocedural =
        !D || D->Definition.Configuration.InterproceduralEffects;
    Body Plan(*this, F, Interprocedural);
    for (const auto &Event : Plan.Replacements)
      if (Event.Location.second == 0)
        if (auto *A =
                llvm::dyn_cast_or_null<llvm::Argument>(Event.Location.first))
          S.Replacements.insert({A->getArgNo(), Event.Type, Event.Cleanup});
    for (auto *Block : Plan.Reachable)
      for (auto &I : *Block) {
        if (I.getMetadata("cpn.internal"))
          continue;
        auto &Effects = I.getMetadata(BoundaryScope) ? S.Boundary : S.Effects;
        addMetadataEffects(I.getMetadata(OperationEffects), Effects);
        addMetadataEffects(I.getMetadata(BoundaryEffects), S.Boundary);
        if (auto *L = llvm::dyn_cast<llvm::LoadInst>(&I)) {
          if (!Plan.computesWrite(*L))
            Plan.memory(Effects, "read", L->getPointerOperand());
          if (L->isVolatile())
            Effects.insert("volatile");
          if (L->isAtomic())
            Effects.insert("atomic");
        } else if (auto *Store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
          Plan.memory(Effects, "write", Store->getPointerOperand());
          if (Store->isVolatile())
            Effects.insert("volatile");
          if (Store->isAtomic())
            Effects.insert("atomic");
        } else if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I)) {
          callEffects(Plan, S, Effects, *Call, Interprocedural);
        }
      }
    return S;
  }

public:
  explicit Inference(const Context &U, bool CollectBodies = true) : U(U) {
    for (const auto &F : U.Functions)
      for (auto *Entry : {F.IR, F.BaseIR, F.ImportAdapter})
        if (Entry)
          Declarations.emplace(Entry, &F);
    for (const auto &[Name, Object] : U.Globals) {
      if (Object.Address)
        SourceGlobals.insert(llvm::getUnderlyingObject(Object.Address));
      if (Object.ReferenceCell)
        SourceGlobals.insert(Object.ReferenceCell);
    }
    for (const auto &[Name, Object] : U.ExternalObjects)
      if (Object.Address)
        SourceGlobals.insert(llvm::getUnderlyingObject(Object.Address));
    if (auto *Begin = U.M.getFunction("cpn.slot.begin"))
      for (auto *User : Begin->users())
        if (auto *Start = llvm::dyn_cast<llvm::CallBase>(User))
          if (llvm::isa<llvm::GlobalVariable>(Start->getArgOperand(0)))
            GlobalStorageAddresses.emplace(Start->getArgOperand(0),
                                           Start->getArgOperand(1));
    if (CollectBodies)
      for (auto &F : U.M)
        if (!F.isDeclaration() &&
            (Declarations.count(&F) || !runtimeBookkeeping(F.getName())))
          Summaries.emplace(&F, Summary{});
  }

  EffectSet describePredicates(const Function &D, llvm::Function &Probe,
                               const llvm::Argument *Result) {
    Declarations.emplace(&Probe, &D);
    ProbedResult = Result;
    return summarize(Probe, &D).Effects;
  }

  void verify() {
    bool Changed;
    do {
      Changed = false;
      for (auto &[F, S] : Summaries) {
        auto It = Declarations.find(F);
        auto Next =
            summarize(*F, It != Declarations.end() ? It->second : nullptr);
        if (!(Next == S)) {
          S = std::move(Next);
          Changed = true;
        }
      }
    } while (Changed);
    for (const auto &D : U.Functions) {
      const auto &Policy = D.Definition.Configuration;
      if (!D.Effects && !Policy.StrictEffectDiagnostics)
        continue;
      bool Unknown = false;
      for (auto *F : {D.IR, D.BaseIR, D.ImportAdapter}) {
        auto It = Summaries.find(F);
        if (It == Summaries.end())
          continue;
        if (D.Effects)
          for (const auto &Effect : It->second.Effects)
            if (!covers(*D.Effects, Effect))
              fail(D.Decl.At, "effect " + spelling(Effect) +
                                  " exceeds declared effects of '" + D.Name +
                                  "'");
        Unknown |= It->second.Open;
      }
      if (Unknown)
        Policy.diagnose(D.Decl.At, Severity::Anomaly, {},
                        "call effects could not be established for '" + D.Name +
                            "'");
    }
  }
};
} // namespace

EffectSet cpn::bindEffectNames(StringRef Bound, const std::vector<Node> &Params,
                               bool HasReceiver, const Token &At) {
  EffectSet Result;
  if (Bound == "none")
    return Result;
  llvm::SmallVector<StringRef> Items;
  Bound.split(Items, ',');
  for (auto Item : Items) {
    const auto [Kind, Region] = Item.split(':');
    if (Region.empty() || Kind == "trap" || Region == "any" ||
        Region == "global") {
      Result.insert(Item.str());
      continue;
    }
    if (Region == "this") {
      if (!HasReceiver || (Kind != "read" && Kind != "write"))
        fail(At, "invalid receiver effect region");
      Result.insert(Item.str());
      continue;
    }
    auto P =
        llvm::find_if(Params, [&](const Node &N) { return Region == N.Text; });
    if (P == Params.end())
      fail(At, "unknown effect region '" + Region.str() + "'");
    Result.insert((Kind + ":" + position(P - Params.begin())).str());
  }
  for (auto It = Result.begin(); It != Result.end();) {
    const auto [Kind, Region] = StringRef(*It).split(':');
    if (!Region.empty() && Region != "any" &&
        Result.count((Kind + ":any").str()))
      It = Result.erase(It);
    else
      ++It;
  }
  return Result;
}

std::string cpn::effectFlags(const EffectBound &Bound) {
  if (!Bound)
    return {};
  std::string Flags = " effects_closed";
  for (const auto &Item : *Bound)
    Flags += " effect#" + Item;
  return Flags;
}

EffectBound cpn::callableEffects(StringRef Type) {
  EffectBound Result;
  auto Flags = callableFlags(Type);
  if (!Flags.count("effects_closed"))
    return Result;
  Result.emplace();
  for (auto Flag : Flags)
    if (Flag.consume_front("effect#"))
      Result->insert(Flag.str());
  return Result;
}

EffectSet cpn::callablePredicateEffects(StringRef Type) {
  EffectSet Result;
  for (auto Flag : callableFlags(Type))
    if (Flag.consume_front("predicate#"))
      Result.insert(Flag.str());
  return Result;
}

std::string cpn::predicateEffectFlags(const EffectSet &Bound) {
  std::string Flags;
  for (const auto &Item : Bound)
    Flags += " predicate#" + Item;
  return Flags;
}

bool cpn::effectsFit(const EffectBound &Source, const EffectBound &Target) {
  return !Target || (Source && llvm::all_of(*Source, [&](StringRef Item) {
                       return covers(*Target, Item);
                     }));
}

void cpn::describeEffectCall(llvm::CallBase &Call, const EffectBound &Bound,
                             unsigned Headers, bool Receiver,
                             llvm::Function *Contract,
                             llvm::ArrayRef<unsigned> ValueAggregates,
                             const EffectSet &Predicate) {
  auto &C = Call.getContext();
  auto Index = [&](unsigned I) {
    return llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(llvm::Type::getInt32Ty(C), I));
  };
  llvm::SmallVector<llvm::Metadata *> Aggregates;
  for (auto I : ValueAggregates)
    Aggregates.push_back(Index(I));
  llvm::SmallVector<llvm::Metadata *> Predicates;
  for (const auto &Item : Predicate)
    Predicates.push_back(llvm::MDString::get(C, Item));
  llvm::SmallVector<llvm::Metadata *> Fields{
      Index(Headers),
      Index(Receiver),
      Index(Bound.has_value()),
      Contract ? llvm::ValueAsMetadata::get(Contract) : nullptr,
      llvm::MDNode::get(C, Aggregates),
      llvm::MDNode::get(C, Predicates)};
  if (Bound)
    for (const auto &Item : *Bound)
      Fields.push_back(llvm::MDString::get(C, Item));
  Call.setMetadata(CallEffects, llvm::MDNode::get(C, Fields));
}

EffectSet Context::bindPredicateEffects(const Function &D,
                                        llvm::Function &Probe,
                                        const llvm::Argument *Result) {
  return Inference(*this, false).describePredicates(D, Probe, Result);
}

void Context::checkEffects() {
  if (llvm::any_of(Functions, [](const Function &F) {
        return F.Effects || F.Definition.Configuration.StrictEffectDiagnostics;
      }))
    Inference(*this).verify();
  for (auto &F : M)
    for (auto &Block : F)
      for (auto &I : llvm::make_early_inc_range(Block)) {
        I.setMetadata(CallEffects, nullptr);
        auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!Call)
          continue;
        if (Call->getOperandBundle(StorageWrite)) {
          I.eraseFromParent();
          continue;
        }
        auto Descriptor = Call->getOperandBundle(StorageRetire);
        if (!Descriptor)
          Descriptor = Call->getOperandBundle(StorageReplace);
        if (!Descriptor)
          Descriptor = Call->getOperandBundle(StorageView);
        if (Descriptor) {
          auto *Native = llvm::CallBase::removeOperandBundle(
              Call, Descriptor->getTagID(), Call->getIterator());
          if (Descriptor->getTagName() == StorageRetire &&
              llvm::isa<llvm::GlobalVariable>(Call->getArgOperand(0)) &&
              llvm::cast<llvm::ConstantInt>(Descriptor->Inputs[2].get())
                  ->isOne())
            Native->setMetadata("cpn.storage.original.retire",
                                llvm::MDNode::get(M.getContext(), {}));
          Native->takeName(Call);
          Call->replaceAllUsesWith(Native);
          Call->eraseFromParent();
        }
      }
  if (auto *Marker = M.getFunction("llvm.donothing");
      Marker && Marker->use_empty())
    Marker->eraseFromParent();
}
