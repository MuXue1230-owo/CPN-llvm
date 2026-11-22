#include "Sema.h"

using namespace cpn;
using llvm::StringRef;

namespace {
bool eligible(const Function &F) {
  auto Access = F.Decl.Settings.find("access");
  return F.Decl.K == Node::Function && !F.Owner.empty() && !F.isStatic() &&
         !F.Decl.Settings.count("closure") &&
         (Access == F.Decl.Settings.end() || Access->second == "public") &&
         F.Initializes.empty();
}

bool checked(const Record &R) {
  return R.InvariantSite && R.InvariantSite->Configuration.ContractsEnabled &&
         R.InvariantSite->Configuration.InvariantValidation == "check";
}

bool checkable(const Context &U, const std::string &Type) {
  auto MayFail = [&](const std::string &T) {
    const auto &R = U.Records.at(T);
    return checked(R) && llvm::any_of(R.Decl.Contracts, [](const Node &C) {
             const auto &P = C.Children.front();
             return P.K != Node::Name || P.Text != "true";
           });
  };
  return MayFail(Type) ||
         llvm::any_of(U.Records.at(Type).Views, [&](const auto &View) {
           return !View.first.empty() && MayFail(View.second);
         });
}

// One linked list per thread records the exact layer undergoing a
// construction or destruction transaction. Other receivers, including an
// independently live member of that layer, still pass through their checks.
llvm::GlobalVariable *currentLifetime(llvm::Module &M) {
  if (auto *G = M.getGlobalVariable("cpn.invariant.lifetime", true))
    return G;
  auto *Ptr = llvm::PointerType::getUnqual(M.getContext());
  return new llvm::GlobalVariable(
      M, Ptr, false, llvm::GlobalValue::InternalLinkage,
      llvm::ConstantPointerNull::get(Ptr), "cpn.invariant.lifetime", nullptr,
      llvm::GlobalVariable::GeneralDynamicTLSModel);
}

llvm::StructType *lifetimeEntry(llvm::LLVMContext &C) {
  auto *Ptr = llvm::PointerType::getUnqual(C);
  return llvm::StructType::get(C, {Ptr, Ptr, Ptr});
}

void markInternal(llvm::Instruction *I) {
  I->setMetadata("cpn.internal", llvm::MDNode::get(I->getContext(), {}));
}
} // namespace

void Context::validateInvariants(const std::string &Type) {
  if (!Records.at(Type).InvariantSite)
    return;
  auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(C),
                                     {llvm::PointerType::getUnqual(C)}, false);
  auto *Probe = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                       "cpn.invariant.check", M);
  Frame Check(*this, nullptr, Probe);
  Check.B.SetInsertPoint(Check.block("entry"));
  Check.evaluateInvariants({Type, nullptr, Probe->getArg(0)}, true);
  Probe->eraseFromParent();
}

bool Context::hasCheckedInvariant(const Function &F) const {
  return eligible(F) && checkable(*this, F.Owner);
}

llvm::Value *Frame::pushInvariantLifetime(const Value &Obj, const Node *Tail,
                                          bool IsConstruction) {
  if (!IR || TypeQuery || !checkable(U, Obj.Type))
    return nullptr;
  auto *Current = currentLifetime(U.M);
  auto *Previous = B.CreateLoad(B.getPtrTy(), Current);
  markInternal(Previous);
  auto *Entry = lifetimeEntry(U.C);
  llvm::IRBuilder<> AtEntry(IR->getEntryBlock().begin());
  auto *Node = AtEntry.CreateAlloca(Entry);
  B.CreateStore(Obj.Address, B.CreateStructGEP(Entry, Node, 0));
  B.CreateStore(U.typeID(Obj.Type), B.CreateStructGEP(Entry, Node, 1));
  B.CreateStore(Previous, B.CreateStructGEP(Entry, Node, 2));
  markInternal(B.CreateStore(Node, Current));
  if (IsConstruction) {
    std::optional<SourcePosition> At;
    if (Tail)
      At.emplace(Tail->At.Line, Tail->At.Column);
    InvariantConstructionLifetimes.push_back({Previous, Scopes.size(), At});
  }
  return Previous;
}

void Frame::popInvariantLifetime(llvm::Value *Previous, bool IsConstruction) {
  if (!Previous)
    return;
  if (IsConstruction)
    InvariantConstructionLifetimes.pop_back();
  markInternal(B.CreateStore(Previous, currentLifetime(U.M)));
}

void Frame::exitInvariantConstructionLifetimes(
    size_t Depth, const std::set<SourcePosition> *Exited) {
  auto First =
      llvm::find_if(InvariantConstructionLifetimes, [&](const auto &L) {
        return L.Depth >= Depth &&
               (!Exited || (L.Tail && Exited->count(*L.Tail)));
      });
  if (First == InvariantConstructionLifetimes.end())
    return;
  markInternal(B.CreateStore(First->Previous, currentLifetime(U.M)));
}

void Frame::evaluateInvariants(Value Obj, bool ValidateOnly, bool OwnBoundary) {
  auto &R = U.Records.at(Obj.Type);
  if (!R.InvariantSite || (!ValidateOnly && !checked(R)))
    return;
  Frame Pred(U, nullptr, IR, Obj.Type + "::");
  Pred.TypeQuery = ValidateOnly;
  Pred.Env = R.Env;
  Pred.Opt = R.InvariantSite->Configuration;
  Pred.LookupLimit = R.InvariantSite->Through;
  Obj.Readonly = true;
  if (IR) {
    Pred.B.SetInsertPoint(B.GetInsertBlock());
    Pred.Self = Obj;
    Pred.Scopes.front().Names["this"] = {"const<" + Obj.Type + ">*",
                                         Obj.Address};
  } else
    Pred.ConstantReceiver = &Obj;
  unsigned Ordinal = 0;
  for (const auto &Clause : R.Decl.Contracts)
    Pred.evaluatePredicate(Clause, Obj.Type, ++Ordinal,
                           Pred.Opt.InvariantValidation, ValidateOnly,
                           OwnBoundary);
  if (IR)
    B.SetInsertPoint(Pred.B.GetInsertBlock());
}

void Frame::checkInvariants(Value Obj, bool IncludeBases, bool OwnBoundary) {
  auto I = U.Records.find(Obj.Type);
  if (I == U.Records.end() || TypeQuery)
    return;
  if (IncludeBases)
    for (const auto &[Path, Base] : I->second.Views)
      if (!Path.empty() && checked(U.Records.at(Base))) {
        auto BaseObject = Obj;
        if (!IR && BaseObject.Location) {
          BaseObject = load(BaseObject);
          BaseObject.Location.reset();
          BaseObject.Address = nullptr;
        }
        evaluateInvariants(baseView(BaseObject, Path), false, OwnBoundary);
      }
  evaluateInvariants(Obj, false, OwnBoundary);
}

void Frame::checkMethodInvariant(bool Entry) {
  if (!F || (!Entry && F->Decl.Const) || !U.hasCheckedInvariant(*F))
    return;
  if (!IR) {
    if (!ConstantReceiver)
      return;
    const auto &Place = ConstantReceiver->Location;
    if (llvm::any_of(U.ConstantInvariantLifetimes, [&](const Value *Active) {
          return ConstantReceiver == Active ||
                 (Place && Place->Root == Active && Place->Steps.empty());
        }))
      return;
    checkInvariants(*ConstantReceiver, true, true);
    return;
  }
  auto *Start = B.GetInsertBlock();
  auto *Current = B.CreateLoad(B.getPtrTy(), currentLifetime(U.M));
  markInternal(Current);
  auto *Head = block("invariant.lifetime"), *Inspect = block("invariant.layer"),
       *Check = block("invariant.check"), *Done = block("invariant.done");
  B.CreateBr(Head);
  B.SetInsertPoint(Head);
  auto *Node = B.CreatePHI(B.getPtrTy(), 2);
  Node->addIncoming(Current, Start);
  B.CreateCondBr(B.CreateIsNull(Node), Check, Inspect);
  B.SetInsertPoint(Inspect);
  auto *Layout = lifetimeEntry(U.C);
  auto load = [&](unsigned I) {
    auto *V = B.CreateLoad(B.getPtrTy(), B.CreateStructGEP(Layout, Node, I));
    markInternal(V);
    return V;
  };
  auto *Same = B.CreateAnd(B.CreateICmpEQ(Self.Address, load(0)),
                           B.CreateICmpEQ(U.typeID(Self.Type), load(1)));
  Node->addIncoming(load(2), Inspect);
  B.CreateCondBr(Same, Done, Head);
  B.SetInsertPoint(Check);
  checkInvariants(Self, true, true);
  B.CreateBr(Done);
  B.SetInsertPoint(Done);
}
