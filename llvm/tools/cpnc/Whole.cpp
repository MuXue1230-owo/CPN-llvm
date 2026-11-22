#include "Sema.h"
using namespace cpn;
using llvm::StringRef;

void Context::checkWholeContracts() {
  bool Changed;
  do {
    Changed = false;
    for (auto &F : Functions)
      if (!F.MayWhole && llvm::any_of(F.Calls, [](const Function *Callee) {
            return Callee->MayWhole;
          })) {
        F.MayWhole = true;
        Changed = true;
      }
  } while (Changed);
  for (const auto &[F, At] : RestrictedPointers)
    if (F->MayWhole)
      fail(At, "function pointer must preserve lifecycle_effect(whole)");
}

bool Frame::usesWhole(const Node &N) {
  if (N.Settings.count("lifecycle_effect") || N.K == Node::DestructionOwner ||
      (N.K == Node::Name &&
       (N.Text == "destroy_base" || N.Text == "abandon_base" ||
        N.Text == "transfer_destruction")))
    return true;
  return llvm::any_of(N.Children, usesWhole) ||
         llvm::any_of(N.Params, usesWhole) ||
         llvm::any_of(N.TemplateArgs, usesWhole);
}

BasePath Frame::selectBase(const Record &Root, const BasePath &Start,
                           const Node &Selector) {
  if (!Selector.TemplateArgs.empty()) {
    auto Path = Start;
    for (const auto &Edge : Selector.TemplateArgs) {
      auto Type = resolve(Edge.Type, Edge.At);
      auto I = Root.Edges.find(Path);
      if (I != Root.Edges.end()) {
        auto Match = llvm::find_if(I->second, [&](const auto &Child) {
          return Root.Views.at(Child) == Type;
        });
        if (Match != I->second.end()) {
          Path = *Match;
          continue;
        }
      }
      fail(Edge.At, "base_path must follow successive direct base edges");
    }
    return Path;
  }
  auto Type = resolve(Selector.Type, Selector.At);
  std::optional<BasePath> Match;
  for (const auto &[Path, T] : Root.Views) {
    if (Path == Start || T != Type || !Root.contains(Start, Path))
      continue;
    if (Match)
      fail(Selector.At, "ambiguous base path");
    Match = Path;
  }
  if (!Match)
    fail(Selector.At, "selector must name a reachable base");
  return *Match;
}
void Context::bindOwners(const std::string &Name, const std::string &Prefix) {
  auto &Root = Records.at(Name);
  Frame Resolver(*this, nullptr, nullptr, Prefix);
  Resolver.Env = Root.Env;
  for (const auto &D : Root.Decl.Children) {
    if (D.K != Node::DestructionOwner)
      continue;
    auto T = Resolver.resolve(D.Type, D.At);
    auto Virtuals = llvm::ArrayRef(Root.Bases).take_front(Root.VirtualCount);
    auto V = llvm::find(Virtuals, T);
    if (V == Virtuals.end())
      fail(D.At, "destruction_owner requires a shared virtual base");
    auto Owner = Resolver.selectBase(Root, {}, D.TemplateArgs.front());
    BasePath Target{unsigned(V - Virtuals.begin())};
    if (Owner == Target || !Root.contains(Owner, Target))
      fail(D.At, "destruction owner must contain the selected virtual base");
    if (!Root.LocalOwners.emplace(T, Owner).second)
      fail(D.At, "competing destruction owner bindings");
  }
  for (const auto &[Start, Type] : Root.Views) {
    for (const auto &[Virtual, Relative] : Records.at(Type).LocalOwners) {
      BasePath Owner = Start;
      const Record *Layer = &Records.at(Type);
      for (unsigned Index : Relative) {
        auto &Base = Layer->Bases[Index];
        if (Index < Layer->VirtualCount)
          Owner = {unsigned(llvm::find(Root.Bases, Base) - Root.Bases.begin())};
        else
          Owner.push_back(Index);
        Layer = &Records.at(Base);
      }
      if (!Root.Owners.emplace(Virtual, Owner).second)
        fail(Root.Decl.At, "competing destruction owner bindings");
    }
  }
}

llvm::Function *Context::baseCleanup(const std::string &Type) {
  auto &Entry = BaseCleanups[Type];
  if (Entry)
    return Entry;
  auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(C),
                                     {llvm::PointerType::getUnqual(C)}, false);
  Entry = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                 "cpn.base.drop." + Type, M);
  Frame Body(*this, nullptr, Entry);
  Body.B.SetInsertPoint(Body.block("entry"));
  Body.dropLayer({Type, nullptr, Entry->getArg(0)}, true);
  Body.B.CreateRetVoid();
  return Entry;
}

llvm::Function *Context::coordinator(const std::string &Type) {
  auto &Entry = Coordinators[Type];
  if (Entry)
    return Entry;
  auto &Root = Records.at(Type);
  auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(C),
                                     {llvm::PointerType::getUnqual(C)}, false);
  Entry = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                 "cpn.complete.drop." + Type, M);
  Frame F(*this, nullptr, Entry);
  auto &B = F.B;
  B.SetInsertPoint(F.block("entry"));
  auto *ContextType = llvm::StructType::getTypeByName(C, "cpn.boundary");
  auto *ViewType = llvm::StructType::getTypeByName(C, "cpn.view");
  auto *Active = M.getGlobalVariable("cpn.boundary.current", true);
  auto *Pending = M.getGlobalVariable("cpn.request.pending", true);
  auto *Prev = B.CreateLoad(B.getPtrTy(), Active);
  auto *Boundary = B.CreateAlloca(ContextType);
  auto *Views = B.CreateAlloca(ViewType, B.getInt32(Root.Views.size()));
  B.CreateStore(Views, Boundary);
  B.CreateStore(B.getInt32(Root.Views.size()),
                B.CreateStructGEP(ContextType, Boundary, 1));
  B.CreateStore(B.getInt64(0), B.CreateStructGEP(ContextType, Boundary, 2));
  Value Object{Type, nullptr, Entry->getArg(0)};
  std::map<BasePath, unsigned> Indices;
  for (const auto &[Path, T] : Root.Views)
    Indices.emplace(Path, Indices.size());
  for (const auto &[Path, T] : Root.Views) {
    auto *Row = B.CreateGEP(ViewType, Views, B.getInt32(Indices.at(Path)));
    auto store = [&](unsigned Field, llvm::Value *V) {
      B.CreateStore(V, B.CreateStructGEP(ViewType, Row, Field));
    };
    store(0, F.baseView(Object, Path).Address);
    store(1, typeID(T));
    store(2, Path.empty() ? static_cast<llvm::Constant *>(
                                llvm::ConstantPointerNull::get(B.getPtrTy()))
                          : baseCleanup(T));
    std::vector<uint8_t> Containing;
    for (const auto &[Layer, LayerType] : Root.Views)
      Containing.push_back(Layer != Path && Root.contains(Layer, Path));
    auto *Mask = llvm::ConstantDataArray::get(C, Containing);
    auto *MaskVar = new llvm::GlobalVariable(M, Mask->getType(), true,
                                             llvm::GlobalValue::PrivateLinkage,
                                             Mask, "cpn.base.ancestors");
    MaskVar->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
    store(3, MaskVar);
    BasePath Owner = Path;
    if (!Owner.empty())
      Owner.pop_back();
    llvm::Value *Binding = B.getInt32(Indices.at(Owner));
    llvm::Value *Eligible = B.getInt1(!Path.empty());
    if (Path.size() == 1 && Path.front() < Root.VirtualCount) {
      auto *State = ownerRecordType();
      auto *Row = F.ownerRecord(Object, Path.front());
      B.CreateStore(B.getTrue(), B.CreateStructGEP(State, Row, 3));
      Binding = B.CreateLoad(B.getInt32Ty(), B.CreateStructGEP(State, Row, 0));
      Eligible = B.getFalse();
      for (const auto &[Candidate, Layer] : Root.Views) {
        if (Candidate == Path || !Root.contains(Candidate, Path))
          continue;
        bool Manual =
            llvm::any_of(Records.at(Layer).Decl.Children, [&](const Node &D) {
              return D.K == Node::Init && D.Type == "Complete" &&
                     D.Text == "$virtual:" + T;
            });
        if (Manual)
          Eligible = B.CreateOr(
              Eligible,
              B.CreateICmpEQ(Binding, B.getInt32(Indices.at(Candidate))));
      }
    }
    store(4, Binding);
    store(5, Eligible);
    store(6, B.getFalse());
    store(7, B.getFalse());
  }
  B.CreateStore(Boundary, Active);
  auto *Request = B.CreateLoad(B.getPtrTy(), Pending);
  auto *Begin = F.block("requested"), *Sweep = F.block("sweep");
  B.CreateCondBr(B.CreateIsNotNull(Request), Begin, Sweep);
  B.SetInsertPoint(Begin);
  B.CreateStore(llvm::ConstantPointerNull::get(B.getPtrTy()), Pending);
  F.guard(
      B.CreateNot(B.CreateCall(M.getFunction("cpn.whole.request"), {Request})));
  F.branch(Sweep);
  B.SetInsertPoint(Sweep);
  F.dropLayer(Object, false);
  B.CreateStore(Prev, Active);
  B.CreateRetVoid();
  return Entry;
}

llvm::Value *Frame::wholeEpoch() {
  return U.Whole && IR ? B.CreateCall(U.M.getFunction("cpn.whole.epoch"))
                       : nullptr;
}
void Frame::exitWhole() {
  endExpression();
  cleanup(0);
  exitInvariantConstructionLifetimes();
  if (InlineReturn)
    branch(InlineReturn);
  else if (IR->getReturnType()->isVoidTy())
    B.CreateRetVoid();
  else
    B.CreateRet(llvm::PoisonValue::get(IR->getReturnType()));
}
void Frame::propagateWhole(llvm::Value *Before) {
  if (!Before)
    return;
  auto *Exit = block("whole.exit"), *Next = block("whole.continue");
  B.CreateCondBr(B.CreateICmpNE(Before, wholeEpoch()), Exit, Next);
  B.SetInsertPoint(Exit);
  {
    llvm::SaveAndRestore TempsScope(Temps);
    llvm::SaveAndRestore ActiveScope(Active);
    exitWhole();
  }
  B.SetInsertPoint(Next);
}

Value Frame::transferOwner(const Node &C, const Node &Operand) {
  auto Target = eval(Operand);
  if (StringRef(Target.Type).ends_with("*")) {
    auto T = element(Target.Type);
    if (StringRef(T).starts_with("const<") && T.back() == '>')
      T = T.substr(6, T.size() - 7);
    guard(B.CreateIsNull(Target.IR));
    Value View{T, nullptr, Target.IR};
    View.borrow(Target);
    Target = View;
  }
  if (!IR || !Target.Address || !U.Records.count(Target.Type))
    fail(C.At, "destruction transfer requires a class layer");
  const auto &Layer = U.Records.at(Target.Type);
  auto Virtuals = llvm::ArrayRef(Layer.Bases).take_front(Layer.VirtualCount);
  auto T = resolve(C.TemplateArgs.front().Type, C.At);
  auto V = llvm::find(Virtuals, T);
  if (V == Virtuals.end())
    fail(C.At, "target must contain the selected virtual base");
  ensureLive(Target, C.At);
  auto *Row = ownerRecord(Target, V - Virtuals.begin());
  auto *State = U.ownerRecordType();
  auto *Entered =
      B.CreateLoad(B.getInt1Ty(), B.CreateStructGEP(Layer.IR, Target.Address,
                                                    Layer.layerEnteredSlot()));
  auto *Alive = B.CreateLoad(B.getInt1Ty(), B.CreateStructGEP(State, Row, 2));
  auto *Frozen = B.CreateLoad(B.getInt1Ty(), B.CreateStructGEP(State, Row, 3));
  guard(B.CreateOr(Frozen, B.CreateNot(B.CreateAnd(Entered, Alive))));
  auto *ID =
      B.CreateLoad(B.getInt32Ty(), B.CreateStructGEP(Layer.IR, Target.Address,
                                                     Layer.layerIndexSlot()));
  B.CreateStore(ID, B.CreateStructGEP(State, Row, 0));
  return {"void"};
}
Value Frame::baseRequest(const Node &C, const Node &Operand) {
  if (F)
    F->MayWhole = true;
  auto Object = eval(Operand);
  if (StringRef(Object.Type).ends_with("*")) {
    auto T = element(Object.Type);
    if (StringRef(T).starts_with("const<") && T.back() == '>')
      T = T.substr(6, T.size() - 7);
    guard(B.CreateIsNull(Object.IR));
    auto View = Value{T, nullptr, Object.IR};
    View.borrow(Object);
    Object = View;
  }
  if (!IR || !Object.Address || !U.Records.count(Object.Type))
    fail(C.At, "base request requires an object or pointer to a class layer");
  const auto &R = U.Records.at(Object.Type);
  auto Path = selectBase(R, {}, C.TemplateArgs.front());
  auto Target = baseView(Object, Path);
  if (C.Text == "abandon_base")
    checkAbandon(Target.Type, C.At);
  auto Parent = Path;
  Parent.pop_back();
  auto Authority = baseView(Object, Parent);
  auto *RequestType = llvm::StructType::getTypeByName(U.C, "cpn.request");
  llvm::IRBuilder<> Alloc(IR->getEntryBlock().begin());
  auto *Request = Alloc.CreateAlloca(RequestType);
  auto store = [&](unsigned I, llvm::Value *V) {
    B.CreateStore(V, B.CreateStructGEP(RequestType, Request, I));
  };
  store(0, Target.Address);
  store(1, U.typeID(Target.Type));
  store(2, Authority.Address);
  store(3, U.typeID(Authority.Type));
  store(4, B.getInt1(C.Text == "destroy_base"));
  auto *Current = block("whole.current"), *External = block("whole.external");
  auto *RequestWhole =
      B.CreateCall(U.M.getFunction("cpn.whole.request"), {Request});
  RequestWhole->setMetadata(
      "cpn.effect", llvm::MDNode::get(U.C, llvm::MDString::get(U.C, "whole")));
  B.CreateCondBr(RequestWhole, Current, External);
  B.SetInsertPoint(Current);
  {
    llvm::SaveAndRestore TempsScope(Temps);
    llvm::SaveAndRestore ActiveScope(Active);
    exitWhole();
  }
  B.SetInsertPoint(External);
  auto *Registered = slotFor(Object);
  auto *Containing = B.CreateCall(U.M.getFunction("cpn.slot.enclosing"),
                                  {Object.Address, Target.Address});
  auto *Slot =
      B.CreateSelect(B.CreateIsNotNull(Registered), Registered, Containing);
  guard(B.CreateIsNull(Slot));
  guard(B.CreateNot(B.CreateTrunc(
      B.CreateCall(U.M.getFunction("cpn.generation"), {Slot, B.getFalse()}),
      B.getInt1Ty())));
  auto *Pending = U.M.getGlobalVariable("cpn.request.pending", true);
  B.CreateStore(Request, Pending);
  B.CreateCall(U.M.getFunction("cpn.slot.retire"), {Slot, B.getTrue()});
  guard(B.CreateIsNotNull(B.CreateLoad(B.getPtrTy(), Pending)));
  if (!Object.Storage.empty() && !Object.Subobject)
    Active[Object.Storage] = 0;
  return {"void"};
}
