#include "Sema.h"
using namespace cpn;
std::string Frame::directField(const Node &N) const {
  if (N.K == Node::Name) {
    for (auto &Scope : Scopes)
      if (Scope.Names.count(N.Text))
        return "";
    return FieldFlags.count(N.Text) || ConstantMembersAlive.count(N.Text)
               ? N.Text
               : "";
  }
  if (N.K == Node::Member && N.Definition && N.Children[0].K == Node::Name &&
      N.Children[0].Text == "this" &&
      (FieldFlags.count(N.Text) || ConstantMembersAlive.count(N.Text)))
    return N.Text;
  return "";
}
void Frame::endField(const std::string &Slot, const Token &At,
                     bool RunDestructor, bool Explicit) {
  auto It = FieldFlags.find(Slot);
  if (It == FieldFlags.end())
    fail(At, "request must select a direct subobject");
  auto *Alive = B.CreateLoad(B.getInt1Ty(), It->second);
  if (Explicit)
    guard(B.CreateNot(Alive));
  auto *Do = block("retire.slot"), *Done = block("retire.next");
  B.CreateCondBr(Alive, Do, Done);
  B.SetInsertPoint(Do);
  B.CreateStore(B.getFalse(), It->second);
  Token Name = At;
  Name.Text = Slot;
  if (!RunDestructor && Explicit)
    checkAbandon(member(Self, Name).Type, At);
  if (RunDestructor)
    dropChild(Self, member(Self, Name),
              llvm::StringRef(Slot).starts_with("$base:") ||
                  llvm::StringRef(Slot).starts_with("$virtual:"));
  branch(Done);
  B.SetInsertPoint(Done);
}
void Frame::checkAbandon(const std::string &Type, const Token &At) {
  auto Nontrivial = [&](auto &&Visit, const std::string &T) -> bool {
    if (llvm::StringRef(T).ends_with("]"))
      return !llvm::StringRef(T).ends_with("[0]") && Visit(Visit, element(T));
    if (!U.Records.count(T))
      return false;
    if (U.Overloads.count(T + "::$drop"))
      return true;
    if (auto It = U.Variants.find(T); It != U.Variants.end())
      for (const auto &Case : It->second)
        for (const auto &Field : U.Cases.at(Case).Types)
          if (Visit(Visit, Field))
            return true;
    return llvm::any_of(U.Records.at(T).Fields,
                        [&](const Field &F) { return Visit(Visit, F.Type); });
  };
  if (!Nontrivial(Nontrivial, Type))
    return;
  Opt.diagnose(At, Severity::Anomaly, "LIFE004",
               "abandon bypasses nontrivial cleanup of " + Type);
}
void Frame::endConstantScope() {
  auto Names = std::move(Scopes.back().ConstantDrops);
  Scopes.back().ConstantDrops.clear();
  for (const auto &Name : llvm::reverse(Names)) {
    auto V = Scopes.back().Names.at(Name);
    constantDrop(V, F ? F->Decl.At : Token{});
  }
}

void Frame::endConstantField(const std::string &Slot, bool Run,
                             const Token &At) {
  auto &Alive = ConstantMembersAlive.at(Slot);
  if (!Alive)
    fail(At, "subobject destruction obligation already consumed");
  Token Field = At;
  Field.Text = Slot;
  auto V = member(*ConstantReceiver, Field);
  Alive = false;
  if (Run)
    constantDrop(V, At);
  else
    checkAbandon(V.Type, At);
}

void Frame::constantDrop(Value Object, const Token &At) {
  auto Type = unconst(Object.Type);
  if (!U.aggregate(Type))
    return;
  ConstantActivation Activation(U, At);
  Object = load(Object);
  Object.Type = Type;
  Object.Location.reset();
  Object.ConstantTemporary.reset();
  Object.Address = nullptr;
  auto *C = llvm::dyn_cast_or_null<llvm::Constant>(Object.IR);
  if (!C)
    fail(At, "constant object required for destruction");
  if (auto *Array = llvm::dyn_cast<llvm::ArrayType>(C->getType())) {
    auto E = element(Type);
    if (U.aggregate(unconst(E)) && !llvm::StringRef(Type).ends_with("[0]"))
      for (size_t I = Array->getNumElements(); I; --I)
        constantDrop({E, C->getAggregateElement(unsigned(I - 1))}, At);
    return;
  }
  auto &R = U.Records.at(Type);
  auto D = U.Overloads.find(Type + "::$drop");
  Function *Destructor = D == U.Overloads.end() ? nullptr : D->second.front();
  Frame Body(U, Destructor, nullptr, Type + "::");
  Object.Readonly = false;
  Body.ConstantReceiver = &Object;
  std::set<std::string> Manual;
  for (size_t I = 0; I < R.Fields.size(); ++I) {
    auto &Name = R.Fields[I].Decl.Text;
    Body.ConstantMembersAlive[Name] = true;
    if (R.Decl.Settings.count("manual") && I >= R.Bases.size())
      Manual.insert(Name);
  }
  for (const auto &Decl : R.Decl.Children)
    if (Decl.K == Node::Init && Decl.Type == "Complete") {
      if (Decl.Text == "*")
        for (const auto &Field : R.Fields)
          Manual.insert(Field.Decl.Text);
      else
        Manual.insert(Decl.Text);
    }
  if (Destructor) {
    if (Destructor->Decl.Prototype || Destructor->Decl.Children.empty())
      fail(At, "constant destruction requires a destructor definition");
    Body.constructorBody(Destructor->Decl.Children.front());
  }
  if (U.Variants.count(Type)) {
    auto *Image = llvm::cast<llvm::Constant>(Object.IR);
    auto Tag = llvm::cast<llvm::ConstantInt>(Image->getAggregateElement(0u))
                   ->getZExtValue();
    auto &Active = U.Cases.at(U.Variants.at(Type).at(Tag));
    auto *Payload = unpackVariant(Active, Image, At);
    for (unsigned I = Active.Types.size(); I; --I)
      constantDrop({Active.Types[I - 1], Payload->getAggregateElement(I - 1)},
                   At);
  }
  for (auto &Field : llvm::reverse(R.Fields)) {
    const auto &Name = Field.Decl.Text;
    if (!Body.ConstantMembersAlive.at(Name))
      continue;
    if (Manual.count(Name) && Destructor)
      break;
    Body.endConstantField(Name, true, At);
  }
  if (Destructor && Destructor->Decl.Children.size() > 1)
    Body.constructorBody(Destructor->Decl.Children[1]);
  for (auto &Field : llvm::reverse(R.Fields))
    if (Body.ConstantMembersAlive.at(Field.Decl.Text))
      Body.endConstantField(Field.Decl.Text, true, At);
}
void Frame::retirement() {
  auto &R = U.Records.at(Self.Type);
  installTables(Self);
  std::set<std::string> Manual;
  for (unsigned I = 0; I < R.Fields.size(); ++I) {
    auto &Field = R.Fields[I];
    auto *Flag = allocate("bool", Field.Decl.At);
    B.CreateStore(B.getInt1(!BaseLayer || I >= R.VirtualCount), Flag);
    FieldFlags[Field.Decl.Text] = Flag;
    if (R.Decl.Settings.count("manual") && I >= R.Bases.size())
      Manual.insert(Field.Decl.Text);
  }
  for (auto &D : R.Decl.Children)
    if (D.K == Node::Init && D.Type == "Complete") {
      if (D.Text == "*") {
        for (size_t I = R.VirtualCount; I < R.Fields.size(); ++I)
          Manual.insert(R.Fields[I].Decl.Text);
      } else if (FieldFlags.count(D.Text))
        Manual.insert(D.Text);
      else
        fail(D.At, "Complete must select a direct subobject");
    }
  InlineReturn = block("dtor.sweep");
  if (U.Whole) {
    auto *Body = block("dtor.body");
    B.CreateCondBr(B.CreateCall(U.M.getFunction("cpn.view.skip"),
                                {Self.Address, U.typeID(Self.Type)}),
                   InlineReturn, Body);
    B.SetInsertPoint(Body);
  }
  stmt(F->Decl.Children[0]);
  branch(InlineReturn);
  B.SetInsertPoint(InlineReturn);
  Live = true;
  if (R.Decl.K == Node::Union)
    dropPayload(Self);
  auto *Cleanup = block("dtor.cleanup");
  for (auto I = R.Fields.rbegin(); I != R.Fields.rend(); ++I) {
    auto &Slot = I->Decl.Text;
    if (llvm::StringRef(Slot).starts_with("$virtual:"))
      break;
    if (Manual.count(Slot)) {
      auto *Next = block("dtor.pass");
      auto *Alive = B.CreateLoad(B.getInt1Ty(), FieldFlags.at(Slot));
      llvm::Value *Barrier = Alive;
      if (U.Whole && llvm::StringRef(Slot).starts_with("$base:")) {
        auto *Addr =
            fieldAddress(Self, std::distance(R.Fields.begin(), I.base()) - 1);
        Barrier = B.CreateAnd(
            Alive, B.CreateCall(U.M.getFunction("cpn.view.available"),
                                {Addr, U.typeID(I->Type), B.getFalse()}));
      }
      B.CreateCondBr(Barrier, Cleanup, Next);
      B.SetInsertPoint(Next);
    } else
      endField(Slot, I->Decl.At, true, false);
  }
  branch(Cleanup);
  B.SetInsertPoint(Cleanup);
  InlineReturn = block("dtor.remainder");
  if (F->Decl.Children.size() > 1)
    stmt(F->Decl.Children[1]);
  branch(InlineReturn);
  B.SetInsertPoint(InlineReturn);
  InlineReturn = nullptr;
  Live = true;
  for (auto I = R.Fields.rbegin(); I != R.Fields.rend(); ++I)
    endField(I->Decl.Text, I->Decl.At, true, false);
}
