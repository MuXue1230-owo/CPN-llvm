#include "Sema.h"
using namespace cpn;
Value Frame::closure(const Node &N) {
  if (!IR)
    fail(N.At, "constant evaluation of a closure is unavailable");
  std::string Type = "$closure." + std::string(F ? F->Name : Prefix) + "." +
                     std::to_string(N.At.Line) + "." +
                     std::to_string(N.At.Column);
  std::vector<Value> Values;
  for (auto &C : N.TemplateArgs) {
    Value V =
        C.Type == "initializer" ? eval(C.Children[0]) : load(lookup(C.At));
    if (C.Type == "borrow") {
      if (!V.Address)
        fail(C.At, "borrow capture requires an object lvalue");
      V.Type = (V.Readonly ? "const<" + V.Type + ">" : V.Type) + "*";
      V.IR = V.Address;
      V.Address = nullptr;
    } else if (C.Type == "this") {
      if (!F || F->Owner.empty())
        fail(C.At, "this capture requires an enclosing receiver");
    } else {
      if (V.Type == "integer")
        V = convert(V, Opt.DefaultInt, C.At);
      if (V.Type == "real")
        V = floatingConvert(V, Opt.DefaultReal, C.At);
      V = materialize(V, C.At);
    }
    Values.push_back(V);
  }
  if (!U.Records.count(Type)) {
    auto &R = U.Records[Type];
    R.Decl = N;
    R.Complete = true;
    R.IR = llvm::StructType::create(U.C, Type);
    std::vector<llvm::Type *> Fields;
    for (size_t I = 0; I < Values.size(); ++I) {
      R.Fields.push_back({N.TemplateArgs[I], Values[I].Type});
      Fields.push_back(U.ir(Values[I].Type, N.At));
    }
    if (Fields.empty())
      Fields.push_back(B.getInt8Ty());
    R.IR->setBody(Fields);
    Node Op = N;
    Op.K = Node::Function;
    Op.Text = Op.At.Text = "$call";
    Op.Settings["closure"] = "true";
    Op.TemplateArgs.clear();
    auto *D = U.declare(Op, Type + "::$call", Prefix, Env, Type);
    U.emit(*D);
  }
  auto &R = U.Records.at(Type);
  auto *Ptr = allocate(Type, N.At);
  if (Values.empty())
    B.CreateStore(llvm::Constant::getNullValue(R.IR), Ptr);
  for (size_t I = 0; I < Values.size(); ++I)
    B.CreateStore(Values[I].IR, B.CreateStructGEP(R.IR, Ptr, I));
  Value V{Type, B.CreateLoad(R.IR, Ptr), Ptr};
  V.Expiring = V.Prvalue = true;
  Temps.push_back(V);
  return V;
}
void Frame::bindCaptures() {
  auto &R = U.Records.at(F->Owner);
  Local Captures;
  for (size_t I = 0; I < R.Fields.size(); ++I) {
    auto &Field = R.Fields[I];
    auto *Cell = B.CreateStructGEP(R.IR, Self.Address, I);
    auto &Name = Field.Decl.Text;
    auto &Type = Field.Type;
    if (Scopes[0].Names.count(Name) && Name != "this")
      fail(Field.Decl.At, "parameter shadows a capture");
    if (Field.Decl.Type == "borrow") {
      auto E = element(Type);
      bool Const = llvm::StringRef(E).starts_with("const<") && E.back() == '>';
      Captures.Names[Name] = {Const ? E.substr(6, E.size() - 7) : E, nullptr,
                              B.CreateLoad(B.getPtrTy(), Cell), Const};
    } else
      Captures.Names[Name] = {Type, nullptr, Cell, F->Decl.Const};
  }
  Scopes[0].Names.erase("this");
  Scopes.insert(Scopes.begin(), std::move(Captures));
}
Value Frame::callClosure(Value Receiver, const std::vector<Node> &Args,
                         const Token &At) {
  auto It = U.Records.find(Receiver.Type);
  if (It == U.Records.end())
    fail(At, "callable expression required");
  Node Designator(Node::Name, At);
  Designator.At.Text = Designator.Text =
      It->second.Decl.K == Node::Lambda ? "$call" : "operator()";
  auto Owner = methodOwner(Receiver.Type, Designator.At);
  if (Owner.empty())
    fail(At, "callable expression required");
  adjust(Receiver, Owner, At);
  auto Actual = evaluateArguments(Args);
  auto *Op = select(Designator.Text, Designator, Actual.Values, Receiver);
  admitArguments(Actual, Op, At);
  return invoke(*Op, std::move(Actual.Values), At, Receiver, true);
}
