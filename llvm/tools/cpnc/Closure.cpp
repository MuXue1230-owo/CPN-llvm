#include "Sema.h"
using namespace cpn;
Value Frame::closure(const Node &N) {
  if (!IR)
    fail(N.At, "constant evaluation of a closure is unavailable");
  std::string Type = "$closure." + std::string(F ? F->Name : Prefix) + "." +
                     std::to_string(N.At.Line) + "." +
                     std::to_string(N.At.Column);
  std::vector<Value> Values;
  std::vector<llvm::AllocaInst *> Slots;
  for (auto &C : N.TemplateArgs) {
    // Capture types determine the closure layout. Redirect this opaque
    // address to its final field as soon as all capture types are known.
    auto *Slot = B.CreateAlloca(B.getInt8Ty());
    Slots.push_back(Slot);
    Value V = C.Type == "initializer" ? eval(C.Children[0], "", Slot)
                                      : load(lookup(C.At));
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
      materialize(V, C.At, Slot);
    }
    if (C.Type == "borrow" || C.Type == "this")
      B.CreateStore(V.IR, Slot);
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
    EnterDefinition Site(U, {Opt, LookupLimit});
    auto *D = U.declare(Op, Type + "::$call", Prefix, Env, Type);
    U.emit(*D);
  }
  auto &R = U.Records.at(Type);
  auto *Ptr =
      ExpressionDestination.Address && (ExpressionDestination.Type == Type ||
                                        ExpressionDestination.Type.empty())
          ? ExpressionDestination.Address
          : allocate(Type, N.At);
  if (Values.empty())
    B.CreateStore(llvm::Constant::getNullValue(R.IR), Ptr);
  for (size_t I = 0; I < Slots.size(); ++I) {
    llvm::IRBuilder<> Field(Slots[I]);
    Slots[I]->replaceAllUsesWith(Field.CreateStructGEP(R.IR, Ptr, I));
    Slots[I]->eraseFromParent();
  }
  Value V{Type, B.CreateLoad(R.IR, Ptr), Ptr};
  V.Expiring = V.Prvalue = true;
  if (Ptr != ExpressionDestination.Address)
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

Value Frame::closurePointer(const Value &Source, const std::string &T,
                            const Token &At) {
  auto &R = U.Records.at(Source.Type);
  if (!R.Fields.empty())
    fail(At, "function pointer requires a captureless closure");
  auto &Op = *U.Overloads.at(Source.Type + "::$call").front();
  auto Contract = T.substr(0, T.size() - 1);
  const auto &Sig = U.Signatures.at(Contract);
  if (Sig.front() != Op.Result ||
      !llvm::equal(llvm::ArrayRef(Sig).drop_front(), Op.Params) ||
      (callableFlag(Contract, " noexcept") && !Op.Decl.Noexcept))
    fail(At, "closure signature is incompatible with function pointer");
  if (!callableFlag(Contract, " whole"))
    U.RestrictedPointers.emplace_back(&Op, At);
  if (!U.compatibleCallable(U.callableType(Op), Contract))
    fail(At, Op.MayWhole && !callableFlag(Contract, " whole")
                 ? "function pointer must preserve lifecycle_effect(whole)"
                 : "incompatible closure borrow contract");
  if (!R.ClosureEntry) {
    // The native entry omits the receiver. Preserve the result slot and
    // parameter objects supplied by the indirect caller.
    auto *Method = Op.IR->getFunctionType();
    unsigned Receiver = U.aggregate(Op.Result) ? 1 : 0;
    std::vector<llvm::Type *> Params(Method->param_begin(),
                                     Method->param_end());
    Params.erase(Params.begin() + Receiver);
    auto *FT = llvm::FunctionType::get(Method->getReturnType(), Params, false);
    R.ClosureEntry = llvm::Function::Create(
        FT, llvm::GlobalValue::InternalLinkage, Op.Name + ".entry", U.M);
    llvm::IRBuilder<> Entry(
        llvm::BasicBlock::Create(U.C, "entry", R.ClosureEntry));
    std::vector<llvm::Value *> Args;
    for (auto &Arg : R.ClosureEntry->args())
      Args.push_back(&Arg);
    Args.insert(Args.begin() + Receiver, Entry.CreateAlloca(R.IR));
    auto *Result = Entry.CreateCall(Op.IR, Args);
    if (FT->getReturnType()->isVoidTy())
      Entry.CreateRetVoid();
    else
      Entry.CreateRet(Result);
  }
  return {T, R.ClosureEntry};
}
