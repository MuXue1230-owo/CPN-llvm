#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/ConvertUTF.h"
#include <algorithm>

using namespace cpn;
using llvm::StringRef;
namespace {
bool ends(const std::string &T, StringRef S) {
  return StringRef(T).ends_with(S);
}
std::string baseRef(std::string T) {
  while (ends(T, "&"))
    T.pop_back();
  return T;
}
bool assignment(StringRef Op) {
  return Op == "=" || Op == "+=" || Op == "-=" || Op == "*=" || Op == "/=" ||
         Op == "%=" || Op == "&=" || Op == "|=" || Op == "^=" || Op == "<<=" ||
         Op == ">>=";
}
} // namespace
Value Frame::lookup(const Token &T) {
  for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
    if (I->UnavailableNames.count(T.Text))
      fail(T, "unknown name '" + T.Text +
                  "' in static initializer: automatic object is unavailable");
    if (I->Aliases.count(T.Text))
      fail(T, "type alias requires a type or construction context");
    auto V = I->Names.find(T.Text);
    if (V != I->Names.end()) {
      if (V->second.Type.empty())
        fail(T, "use before initialization");
      return openStaticReference(V->second);
    }
  }
  if (Env.Values.count(T.Text))
    return Env.Values.at(T.Text);
  if (ConstantReceiver && U.lookupPath(ConstantReceiver->Type, T, false)) {
    if (Transaction)
      Transaction->checkAccess(*this, T);
    return member(load(*ConstantReceiver), T);
  }
  if (!Self.Type.empty()) {
    try {
      return member(Self, T);
    } catch (const Diagnostic &D) {
      if (!StringRef(D.Message).starts_with("unknown member"))
        throw;
    }
  }
  if (F && F->isStatic()) {
    auto Path = U.lookupPath(F->Owner, T, false);
    if (Path) {
      auto Owner = U.Records.at(F->Owner).Views.at(*Path);
      auto Key = Owner + "::" + T.Text;
      if (!U.StaticMembers.count(Key))
        fail(T, "instance field requires a receiver");
      checkAccess(U.StaticMembers.at(Key).second, Owner, T);
      if (!U.Globals.count(Key))
        fail(T, "static member used before initialization");
      return openStaticReference(U.Globals.at(Key));
    }
  }
  std::string Tail, Name = T.Text;
  if (auto Owner = memberQualifier(Name, T, Tail))
    Name = *Owner + "::" + Tail;
  auto Key = scopeKey(Prefix, Name,
                      [&](const std::string &K) { return U.Globals.count(K); });
  if (!Key.empty()) {
    auto Qualified = llvm::StringRef(Key);
    while (Qualified.contains("::")) {
      Qualified = Qualified.rsplit("::").first;
      if (auto It = U.MemberTypes.find(Qualified.str());
          It != U.MemberTypes.end())
        checkAccess(It->second.second, It->second.first, T);
    }
    if (auto I = U.StaticMembers.find(Key); I != U.StaticMembers.end())
      checkAccess(I->second.second, I->second.first, T);
    return openStaticReference(U.Globals.at(Key));
  }
  fail(T, "unknown name '" + T.Text + "'");
}
void Frame::checkAccess(const Node &Decl, const std::string &Owner,
                        const Token &At) {
  auto Access = Decl.Settings.find("access");
  if (Access == Decl.Settings.end() || Access->second == "public" ||
      (F && F->Owner == Owner) ||
      llvm::StringRef(Prefix).starts_with(Owner + "::"))
    return;
  if (F && Access->second == "protected") {
    Value SelfView{F->Owner};
    if (adjust(SelfView, Owner, At, false))
      return;
  }
  fail(At, "inaccessible member '" + Decl.Text + "'");
}
Function *Frame::checkSelected(Function *D, const Token &At) {
  checkAccess(D->Decl, D->Owner, At);
  if (auto It = D->Decl.Settings.find("control");
      It != D->Decl.Settings.end() && It->second == "delete")
    fail(At, "selected function is deleted");
  return D;
}
Value Frame::member(Value Obj, const Token &T) {
  auto It = U.Records.find(Obj.Type);
  if (It == U.Records.end() || !It->second.Complete)
    fail(T, "member access requires a complete record");
  auto Path = U.lookupPath(Obj.Type, T, false);
  if (!Path)
    fail(T, "unknown member '" + T.Text + "'");
  auto Owner = Path->empty() ? Obj.Type : It->second.Views.at(*Path);
  if (auto I = U.StaticMembers.find(Owner + "::" + T.Text);
      I != U.StaticMembers.end()) {
    checkAccess(I->second.second, Owner, T);
    if (!U.Globals.count(I->first))
      fail(T, "static member used before initialization");
    return openStaticReference(U.Globals.at(I->first));
  }
  Obj = baseView(Obj, *Path);
  auto &R = U.Records.at(Obj.Type);
  for (size_t I = 0; I < R.Fields.size(); ++I)
    if (R.Fields[I].Decl.Text == T.Text) {
      auto &Field = R.Fields[I];
      if (Obj.Address == PendingObject && PendingSlots.count(T.Text))
        fail(T, "use before initialization");
      if (Transaction && IR && Obj.Address == Self.Address)
        Transaction->checkAccess(*this, T);
      checkAccess(Field.Decl, Obj.Type, T);
      if (Obj.Address) {
        Value V{Field.Type, nullptr, fieldAddress(Obj, I),
                Obj.Readonly || Field.Decl.Const};
        return I < R.Bases.size() ? V : subobject(Obj, V);
      }
      return {Field.Type, B.CreateExtractValue(Obj.IR, I)};
    }
  fail(T, "unknown member '" + T.Text + "'");
}
void Frame::bindParams() {
  receivePointerCall();
  size_t I = U.aggregate(F->Result) ? 1 : 0;
  if (!F->Owner.empty() && !F->isStatic()) {
    Self = {F->Owner, nullptr, IR->getArg(I++), F->Decl.Const};
    Scopes[0].Names["this"] = {
        (F->Decl.Const ? "const<" + F->Owner + ">" : F->Owner) + "*",
        Self.Address};
  }
  for (size_t J = 0; J < F->Params.size(); ++J) {
    auto T = F->Params[J];
    auto &P = F->Decl.Params[J];
    auto *A = IR->getArg(I++);
    Value V;
    if (ends(T, "&")) {
      auto Base = baseRef(T);
      V = {unconst(Base), nullptr, A, P.Const || Base != unconst(Base)};
      if (TracksStorage) {
        V.Slot = slotFor(V);
        V.Generation = B.CreateCall(U.M.getFunction("cpn.generation"),
                                    {V.Slot, B.getFalse()});
        if (ends(V.Type, "*"))
          V.rememberPointerCell(V);
      }
    } else {
      llvm::Value *Ptr = A;
      if (!U.aggregate(T)) {
        Ptr = allocate(T, P.At);
        B.CreateStore(A, Ptr);
      }
      V = {T, nullptr, Ptr, P.Const};
      if (TracksStorage)
        trackLocal(V, "parameter.");
      Scopes[0].Drops.push_back(V);
    }
    if (carriesPointerBounds(T)) {
      V.BoundsCell = incomingPointerCell(J + 1);
      if (!ends(T, "&")) {
        readBounds(V, V.BoundsCell);
        V.BoundsCell = storedPointerCell(V.Address);
        saveBounds(V.BoundsCell, V);
      }
    } else if (ends(T, "&"))
      readReferent(V, incomingPointerCell(J + 1));
    if (ends(T, "&") || ends(T, "*"))
      V.Origins.insert(J);
    Scopes[0].Names[parameterBinding(F->Decl, J)] = V;
  }
}
void Frame::bindInlineParams(const std::vector<Value> &Actual,
                             const Function *DefaultDeclaration,
                             Value *DefaultReceiver) {
  const auto &Declaration = DefaultDeclaration ? *DefaultDeclaration : *F;
  Local Defaults;
  for (size_t I = 0; I < F->Params.size(); ++I) {
    const auto &Type = F->Params[I];
    const auto &Param = F->Decl.Params[I];
    const auto &Default = Declaration.DefaultParams[I];
    Value V;
    if (I < Actual.size())
      V = Actual[I];
    else {
      llvm::SaveAndRestore Policy(Opt, Declaration.Defaults.Configuration);
      llvm::SaveAndRestore Limit(LookupLimit, Declaration.Defaults.Through);
      llvm::SaveAndRestore Namespace(Prefix, Declaration.DefaultPrefix);
      llvm::SaveAndRestore Bindings(Env, Declaration.DefaultEnv);
      llvm::SaveAndRestore Receiver(ConstantReceiver, DefaultReceiver
                                                          ? DefaultReceiver
                                                          : ConstantReceiver);
      Scopes.push_back(Defaults);
      if (ends(Type, "&") && Default.Children.size() == 1)
        V = bindReference(eval(Default.Children.front()), Type, Default.At);
      else
        V = materialize(
            construct(unconst(baseRef(Type)), Default.Children, Default.At),
            Default.At);
      Scopes.pop_back();
    }
    if (ends(Type, "&"))
      V = bindReference(V, Type, Param.At);
    else {
      if (!IR) {
        V = materialize(convert(V, Type, Param.At), Param.At);
        if (!llvm::isa_and_nonnull<llvm::Constant>(V.IR))
          fail(Param.At, "constant argument required");
        V.Location.reset();
        V.Address = nullptr;
      } else if (!U.aggregate(Type)) {
        auto *Cell = allocate(Type, Param.At);
        B.CreateStore(load(convert(V, Type, Param.At)).IR, Cell);
        V.Address = Cell;
        V.IR = nullptr;
        if (carriesPointerBounds(Type)) {
          V.BoundsCell = storedPointerCell(Cell);
          saveBounds(V.BoundsCell, V);
        }
      }
      V.Readonly = Param.Const;
      V.Prvalue = V.Expiring = false;
      if (TracksStorage)
        trackLocal(V, "parameter.");
      if (IR)
        Scopes.front().Drops.push_back(V);
      else {
        auto Name =
            Param.Text.empty() ? "$arg." + std::to_string(I) : Param.Text;
        Scopes.front().Names[Name] = V;
        Scopes.front().ConstantDrops.push_back(Name);
      }
    }
    if (IR)
      V.IR = nullptr;
    if (!Param.Text.empty() || !F->Decl.Contracts.empty())
      Scopes.front().Names[parameterBinding(F->Decl, I)] = V;
    if (!Default.Text.empty())
      Defaults.Names[Default.Text] = V;
  }
}
Value Frame::boolean(const Node &N) {
  auto V = eval(N);
  if (V.Type == "never")
    return convert(V, "bool", N.At);
  if (V.Type != "bool")
    fail(N.At, "condition requires bool");
  if (N.K == Node::Binary && N.Text == "=" && !N.Grouped)
    Opt.warn(N.At, "assignment used directly as a Boolean condition");
  return V;
}
Value Frame::pointedObject(Value P, const Token &At) {
  if (!ends(P.Type, "*") || unconst(element(P.Type)) == "void")
    fail(At, "typed object pointer required");
  if (llvm::isa<llvm::ConstantPointerNull>(P.IR))
    fail(At, "null pointer access");
  if (IR && Opt.RawValidation)
    guard(B.CreateIsNull(P.IR));
  if (!IR && P.Upper) {
    int64_t Position, End;
    const auto &Layout = U.M.getDataLayout();
    if (llvm::GetPointerBaseWithConstantOffset(P.IR, Position, Layout) ==
            llvm::GetPointerBaseWithConstantOffset(P.Upper, End, Layout) &&
        Position == End)
      fail(At, "cannot dereference a one-past pointer");
  }
  if (IR && P.Upper)
    guard(
        B.CreateAnd(B.CreateIsNotNull(P.Upper), B.CreateICmpEQ(P.IR, P.Upper)));
  auto Base = element(P.Type);
  Value V{unconst(Base), nullptr, P.IR, Base != unconst(Base)};
  V.borrow(P);
  V.ElementLower = P.Lower;
  V.ElementUpper = P.Upper;
  return V;
}

Value Frame::place(const Node &N, bool NeedLive) {
  Value V;
  if (N.K == Node::Name)
    V = lookup(N.At);
  else if (N.K == Node::Unary && N.Text == "*")
    V = pointedObject(eval(N.Children[0]), N.At);
  else if (N.K == Node::Member) {
    auto Base = N.Definition ? eval(N.Children[0]) : place(N.Children[0]);
    if (N.Definition) {
      Base = pointedObject(Base, N.At);
      ensureLive(Base, N.At);
    }
    V = member(Base, N.At);
  } else if (N.K == Node::Index)
    V = subscript(N);
  else
    V = eval(N);
  if (!V.Address)
    fail(N.At, "object lvalue required");
  if (IR && V.Slot && !V.PointerCell && !V.IR && !V.BoundsCell &&
      ends(V.Type, "*")) {
    V.rememberPointerCell(V);
    V.Storage.clear();
  }
  if (NeedLive && (!V.BoundsCell || V.PointerCell))
    ensureLive(V, N.At);
  if (IR && carriesPointerBounds(V.Type) && !V.BoundsCell)
    V.BoundsCell = storedPointerCell(V.Address);
  return V;
}
Value Frame::subscript(const Node &N) {
  auto Base = place(N.Children[0]);
  auto Index = eval(N.Children[1]);
  if (U.Records.count(Base.Type))
    return applyOperator("operator[]", N.At, {{Base, Index}, {}, {}});
  if (!ends(Base.Type, "]") || !integer(Index.Type) || !Base.Address)
    fail(N.At, "array object and integer index required");
  auto *Array = llvm::cast<llvm::ArrayType>(U.ir(Base.Type));
  auto Count = ends(Base.Type, "[0]") ? 0 : Array->getNumElements();
  if (auto *K = llvm::dyn_cast<llvm::ConstantInt>(Index.IR)) {
    if (K->getValue().uge(Count))
      fail(N.At, "array index outside extent");
  }
  if (!IR) {
    auto *Address = symbolicAddress(Base, N.At);
    auto *IndexValue = llvm::dyn_cast<llvm::ConstantInt>(Index.IR);
    if (!IndexValue)
      fail(N.At, "constant array index required");
    auto E = element(Base.Type);
    llvm::Constant *Indices[] = {B.getInt32(0),
                                 B.getInt64(IndexValue->getZExtValue())};
    Value V{unconst(E), nullptr,
            llvm::ConstantExpr::getGetElementPtr(U.M.getDataLayout(), Array,
                                                 Address, Indices),
            Base.Readonly || E != unconst(E)};
    V.ElementLower = Address;
    V.ElementUpper = llvm::ConstantExpr::getGetElementPtr(
        U.M.getDataLayout(), Array->getElementType(), Address,
        B.getInt64(Count));
    return V;
  }
  auto *I = B.CreateIntCast(Index.IR, B.getInt64Ty(), signedType(Index.Type));
  guard(B.CreateICmpUGE(I, B.getInt64(Count)));
  auto E = element(Base.Type);
  auto V = subobject(
      Base, {unconst(E), nullptr,
             B.CreateInBoundsGEP(Array, Base.Address, {B.getInt32(0), I}),
             Base.Readonly || E != unconst(E)});
  if (TracksStorage) {
    V.ArraySlot = slotFor(Base);
    V.ArrayGeneration = Base.Generation
                            ? Base.Generation
                            : B.CreateCall(U.M.getFunction("cpn.generation"),
                                           {V.ArraySlot, B.getFalse()});
  }
  V.ElementLower = Base.Address;
  V.ElementUpper =
      B.CreateGEP(Array->getElementType(), Base.Address, B.getInt64(Count));
  return V;
}
std::string Frame::unevaluatedType(const Node &N, bool IncludeCategory) {
  const bool Address = N.K == Node::Unary && N.Text == "&";
  const Node &Subject = Address ? N.Children.front() : N;
  if (Subject.K == Node::Name && llvm::none_of(Scopes, [&](const Local &S) {
        return S.Names.count(Subject.Text);
      })) {
    auto Group = visibleOverloads(callKey(Subject.Text));
    if (!Group.empty()) {
      if (Group.size() != 1 ||
          (!Group.front()->Owner.empty() && !Group.front()->isStatic()))
        fail(N.At, "type query requires a unique native function");
      return U.callableType(*checkSelected(Group.front(), N.At)) +
             (Address ? "*" : "");
    }
  }
  auto *Tmp = llvm::Function::Create(
      llvm::FunctionType::get(B.getVoidTy(), false),
      llvm::GlobalValue::InternalLinkage, "cpn.unevaluated", U.M);
  struct Discard {
    llvm::Function *Fn;
    ~Discard() { Fn->eraseFromParent(); }
  } Guard{Tmp};
  // Type checking uses the caller's bindings, but unevaluated calls do not
  // add a lifecycle effect to the surrounding function.
  Function QueryOwner;
  if (F)
    QueryOwner = *F;
  Frame Probe(U, F ? &QueryOwner : nullptr, Tmp, Prefix);
  Probe.TypeQuery = true;
  Probe.Opt = Opt;
  Probe.LookupLimit = LookupLimit;
  Probe.Env = Env;
  Probe.Scopes = Scopes;
  Probe.Self = Self;
  Probe.B.SetInsertPoint(Probe.block("entry"));
  auto V = Probe.eval(N);
  auto T = Probe.materializationType(V.Type, N.At);
  if (IncludeCategory && V.Readonly)
    T = qualifyConst(T);
  if (IncludeCategory && V.Address && !V.Prvalue)
    T += V.Expiring ? "&&" : "&";
  return T;
}
Value Frame::constantEval(const Node &N) {
  if (IR) {
    Frame CF(U, F, nullptr, Prefix);
    CF.Opt = Opt;
    CF.LookupLimit = LookupLimit;
    CF.Scopes = Scopes;
    CF.Env = Env;
    return CF.constantEval(N);
  }
  ConstantActivation Activation(U, N.At);
  auto V = eval(N);
  if (!llvm::isa_and_nonnull<llvm::Constant>(V.IR))
    fail(N.At, "constant expression required");
  return V;
}
Value Frame::eval(const Node &N, std::string Expected, llvm::Value *Dest) {
  llvm::SaveAndRestore Destination(ExpressionDestination,
                                   Value{Expected, nullptr, Dest});
  auto &A = N.Children;
  auto Op = N.Text;
  if (InPredicate && (N.K == Node::Lambda ||
                      (N.K == Node::Unary && (Op == "++" || Op == "--")) ||
                      (N.K == Node::Binary && assignment(Op))))
    fail(N.At,
         "contract predicate cannot mutate objects or construct closures");
  if (!IR && U.ConstantDepth)
    U.chargeConstant(N.At);
  if (!IR && ((N.K == Node::Unary && (Op == "++" || Op == "--")) ||
              (N.K == Node::Binary && assignment(Op)))) {
    if (Transaction && N.K == Node::Binary && Op == "=")
      if (auto V = Transaction->firstWrite(*this, N))
        return *V;
    return constantAssignment(N);
  }
  const bool ImplicitThis =
      ConstantReceiver && (!F || !F->Decl.Settings.count("closure"));
  if (ImplicitThis && N.K == Node::Unary && Op == "*" && A[0].K == Node::Name &&
      A[0].Text == "this")
    return constantSelf(N.At);
  if (!IR && (N.K == Node::Name || N.K == Node::Member || N.K == Node::Index ||
              (N.K == Node::Unary && Op == "*")))
    if (auto Place = constantPlace(N)) {
      if (Place->Type.empty())
        fail(N.At, "use before initialization");
      auto V = Place->read(*this, N.At);
      V.Location = std::make_shared<ConstantPlace>(std::move(*Place));
      return V;
    }
  if (!IR && ImplicitThis && N.K == Node::Name && Op == "this") {
    auto Self = constantSelf(N.At);
    return constantAddress(*Self.Location, N.At);
  }
  switch (N.K) {
  case Node::Lambda:
    return closure(N);
  case Node::Real: {
    Value V{"real"};
    for (char C : N.Text)
      if (C != '_')
        V.RealText += C;
    return floating(Expected) ? floatingConvert(V, Expected, N.At) : V;
  }
  case Node::Number:
    return constant(integerLiteral(N.At));
  case Node::Character: {
    auto S = unquote(N.At);
    uint32_t C = (unsigned char)S[0];
    if (C >= 128) {
      C &= 0x7f >> S.size();
      for (size_t I = 1; I < S.size(); ++I)
        C = (C << 6) | (uint8_t(S[I]) & 63);
    }
    return literal(C, "char");
  }
  case Node::String: {
    auto S = unquote(N.At);
    auto *C = llvm::ConstantDataArray::getString(U.C, S, true);
    auto *G = new llvm::GlobalVariable(U.M, C->getType(), true,
                                       llvm::GlobalValue::PrivateLinkage, C,
                                       "cpn.string");
    U.ConstantObjects.insert(G);
    return {"u8[" + std::to_string(S.size() + 1) + "]", C, G, true};
  }
  case Node::Name:
    if (Op == "true" || Op == "false")
      return literal(Op == "true", "bool");
    else if (Op == "nullptr")
      return {"nullptr_t", B.getInt8(0)};
    else if (builtinPredicate(Op) || constraint(Op))
      return literal(predicate(N), "bool");
    else
      return load(lookup(N.At));
  case Node::Index:
    if (!IR) {
      auto Base = eval(A[0]);
      auto *Array = llvm::dyn_cast_or_null<llvm::Constant>(Base.IR);
      auto Index = eval(A[1]);
      auto *I = llvm::dyn_cast_or_null<llvm::ConstantInt>(Index.IR);
      if (!ends(Base.Type, "]") || !Array || !integer(Index.Type) || !I ||
          ends(Base.Type, "[0]") ||
          I->getValue().uge(
              llvm::cast<llvm::ArrayType>(Array->getType())->getNumElements()))
        fail(N.At, "constant array element requires a valid constant index");
      return {unconst(element(Base.Type)),
              Array->getAggregateElement(unsigned(I->getZExtValue()))};
    }
    return load(subscript(N));
  case Node::Member:
    if (ImplicitThis && N.Definition && A[0].K == Node::Name &&
        A[0].Text == "this") {
      if (Transaction)
        Transaction->checkAccess(*this, N.At);
      return member(load(*ConstantReceiver), N.At);
    }
    if (!IR && !N.Definition) {
      auto Base = eval(A[0]);
      if (U.Records.count(Base.Type) &&
          llvm::isa_and_nonnull<llvm::Constant>(Base.IR)) {
        Base.Address = nullptr;
        return member(Base, N.At);
      }
    }
    return load(place(N));
  case Node::Call: {
    auto V = call(A[0], std::vector<Node>(A.begin() + 1, A.end()));
    if (!IR)
      return constantTemporary(V);
    if (Dest && V.Address == Dest && U.aggregate(V.Type))
      V.Prvalue = V.Expiring = true;
    return V;
  }
  case Node::Configured: {
    auto Old = Opt;
    configure(Opt, N, ConfigScope::Expression);
    auto V = eval(A[0], Expected, Dest);
    Opt = Old;
    return V;
  }
  case Node::Unary: {
    if (Op == "sizeof" || Op == "alignof") {
      auto T = A[0].K == Node::TypeArg ? resolve(A[0].Type, N.At)
               : A[0].K == Node::String
                   ? "u8[" + std::to_string(unquote(A[0].At).size() + 1) + "]"
                   : "";
      if (T.empty())
        T = unevaluatedType(A[0], false);
      auto *Ty = U.ir(T, N.At);
      if (!Ty->isSized())
        fail(N.At, "complete object type required");
      return literal(
          Op == "sizeof"
              ? U.M.getDataLayout().getTypeAllocSize(Ty).getFixedValue()
              : U.M.getDataLayout().getABITypeAlign(Ty).value(),
          "usize");
    }
    if (Op == "&") {
      auto Group = A[0].K == Node::Name ? visibleOverloads(callKey(A[0].Text))
                                        : std::vector<Function *>{};
      if (!Group.empty()) {
        if (!ends(Expected, "*") || !U.Signatures.count(element(Expected)))
          fail(N.At, "target function-pointer type required");
        auto &Sig = U.Signatures.at(element(Expected));
        Function *Match = nullptr;
        for (auto *Candidate : Group) {
          if ((!Candidate->Owner.empty() && !Candidate->isStatic()) ||
              Candidate->Result != Sig.front() ||
              Candidate->Params !=
                  std::vector<std::string>(Sig.begin() + 1, Sig.end()) ||
              (callableFlag(element(Expected), " noexcept") &&
               !Candidate->Decl.Noexcept))
            continue;
          if (Match)
            fail(N.At, "no unique compatible function");
          Match = Candidate;
        }
        if (!Match)
          fail(N.At, "no unique compatible function");
        if (!callableFlag(element(Expected), " whole"))
          U.RestrictedPointers.emplace_back(Match, N.At);
        auto Source = U.callableType(*checkSelected(Match, N.At));
        auto Target = element(Expected);
        if (callableFlag(Source, " whole") && !callableFlag(Target, " whole"))
          fail(N.At, "function pointer must preserve lifecycle_effect(whole)");
        if (!U.compatibleCallable(Source, Target))
          fail(N.At, "incompatible function-pointer effect or borrow contract");
        return {Expected, U.foreignContractEntry(*Match)};
      }
      if (!IR)
        if (auto Place = constantPlace(A[0]))
          return constantAddress(*Place, N.At);
      auto V = place(A[0]);
      Value P{(V.Readonly ? qualifyConst(V.Type) : V.Type) + "*", V.Address};
      P.borrow(V.objectDesignation());
      if (!V.ElementLower) {
        P.ArraySlot = nullptr;
        P.ArrayGeneration = nullptr;
        if (V.BoundsCell && !V.PointerCell) {
          P.Slot = nullptr;
          P.Generation = nullptr;
          P.Storage.clear();
        }
      }
      if (!IR) {
        auto *Address = symbolicAddress(V, N.At);
        P.Lower = V.ElementLower ? V.ElementLower : Address;
        P.Upper = V.ElementUpper ? V.ElementUpper
                                 : llvm::ConstantExpr::getGetElementPtr(
                                       U.M.getDataLayout(), U.ir(V.Type),
                                       Address, B.getInt64(1));
        return P;
      }
      auto *End = B.CreateGEP(U.ir(V.Type), V.Address, B.getInt64(1));
      P.Lower = V.ElementLower
                    ? B.CreateSelect(B.CreateIsNotNull(V.ElementLower),
                                     V.ElementLower, V.Address)
                    : V.Address;
      P.Upper = V.ElementUpper
                    ? B.CreateSelect(B.CreateIsNotNull(V.ElementUpper),
                                     V.ElementUpper, End)
                    : End;
      return P;
    }
    if (Op == "*")
      return load(place(N));
    if (Op == "++" || Op == "--") {
      Node Bop = N;
      Bop.Text = Op == "++" ? "+" : "-";
      auto D = place(A[0]);
      if (D.Readonly)
        fail(N.At, "writable lvalue required");
      auto V = load(D);
      if (U.Records.count(D.Type)) {
        if (D.Expiring)
          fail(N.At, "increment or decrement requires a writable lvalue");
        return applyOperator(std::string(N.Definition ? "operator postfix "
                                                      : "operator prefix ") +
                                 Op,
                             N.At, {{V}, {}, {}});
      }
      auto Next = binary(Bop, V, literal(1));
      B.CreateStore(Next.IR, D.Address);
      if (D.BoundsCell)
        saveBounds(D.BoundsCell, Next);
      if (N.Definition) {
        V.Address = nullptr;
        V.BoundsCell = nullptr;
        V.Expiring = V.Prvalue = true;
        return V;
      }
      Next.Address = D.Address;
      Next.BoundsCell = D.BoundsCell;
      Next.Prvalue = Next.Expiring = false;
      return Next;
    }
    auto V = eval(A[0], Op == "-" && A[0].K == Node::Real ? "" : Expected);
    if (U.Records.count(V.Type))
      return applyOperator("operator" + Op, N.At, {{V}, {}, {}});
    if (Op == "!") {
      if (V.Type != "bool")
        fail(N.At, "logical negation requires bool");
      return {"bool", B.CreateNot(V.IR)};
    }
    if ((floating(V.Type) || V.Type == "real") && (Op == "+" || Op == "-")) {
      if (V.Type == "real") {
        if (Op == "-")
          V.RealText = llvm::StringRef(V.RealText).starts_with("-")
                           ? V.RealText.substr(1)
                           : "-" + V.RealText;
        return floating(Expected) ? floatingConvert(V, Expected, N.At) : V;
      }
      return {V.Type, Op == "-" ? B.CreateFNeg(V.IR) : V.IR};
    }
    if (!integer(V.Type))
      fail(N.At, "integer operand required");
    if (Op == "+")
      return {V.Type, V.IR};
    if (Op == "-") {
      Node Sub = N;
      Sub.Text = "-";
      return binary(Sub, literal(0), V);
    }
    if (V.Type == "integer")
      V = convert(
          V, Expected.empty() ? materializationType(V.Type, N.At) : Expected,
          N.At);
    return {V.Type, B.CreateNot(V.IR)};
  }
  case Node::Conditional:
  case Node::Binary: {
    if (N.K == Node::Conditional || Op == "&&" || Op == "||") {
      auto C = boolean(A[0]);
      if (!IR) {
        auto *K = llvm::dyn_cast<llvm::ConstantInt>(C.IR);
        if (!K)
          fail(N.At, "constant expression required");
        bool Cond = !K->isZero();
        if (N.K == Node::Conditional)
          return eval(A[Cond ? 1 : 2], Expected);
        if ((Op == "&&" && !Cond) || (Op == "||" && Cond))
          return C;
        return boolean(A[1]);
      }
      auto *Yes = block("then"), *No = block("else"), *Done = block("end");
      B.CreateCondBr(C.IR, Yes, No);
      size_t Mark = Temps.size();
      bool EntryLive = Live;
      auto arm = [&](unsigned I, llvm::BasicBlock *Entry,
                     std::vector<Value> &Owned) {
        B.SetInsertPoint(Entry);
        Live = EntryLive;
        auto V = N.K == Node::Conditional   ? eval(A[I], Expected, Dest)
                 : (I == 1) == (Op == "&&") ? boolean(A[1])
                                            : literal(I == 1, "bool");
        Owned.assign(Temps.begin() + Mark, Temps.end());
        Temps.resize(Mark);
        return EntryLive && !Live ? Value{"never"} : V;
      };
      std::vector<Value> YesTemps, NoTemps;
      auto EntryState = Active;
      auto EntryPositions =
          Transaction ? Transaction->positions() : Construction::Positions{};
      auto X = arm(1, Yes, YesTemps);
      auto *EndYes = B.GetInsertBlock();
      auto YesState = Active;
      auto YesPositions =
          Transaction ? Transaction->positions() : Construction::Positions{};
      Active = std::move(EntryState);
      if (Transaction)
        Transaction->restore(EntryPositions);
      auto Y = arm(2, No, NoTemps);
      auto *EndNo = B.GetInsertBlock();
      if (X.Type == "never" || Y.Type == "never") {
        // The diverging arm has no edge into the join, including for
        // aggregates and references whose address comes from the other arm.
        bool Left = X.Type != "never";
        if (X.Type == "never") {
          B.SetInsertPoint(EndYes);
          B.CreateUnreachable();
        }
        if (Y.Type == "never") {
          B.SetInsertPoint(EndNo);
          B.CreateUnreachable();
        }
        if (X.Type == Y.Type) {
          B.SetInsertPoint(Done);
          Live = false;
          return {"never"};
        }
        B.SetInsertPoint(Left ? EndYes : EndNo);
        branch(Done);
        B.SetInsertPoint(Done);
        auto &Owned = Left ? YesTemps : NoTemps;
        Temps.insert(Temps.end(), Owned.begin(), Owned.end());
        if (Left) {
          Active = std::move(YesState);
          if (Transaction)
            Transaction->restore(YesPositions);
        }
        Live = EntryLive;
        return Left ? X : Y;
      }
      if (auto *Known = llvm::dyn_cast<llvm::ConstantInt>(C.IR)) {
        if (!Known->isZero()) {
          Active = std::move(YesState);
          if (Transaction)
            Transaction->restore(YesPositions);
        }
      } else {
        joinStorage(YesState);
        if (Transaction) {
          auto Joined = Transaction->positions();
          Joined.insert(YesPositions.begin(), YesPositions.end());
          Transaction->restore(Joined);
        }
      }
      auto T =
          X.Type == "integer" || (X.Type == "nullptr_t" && ends(Y.Type, "*"))
              ? Y.Type
              : X.Type;
      if (T == "integer")
        T = Expected.empty() ? materializationType(T, N.At) : Expected;
      bool OwnedResult = U.aggregate(T) && (X.Prvalue || Y.Prvalue);
      auto finishArm = [&](Value V, std::vector<Value> &Owned,
                           llvm::BasicBlock *&Exit) {
        B.SetInsertPoint(Exit);
        V = convert(V, T, N.At);
        if (OwnedResult) {
          auto Source = V;
          if (!V.Prvalue || Dest)
            V = materialize(V, N.At, Dest);
          llvm::erase_if(Owned, [&](const Value &Temp) {
            return Source.Prvalue && Temp.Address == Source.Address;
          });
          if (Dest)
            V.Address = Dest;
        }
        Exit = B.GetInsertBlock();
        branch(Done);
        return V;
      };
      X = finishArm(X, YesTemps, EndYes);
      Y = finishArm(Y, NoTemps, EndNo);
      B.SetInsertPoint(Done);
      auto merge = [&](llvm::Value *L, llvm::Value *R) -> llvm::Value * {
        if (L == R)
          return L;
        auto *Phi = B.CreatePHI(L->getType(), 2);
        Phi->addIncoming(L, EndYes);
        Phi->addIncoming(R, EndNo);
        return Phi;
      };
      // Only the evaluated arm's temporaries exist. Keep their guarded
      // addresses until the enclosing full-expression has finished.
      auto selectedTemps = [&](std::vector<Value> &Owned, bool TrueArm) {
        auto *Null = llvm::ConstantPointerNull::get(B.getPtrTy());
        for (auto Temp : Owned) {
          Temp.Address =
              TrueArm ? merge(Temp.Address, Null) : merge(Null, Temp.Address);
          Temp.IR = nullptr;
          Temp.OptionalTemp = true;
          Temps.push_back(Temp);
        }
      };
      selectedTemps(YesTemps, true);
      selectedTemps(NoTemps, false);
      Value V{T, T == "void" ? nullptr : merge(X.IR, Y.IR)};
      if (X.Address && Y.Address) {
        V.Address = merge(X.Address, Y.Address);
        V.Readonly = X.Readonly || Y.Readonly;
        V.Expiring = OwnedResult || (X.Expiring && Y.Expiring);
        V.Prvalue = OwnedResult;
        if (V.Prvalue && V.Address != Dest)
          Temps.push_back(V);
      }
      auto metadata = [&](llvm::Value *Left,
                          llvm::Value *Right) -> llvm::Value * {
        if (!Left && !Right)
          return nullptr;
        auto *Zero =
            llvm::Constant::getNullValue((Left ? Left : Right)->getType());
        return merge(Left ? Left : Zero, Right ? Right : Zero);
      };
      V.Lower = metadata(X.Lower, Y.Lower);
      V.Upper = metadata(X.Upper, Y.Upper);
      V.ElementLower = metadata(X.ElementLower, Y.ElementLower);
      V.ElementUpper = metadata(X.ElementUpper, Y.ElementUpper);
      V.ArraySlot = metadata(X.ArraySlot, Y.ArraySlot);
      V.ArrayGeneration = metadata(X.ArrayGeneration, Y.ArrayGeneration);
      if (V.Address && (X.PointerCell || Y.PointerCell)) {
        auto A = X.PointerCell.value_or(Value::PointerCellLifetime{});
        auto D = Y.PointerCell.value_or(Value::PointerCellLifetime{});
        V.PointerCell = Value::PointerCellLifetime{
            metadata(A.Slot, D.Slot),
            metadata(A.Generation, D.Generation),
            metadata(A.ArraySlot, D.ArraySlot),
            metadata(A.ArrayGeneration, D.ArrayGeneration),
            A.Storage == D.Storage ? A.Storage : "",
            A.ExtentType == D.ExtentType ? A.ExtentType : "",
            A.Subobject || D.Subobject,
            A.BaseView || D.BaseView};
      }
      V.Slot = metadata(X.Slot, Y.Slot);
      V.Generation = metadata(X.Generation, Y.Generation);
      if (X.BoundsCell && Y.BoundsCell)
        V.BoundsCell = merge(X.BoundsCell, Y.BoundsCell);
      if (X.Storage == Y.Storage)
        V.Storage = X.Storage;
      if (X.ExtentType == Y.ExtentType)
        V.ExtentType = X.ExtentType;
      V.Subobject = X.Subobject || Y.Subobject;
      V.Origins = X.Origins;
      V.Origins.insert(Y.Origins.begin(), Y.Origins.end());
      return V;
    }
    if (assignment(Op)) {
      if (Transaction && Op == "=")
        if (auto V = Transaction->firstWrite(*this, N))
          return *V;
      auto D = place(A[0]);
      if (D.Readonly)
        fail(N.At, "writable lvalue required");
      auto Old = Op == "=" ? Value() : load(D);
      auto R = eval(A[1], D.Type);
      if (U.Records.count(D.Type)) {
        auto Special = R.Expiring || !R.Address ? SpecialOperation::MoveAssign
                                                : SpecialOperation::CopyAssign;
        if (Op != "=" || D.Type != R.Type ||
            !U.Records.at(D.Type).Special.count(Special)) {
          if (Op == "=" && D.Type == R.Type &&
              methodOwner(D.Type, Token{"operator=", N.At.Line, N.At.Column})
                  .empty())
            fail(N.At, R.Expiring ? "no available move assignment"
                                  : "no available copy assignment");
          return applyOperator("operator" + Op, N.At, {{D, R}, {}, {}});
        }
      }
      if (Op != "=") {
        Node Math = N;
        Math.Text.pop_back();
        R = binary(Math, Old, R);
      }
      R = convert(R, D.Type, N.At);
      if (U.Records.count(D.Type) || ends(D.Type, "]")) {
        transfer(R, D.Address,
                 R.Expiring || !R.Address ? SpecialOperation::MoveAssign
                                          : SpecialOperation::CopyAssign,
                 N.At);
        return load(D);
      }
      if (D.BoundsCell) {
        saveBounds(D.BoundsCell, R);
        // Branches may rebind a local pointer to a different extent. Keep its
        // dynamic stamp and union of potential parameter origins.
        for (auto &Scope : Scopes)
          for (auto &[Name, Local] : Scope.Names)
            if (Local.BoundsCell == D.BoundsCell) {
              if (Local.Storage != R.Storage)
                Local.Storage.clear();
              Local.Origins.insert(R.Origins.begin(), R.Origins.end());
            }
      }
      if (ends(D.Type, "*") &&
          llvm::isa<llvm::GlobalVariable>(
              llvm::getUnderlyingObject(D.Address)) &&
          F)
        for (auto Origin : R.Origins)
          if (F->NoEscape.count(Origin))
            fail(N.At, "noescape parameter retained in static storage");
      B.CreateStore(R.IR, D.Address);
      D.IR = R.IR;
      return load(D);
    }
    // Only all-literal floating subexpressions inherit the destination's
    // format. A typed operand is a rounding boundary of its own.
    auto LiteralTree = [](const Node &E, auto &&Visit) -> bool {
      if (E.K == Node::Number || E.K == Node::Real)
        return true;
      if (E.K != Node::Unary && E.K != Node::Binary)
        return false;
      return llvm::all_of(E.Children, [&](auto &C) { return Visit(C, Visit); });
    };
    bool Propagate = floating(Expected) && LiteralTree(N, LiteralTree);
    Value L, R;
    if (Propagate) {
      L = eval(A[0], Expected);
      R = eval(A[1], Expected);
    } else {
      auto Operands = evaluateArguments(A);
      if (llvm::any_of(Operands.Values,
                       [&](const Value &V) { return U.Records.count(V.Type); }))
        return applyOperator("operator" + Op, N.At, std::move(Operands));
      admitArguments(Operands, nullptr, N.At);
      L = Operands.Values[0];
      R = Operands.Values[1];
    }
    if (L.Type == "integer" && R.Type == "integer" &&
        (Op == "&" || Op == "|" || Op == "^" || Op == "<<" || Op == ">>")) {
      auto T = integer(Expected) && Expected != "integer"
                   ? Expected
                   : materializationType(L.Type, N.At);
      L = convert(L, T, N.At);
      if (Op != "<<" && Op != ">>")
        R = convert(R, T, N.At);
    }
    if (floating(L.Type) || floating(R.Type) || L.Type == "real" ||
        R.Type == "real")
      return floatingBinary(N, L, R, Expected);
    return binary(N, L, R);
  }
  default:
    fail(N.At, "expected a value expression");
  }
}
// Ranks order exact binding, then qualification/base/null conversions, then
// numeric conversions. Each argument retains its own rank during selection.
std::optional<unsigned> Frame::conversionRank(Value V, const std::string &Param,
                                              const Token &At) {
  if (V.Type == "never")
    return 0;
  auto Base = baseRef(Param), T = unconst(Base);
  bool Ref = Base != Param, RO = T != Base,
       Lvalue = (V.Address || V.Location) && !V.Expiring;
  if (Ref && ((ends(Param, "&&") && Lvalue) ||
              (!ends(Param, "&&") && !RO && !Lvalue) || (!RO && V.Readonly)))
    return {};
  unsigned Qual = Ref && RO && !V.Readonly ? 1 : 0;
  if (V.Type == T)
    return Qual;
  if (Ref && U.Records.count(V.Type) && adjust(V, T, At, false))
    return 1 + Qual;
  if (Ref && (Lvalue || (!RO && !ends(Param, "&&"))))
    return {};
  if (ends(T, "*")) {
    if (V.Type == "nullptr_t")
      return 1;
    if (ends(V.Type, "*")) {
      auto From = element(V.Type), To = element(T);
      if (From != unconst(From) && To == unconst(To))
        return {};
      Value View{unconst(From)};
      if (adjust(View, unconst(To), At, false))
        return 1;
      if (U.compatibleCallable(From, To))
        return 1;
    }
  }
  if (integer(V.Type) && integer(T) && implicitInteger(V, T))
    return V.Type == "integer" && T == Opt.DefaultInt ? Qual : 3;
  if (floating(T)) {
    if (V.Type == "real" || V.Type == "integer") {
      try {
        floatingConvert(V, T, At);
      } catch (const Diagnostic &) {
        return {};
      }
      return V.Type == "real" && T == Opt.DefaultReal ? Qual : 3;
    }
    if (V.Type == "f32" && T == "f64")
      return 3;
    if (V.Type == "f64" && T == "f32") {
      if (auto *C = llvm::dyn_cast<llvm::ConstantFP>(V.IR)) {
        auto Number = C->getValueAPF();
        bool Lost;
        Number.convert(llvm::APFloat::IEEEsingle(),
                       llvm::RoundingMode::NearestTiesToEven, &Lost);
        if (!Lost)
          return 3;
      }
    }
  }
  return {};
}
std::vector<Function *> Frame::visibleOverloads(const std::string &Key) const {
  std::vector<Function *> Group;
  if (auto It = U.Overloads.find(Key); It != U.Overloads.end())
    for (auto *D : It->second)
      if (!D->Owner.empty() || D->DeclaredAt <= LookupLimit)
        Group.push_back(D);
  return Group;
}
std::string Frame::callKey(const std::string &Name,
                           const std::string &Owner) const {
  if (!Owner.empty())
    return Owner + "::" + Name;
  auto Key = scopeKey(Prefix, Name, [&](const std::string &K) {
    auto Fam = U.Families.find(K);
    return !visibleOverloads(K).empty() ||
           (Fam != U.Families.end() && Fam->second.Site.Through <= LookupLimit);
  });
  return Key.empty() ? Name : Key;
}
Function *Frame::prepareCandidate(const Family &Source, const std::string &Key,
                                  const Node &N,
                                  const std::vector<Value> &Args) {
  Family Fam = Source;
  if (!Fam.Decl.Generics.empty() && Fam.Decl.Generics.back().Pack)
    Fam = expand(Fam, deducePackArity(Fam, N, Args), N.At);
  if (Args.size() > Fam.Decl.Params.size() ||
      (Args.size() < Fam.Decl.Params.size() &&
       Fam.Decl.Params[Args.size()].Children.empty()))
    throw DeductionFailure{{N.At, "no viable overload"}};
  auto S = bind(Fam, N.TemplateArgs, Args, N.At);
  std::string ID = Key + "$" + std::to_string(Fam.Decl.At.Line) + "." +
                   std::to_string(Fam.Decl.At.Column) + "<";
  for (auto &P : Fam.Decl.Generics) {
    if (P.K == Node::TypeParam)
      ID += S.Types.at(P.Text);
    else {
      llvm::SmallString<32> V;
      llvm::cast<llvm::ConstantInt>(S.Values.at(P.Text).IR)
          ->getValue()
          .toString(V, 10, signedType(P.Type));
      ID += V.str();
    }
    ID += ",";
  }
  ID += ">";
  if (auto I = U.Instances.find(ID); I != U.Instances.end())
    return I->second;
  EnterDefinition Site(U, Fam.Site);
  if (!Fam.Decl.TemplateArgs.empty()) {
    Frame Probe(U, nullptr, nullptr, Fam.Prefix);
    Probe.Env = S;
    auto V = Probe.constantEval(Fam.Decl.TemplateArgs.front());
    if (V.Type != "bool")
      fail(N.At, "a generic requirement must have Boolean type");
    if (llvm::cast<llvm::ConstantInt>(V.IR)->isZero())
      throw DeductionFailure{{N.At, "constraint is not satisfied"}};
  }
  U.chargeInstance(N.At);
  auto *D = U.declare(Fam.Decl, ID, Fam.Prefix, S, Fam.Owner);
  D->Origin = &Source;
  U.attachGenericBody(*D, Source);
  U.Instances[ID] = D;
  return D;
}

Function *Frame::select(std::string Name, const Node &N,
                        const std::vector<Value> &Args, Value Receiver,
                        bool Operator, Function *Generated) {
  auto Key = callKey(Name, Receiver.Type);
  struct Candidate {
    Function *Decl;
    std::vector<unsigned> Ranks;
  };
  auto Better = [Generated](const Candidate &A, const Candidate &B) {
    bool Strict = false;
    for (size_t I = 0; I < A.Ranks.size(); ++I) {
      if (A.Ranks[I] > B.Ranks[I])
        return false;
      Strict |= A.Ranks[I] < B.Ranks[I];
    }
    return Strict ||
           (Generated && B.Decl == Generated && A.Decl != Generated) ||
           betterPattern(A.Decl->Origin ? A.Decl->Origin->Decl : A.Decl->Decl,
                         B.Decl->Origin ? B.Decl->Origin->Decl : B.Decl->Decl);
  };
  std::vector<Candidate> Best;
  auto Group =
      N.ExplicitApplication ? std::vector<Function *>{} : visibleOverloads(Key);
  if (Generated && llvm::none_of(Group, [&](Function *D) {
        return D->Params == Generated->Params;
      }))
    Group.push_back(Generated);
  if (Operator) {
    auto Owner = methodOwner(Args.front().Type, N.At);
    if (!Owner.empty()) {
      auto Members = visibleOverloads(Owner + "::" + Name);
      Group.insert(Group.end(), Members.begin(), Members.end());
    }
  }
  std::optional<Diagnostic> Rejection;
  if (auto It = U.FunctionFamilies.find(Key); It != U.FunctionFamilies.end())
    for (auto &Fam : It->second) {
      if (Fam.Site.Through > LookupLimit)
        continue;
      try {
        Group.push_back(prepareCandidate(Fam, Key, N, Args));
      } catch (const DeductionFailure &D) {
        Rejection = D;
      }
    }
  if (Group.empty()) {
    if (Rejection)
      throw *Rejection;
    fail(N.At, "unknown name '" + Name + "'");
  }
  for (auto *D : Group) {
    bool MemberOperand = Operator && !D->Owner.empty();
    auto Actual = llvm::ArrayRef(Args).drop_front(MemberOperand ? 1 : 0);
    const auto &Object = MemberOperand ? Args.front() : Receiver;
    if (Object.Type.empty() && !D->Owner.empty() && !D->isStatic())
      continue;
    if (!Object.Type.empty() && !D->isStatic()) {
      auto Q = D->Decl.Settings.find("category");
      if (Q != D->Decl.Settings.end() && !Q->second.empty() &&
          Q->second != (Object.Expiring ? "&&" : "&"))
        continue;
      if (Object.Readonly && !D->Decl.Const && D->Decl.K == Node::Function)
        continue;
    }
    if (Actual.size() > D->Params.size() ||
        (Actual.size() < D->Params.size() &&
         D->Decl.Params[Actual.size()].Children.empty()))
      continue;
    Candidate Current{D, {}};
    if (!Operator || MemberOperand)
      Current.Ranks.push_back(
          unsigned(D->Decl.Const && !Object.Readonly) +
          unsigned(MemberOperand && Object.Type != D->Owner));
    for (size_t I = 0; I < Actual.size(); ++I) {
      auto Rank = conversionRank(Actual[I], D->Params[I], N.At);
      if (!Rank)
        break;
      Current.Ranks.push_back(*Rank);
    }
    if (Current.Ranks.size() != Args.size() + (Operator ? 0 : 1) ||
        llvm::any_of(Best,
                     [&](const Candidate &C) { return Better(C, Current); }))
      continue;
    llvm::erase_if(Best,
                   [&](const Candidate &C) { return Better(Current, C); });
    Best.push_back(std::move(Current));
  }
  if (Best.size() != 1)
    fail(N.At, Best.empty() ? "no viable overload" : "ambiguous overload");
  auto *Selected = checkSelected(Best.front().Decl, N.At);
  if (Selected->Origin && !Selected->Emitted && !Selected->Emitting) {
    llvm::SaveAndRestore Depth(U.SpecializationDepth,
                               U.SpecializationDepth + 1);
    if (U.SpecializationDepth > 128)
      throw ResourceExhausted{
          {N.At, "generic specialization nesting resource exhausted"}};
    EnterDefinition Site(U, Selected->Definition);
    U.emit(*Selected);
  }
  return Selected;
}
Value Frame::applyOperator(const std::string &Name, const Token &At,
                           CallArguments A) {
  Node Callee(Node::Name, At);
  Callee.At.Text = Callee.Text = Name;
  auto *D = select(Name, Callee, A.Values, {}, true);
  Value Receiver;
  bool Staged = !A.Exits.empty();
  if (!D->Owner.empty()) {
    Receiver = A.Values.front();
    A.Values.erase(A.Values.begin());
    if (Staged) {
      B.SetInsertPoint(A.Exits.front());
      A.Entries.erase(A.Entries.begin());
      A.Exits.erase(A.Exits.begin());
    }
    adjust(Receiver, D->Owner, At);
    if (Staged && !A.Entries.empty())
      branch(A.Entries.front());
  }
  if (Staged)
    admitArguments(A, D, At);
  return invoke(*D, std::move(A.Values), At, Receiver, Staged);
}
Value Frame::bindReference(Value V, const std::string &Ty, const Token &At) {
  if (V.Type == "never")
    return {unconst(baseRef(Ty)), nullptr,
            llvm::PoisonValue::get(B.getPtrTy())};
  if (!conversionRank(V, Ty, At))
    fail(At, "incompatible reference binding");
  auto T = unconst(baseRef(Ty));
  if (V.Type != T && !adjust(V, T, At))
    V = convert(V, T, At);
  if (!V.Address && IR) {
    V.Address = allocate(T, At);
    B.CreateStore(V.IR, V.Address);
  }
  V.Readonly |= T != baseRef(Ty);
  return V;
}
// Bind all argument types before connecting their executable blocks. Each
// argument's parameter initialization then precedes its successor expression.
CallArguments Frame::evaluateArguments(const std::vector<Node> &Args,
                                       Function *Context,
                                       Value SingleDestination) {
  CallArguments A;
  for (size_t I = 0; I < Args.size(); ++I) {
    if (IR) {
      if (I)
        B.SetInsertPoint(block("argument"));
      A.Entries.push_back(B.GetInsertBlock());
    }
    auto Expected =
        Context && I < Context->Params.size() ? Context->Params[I] : "";
    if (Args.size() == 1 && SingleDestination.Address)
      A.Values.push_back(
          eval(Args[I], SingleDestination.Type, SingleDestination.Address));
    else
      A.Values.push_back(eval(Args[I], Expected));
    if (IR)
      A.Exits.push_back(B.GetInsertBlock());
  }
  return A;
}
void Frame::admitArguments(CallArguments &A, Function *D, const Token &At) {
  if (!IR)
    return;
  for (size_t I = 0; I < A.Values.size(); ++I) {
    B.SetInsertPoint(A.Exits[I]);
    if (D) {
      auto &Ty = D->Params[I];
      auto &V = A.Values[I];
      V = ends(Ty, "&") ? bindReference(V, Ty, At)
                        : materialize(convert(V, Ty, At), At);
    }
    if (I + 1 < A.Entries.size())
      branch(A.Entries[I + 1]);
  }
}
Value Frame::invoke(Function &D, std::vector<Value> Actual, const Token &T,
                    Value Receiver, bool Prepared) {
  requireObserver(D.Effects, T, &D);
  if (F && IR && !TypeQuery)
    F->Calls.insert(&D);
  if (RequireNoexcept && !D.Decl.Noexcept)
    fail(T, "expression requires a nonthrowing call");
  if (TypeQuery && D.Decl.Settings.count("mode")) {
    if (D.Result == "void" || D.Result == "never")
      return {D.Result};
    auto Base = unconst(baseRef(D.Result));
    Value V{Base, llvm::PoisonValue::get(U.ir(Base, T))};
    V.Prvalue = !ends(D.Result, "&");
    V.Expiring = V.Prvalue || ends(D.Result, "&&");
    V.Readonly = baseRef(D.Result) != Base;
    if (!V.Prvalue)
      V.Address = llvm::PoisonValue::get(B.getPtrTy());
    return V;
  }
  if (!IR || D.Decl.Settings.count("mode")) {
    ConstantActivation Activation(U, T);
    auto StaticReceiver = Receiver;
    auto &Target =
        !IR && D.Slot >= 0 ? constantVirtualTarget(D, Receiver, T) : D;
    if (!Target.Decl.Required || Target.Decl.Prototype)
      fail(T, "constant expression requires a constexpr function");
    Frame CF(U, &Target, nullptr);
    if (!Target.Owner.empty() && !Target.isStatic()) {
      if (!llvm::isa_and_nonnull<llvm::Constant>(Receiver.IR))
        fail(T, "constant receiver required");
      Receiver.Readonly |= Target.Decl.Const;
      CF.ConstantReceiver = &Receiver;
    }
    CF.bindInlineParams(
        Actual, &D, StaticReceiver.Type.empty() ? nullptr : &StaticReceiver);
    bool Closure = Target.Decl.Settings.count("closure");
    if (Closure)
      CF.bindCaptures();
    auto Retire = [&] {
      if (Closure)
        CF.Scopes.pop_back();
      CF.endConstantScope();
      CF.checkMethodInvariant(false);
    };
    CF.checkMethodInvariant(true);
    CF.checkContracts(true);
    try {
      CF.stmt(Target.Decl.Children.front());
    } catch (const ConstantTransfer &R) {
      if (R.Kind != Node::Return)
        throw;
      CF.checkContracts(false, R.Result);
      Retire();
      return R.Result;
    }
    if (Target.Result == "void") {
      CF.checkContracts(false);
      Retire();
      return {"void"};
    }
    fail(T, "constant invocation completed without a result");
  }
  std::vector<llvm::Value *> Values;
  auto *ResultStorage = resultAddress(D.Result, T);
  if (ResultStorage)
    Values.push_back(ResultStorage);
  if (!D.Owner.empty() && !D.isStatic())
    Values.push_back(Receiver.Address);
  auto Original = std::move(Scopes);
  auto OldPrefix = Prefix;
  Scopes = {Local{}};
  Prefix = D.DefaultPrefix;
  bool Defaults = Actual.size() < D.Params.size();
  std::vector<Value> Cells;
  for (size_t I = 0; I < D.Params.size(); ++I) {
    auto &P = D.DefaultParams[I];
    auto Ty = D.Params[I];
    Value V;
    if (I < Actual.size())
      V = Actual[I];
    else {
      llvm::SaveAndRestore Policy(Opt, D.Defaults.Configuration);
      llvm::SaveAndRestore Lookup(LookupLimit, D.Defaults.Through);
      llvm::SaveAndRestore Bindings(Env, D.DefaultEnv);
      V = construct(unconst(baseRef(Ty)), P.Children, P.At);
    }
    if (!Prepared || I >= Actual.size())
      V = ends(Ty, "&") ? bindReference(V, Ty, P.At)
                        : materialize(convert(V, Ty, T), T);
    if (!ends(Ty, "&") && !U.aggregate(Ty) && Defaults) {
      auto *Addr = allocate(Ty, P.At);
      B.CreateStore(V.IR, Addr);
      V.Address = Addr;
      V.IR = nullptr;
      if (carriesPointerBounds(Ty)) {
        V.BoundsCell = B.CreateAlloca(pointerMetadataType());
        saveBounds(V.BoundsCell, V);
      }
    }
    Cells.push_back(V);
    if (!P.Text.empty())
      Scopes.back().Names[P.Text] = V;
  }
  for (size_t I = 0; I < Cells.size(); ++I) {
    auto &P = D.DefaultParams[I];
    auto V =
        Defaults && !P.Text.empty() ? Scopes.back().Names.at(P.Text) : Cells[I];
    if (Defaults && carriesPointerBounds(D.Params[I]))
      Cells[I] = load(V);
    Values.push_back((ends(D.Params[I], "&") || U.aggregate(D.Params[I]))
                         ? V.Address
                         : load(V).IR);
  }
  Scopes = std::move(Original);
  Prefix = std::move(OldPrefix);
  if (!D.Owner.empty() && D.Decl.K == Node::Function && !D.isStatic()) {
    if (Transaction && Receiver.Address == Self.Address) {
      if (auto *Hooks = Transaction->admitCall(*this, D, T))
        Values.push_back(Hooks);
    } else if (!D.Initializes.empty()) {
      if (!TypeQuery)
        fail(T, "LIFE001: initializes requires Pending receiver slots");
      Values.push_back(llvm::PoisonValue::get(B.getPtrTy()));
    }
  }
  auto *Before = wholeEpoch();
  llvm::Value *Target =
      Receiver.BaseView && D.BaseIR ? D.BaseIR : U.foreignContractEntry(D);
  if (D.Slot >= 0) {
    auto &R = U.Records.at(D.Owner);
    auto *Vptr = B.CreateStructGEP(R.IR, Receiver.Address, R.Fields.size());
    auto *Table = B.CreateLoad(B.getPtrTy(), Vptr);
    auto *Slot = B.CreateGEP(B.getPtrTy(), Table, B.getInt32(D.Slot));
    auto *Deltas =
        B.CreateStructGEP(R.IR, Receiver.Address, R.Fields.size() + 1);
    auto *Delta =
        B.CreateLoad(B.getInt64Ty(),
                     B.CreateGEP(B.getInt64Ty(), Deltas, B.getInt64(D.Slot)));
    Values[ResultStorage ? 1 : 0] =
        B.CreateGEP(B.getInt8Ty(), Receiver.Address, Delta);
    Target = B.CreateLoad(B.getPtrTy(), Slot);
  }
  auto Metadata = openPointerCall(Target, D.Result, D.Params, Cells);
  auto *Call = B.CreateCall(D.IR->getFunctionType(), Target, Values);
  unsigned ABIHeaders =
      (ResultStorage != nullptr) + (!D.Owner.empty() && !D.isStatic());
  bool MayWriteCallStorage =
      ResultStorage || D.MayWhole || !D.Consumes.empty() ||
      llvm::any_of(D.Params,
                   [&](const auto &Type) { return U.aggregate(Type); });
  describeBorrowCall(*Call, T, Opt, D.Params, ABIHeaders, D.NoEscape,
                     D.BorrowedResult, D.Effects, MayWriteCallStorage);
  if (D.Slot >= 0)
    describeEffectCall(*Call, D.Effects, ResultStorage ? 1 : 0, true, D.IR);
  Call->setAttributes(D.IR->getAttributes());
  Call->setCallingConv(D.IR->getCallingConv());
  if (D.Result == "never")
    return endDivergentCall();
  closePointerCall(Metadata);
  propagateWhole(Before);
  // A helper can end or replace an extent reached through its receiver or
  // a borrowed argument. Its live state is subsequently checked at runtime.
  if (!Receiver.Storage.empty() && Active.count(Receiver.Storage))
    Active[Receiver.Storage] = -1;
  for (size_t I = 0; I < Actual.size(); ++I)
    if (ends(D.Params[I], "&") || ends(D.Params[I], "*")) {
      const auto &Argument = Actual[I];
      const auto &Storage = ends(D.Params[I], "&") && Argument.PointerCell
                                ? Argument.PointerCell->Storage
                                : Argument.Storage;
      if (Active.count(Storage))
        Active[Storage] = -1;
    }
  auto Returned = callResult(D.Result, Call, T, ResultStorage);
  if (D.BorrowedResult.size() == 1) {
    auto Index = *D.BorrowedResult.begin();
    if (Index < Actual.size()) {
      Returned.Origins = Actual[Index].Origins;
      Returned.Storage = Actual[Index].Storage;
    }
  } else
    for (auto I : D.BorrowedResult)
      if (I < Actual.size())
        Returned.Origins.insert(Actual[I].Origins.begin(),
                                Actual[I].Origins.end());
  return pointerCallResult(Returned, Metadata, D.Result);
}
// Resolve the declaration using the normal overload rules before any argument
// is executed. Native type probes retain literal values and give local objects
// private storage so increments, calls and assignments have their real types.
Function *Frame::constantOverload(const std::string &Name, const Node &C,
                                  const std::vector<Node> &Args, Value Receiver,
                                  Function *Hint) {
  if (Args.empty())
    return select(Name, C, {}, Receiver);
  auto *Tmp = llvm::Function::Create(
      llvm::FunctionType::get(B.getVoidTy(), false),
      llvm::GlobalValue::InternalLinkage, "cpn.constant.arguments", U.M);
  struct Discard {
    llvm::Function *F;
    ~Discard() { F->eraseFromParent(); }
  } Guard{Tmp};
  Function Owner;
  if (F)
    Owner = *F;
  Frame Probe(U, F ? &Owner : nullptr, Tmp, Prefix);
  Probe.TypeQuery = true;
  Probe.Env = Env;
  Probe.Opt = Opt;
  Probe.LookupLimit = LookupLimit;
  Probe.B.SetInsertPoint(Probe.block("entry"));
  Probe.Scopes = Scopes;
  for (auto &Scope : Probe.Scopes)
    for (auto &[Key, V] : Scope.Names) {
      if (V.Type.empty() || V.Type == "integer" || V.Type == "real" ||
          !U.ir(V.Type, C.At)->isSized())
        continue;
      if (!llvm::isa_and_nonnull<llvm::GlobalVariable>(V.Address))
        V.Address = Probe.allocate(V.Type, C.At);
      V.Location.reset();
      if (!V.Readonly)
        V.IR = nullptr;
    }
  if (ConstantReceiver) {
    Probe.Self = {ConstantReceiver->Type, nullptr,
                  Probe.allocate(ConstantReceiver->Type, C.At),
                  ConstantReceiver->Readonly};
    Probe.Scopes.front().Names["this"] = {(Probe.Self.Readonly
                                               ? qualifyConst(Probe.Self.Type)
                                               : Probe.Self.Type) +
                                              "*",
                                          Probe.Self.Address};
  }
  auto Shapes = Probe.evaluateArguments(Args, Hint);
  return select(Name, C, Shapes.Values, Receiver);
}

Value Frame::constantCall(Function &D, const std::vector<Node> &Args,
                          const Token &At, Value Receiver) {
  std::vector<Value> Actual;
  for (size_t I = 0; I < Args.size(); ++I) {
    const auto &Ty = D.Params[I];
    auto V = eval(Args[I], Ty);
    if (ends(Ty, "&"))
      V = bindReference(V, Ty, Args[I].At);
    else {
      V = materialize(convert(V, Ty, Args[I].At), Args[I].At);
      V.Prvalue = V.Expiring = true;
    }
    Actual.push_back(V);
  }
  return invoke(D, std::move(Actual), At, Receiver, true);
}

Value Frame::call(const Node &C, const std::vector<Node> &Args,
                  Value Receiver) {
  if (C.K != Node::Name && C.K != Node::Member &&
      !(C.K == Node::Unary && C.Text == "*")) {
    auto Callee = eval(C);
    if (ends(Callee.Type, "*") && U.Signatures.count(element(Callee.Type)))
      return indirect(Callee, Args, C.At);
    return callClosure(Callee, Args, C.At);
  }
  if (C.K == Node::Unary && C.Text == "*" && C.Children.size() == 1)
    return indirect(eval(C.Children[0]), Args, C.At);
  if (C.K == Node::Name) {
    for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
      if (I->UnavailableNames.count(C.Text))
        fail(C.At,
             "unknown callable '" + C.Text +
                 "' in static initializer: automatic object is unavailable");
      if (I->Aliases.count(C.Text))
        break;
      auto V = I->Names.find(C.Text);
      if (V != I->Names.end() && U.Records.count(V->second.Type))
        return callClosure(IR ? V->second : eval(C), Args, C.At);
      if (V != I->Names.end() && ends(V->second.Type, "*") &&
          U.Signatures.count(element(V->second.Type)))
        return indirect(load(V->second), Args, C.At);
      if (V != I->Names.end())
        fail(C.At, "object is not callable");
    }
  }
  if (C.K == Node::Name && !typeCallee(C.Text, C.At) &&
      methodOwner(ConstantReceiver ? ConstantReceiver->Type : Self.Type, C.At)
          .empty()) {
    auto Key = scopeKey(Prefix, C.Text,
                        [&](const auto &K) { return U.Globals.count(K); });
    if (!Key.empty()) {
      auto V = lookup(C.At);
      if (ends(V.Type, "*") && U.Signatures.count(element(V.Type)))
        return indirect(load(V), Args, C.At);
      if (U.Records.count(V.Type))
        return callClosure(V, Args, C.At);
    }
  }
  if (C.K == Node::Member) {
    if (ConstantReceiver && (!F || !F->Decl.Settings.count("closure")) &&
        C.Definition && C.Children[0].K == Node::Name &&
        C.Children[0].Text == "this")
      Receiver = constantSelf(C.At);
    else {
      Receiver =
          C.Definition || !IR ? eval(C.Children[0]) : place(C.Children[0]);
      if (C.Definition) {
        if (!IR) {
          auto Place = constantPointerPlace(Receiver, C.At);
          Receiver = Place.read(*this, C.At);
          Receiver.Location = std::make_shared<ConstantPlace>(std::move(Place));
        } else {
          Receiver = pointedObject(Receiver, C.At);
          ensureLive(Receiver, C.At);
        }
      }
    }
  } else if (C.K != Node::Name)
    fail(C.At, "callable expression required");
  auto Name = C.Text;
  if (auto Memory = memoryCall(C, Args, Receiver))
    return *Memory;
  if (auto Scalar = scalarConversion(C, Name, Args))
    return *Scalar;
  if (InPredicate &&
      (Name == "destroy" || Name == "abandon" || Name == "construct_at" ||
       Name == "storage_of" || Name == "destroy_base" ||
       Name == "abandon_base" || Name == "transfer_destruction"))
    fail(C.At, "lifecycle operations are unavailable in contract predicates");
  if (const auto *Case = findCase(Name, C.At))
    return variant(*Case, Args, C.At,
                   (Case->Owner == ExpressionDestination.Type ||
                    ExpressionDestination.Type.empty())
                       ? ExpressionDestination.Address
                       : nullptr);
  if (Name == "std::forward" && C.TemplateArgs.size() == 1 &&
      Args.size() == 1) {
    auto Ty = resolve(C.TemplateArgs[0].Type, C.At);
    auto V = eval(Args[0]);
    V.Prvalue = false;
    V.Expiring = !ends(Ty, "&");
    return V;
  }
  if (Name == "std::move" && Args.size() == 1) {
    auto V = eval(Args[0]);
    V.Prvalue = false;
    V.Expiring = true;
    return V;
  }
  if (Name == "transfer_destruction" && Args.size() == 1 &&
      C.TemplateArgs.size() == 1)
    return transferOwner(C, Args.front());
  if ((Name == "destroy_base" || Name == "abandon_base") && Args.size() == 1 &&
      C.TemplateArgs.size() == 1)
    return baseRequest(C, Args.front());
  if ((!FieldFlags.empty() || !ConstantMembersAlive.empty()) &&
      Args.size() == 1 && (Name == "destroy" || Name == "abandon")) {
    auto Slot = directField(Args[0]);
    if (!Slot.empty()) {
      if (IR)
        endField(Slot, C.At, Name == "destroy", true);
      else
        endConstantField(Slot, Name == "destroy", C.At);
      return {"void"};
    }
  }
  if (((Name == "destroy" || Name == "abandon" || Name == "storage_of") &&
       Args.size() == 1) ||
      (Name == "construct_at" && !Args.empty() && C.TemplateArgs.size() == 1)) {
    if (!IR)
      return constantStorageCall(C, Args);
    return storageCall(C, Args);
  }
  if (C.K == Node::Name && typeCallee(Name, C.At)) {
    auto T = resolve(Name, C.At);
    return construct(
        T, Args, C.At,
        (T == ExpressionDestination.Type || ExpressionDestination.Type.empty())
            ? ExpressionDestination.Address
            : nullptr);
  }
  if (C.K == Node::Name) {
    std::string Tail;
    if (auto Owner = memberQualifier(Name, C.At, Tail))
      Name = *Owner + "::" + Tail;
  }
  if (Receiver.Type.empty() && ConstantReceiver &&
      !methodOwner(ConstantReceiver->Type, C.At).empty())
    Receiver = constantSelf(C.At);
  if (Receiver.Type.empty() && !Self.Type.empty() &&
      !methodOwner(Self.Type, C.At).empty())
    Receiver = Self;
  if (!Receiver.Type.empty()) {
    auto Owner = methodOwner(Receiver.Type, C.At);
    if (!Owner.empty() && Owner != Receiver.Type)
      adjust(Receiver, Owner, C.At);
  }
  if (Receiver.Type.empty() && F && F->isStatic())
    if (auto Owner = methodOwner(F->Owner, C.At); !Owner.empty())
      Name = Owner + "::" + Name;
  auto Key = callKey(Name, Receiver.Type);
  auto Group = visibleOverloads(Key);
  if (Receiver.Type.empty() && Group.empty() && !U.FunctionFamilies.count(Key))
    if (auto Numeric = namedInteger(C, Name, Args))
      return *Numeric;
  auto *Hint = Group.size() == 1 && !U.FunctionFamilies.count(Key)
                   ? Group.front()
                   : nullptr;
  if (!IR) {
    auto *D = constantOverload(Name, C, Args, Receiver, Hint);
    return constantCall(*D, Args, C.At, Receiver);
  }
  auto A = evaluateArguments(Args, Hint);
  auto *D = select(Name, C, A.Values, Receiver);
  admitArguments(A, D, C.At);
  return invoke(*D, std::move(A.Values), C.At, Receiver, IR != nullptr);
}
std::string Frame::initSlot(const Node &N) {
  if (StringRef(N.Text).starts_with("base/"))
    return "$base:" + resolve(N.Text.substr(5), N.At);
  if (StringRef(N.Text).starts_with("virtual_base/"))
    return "$virtual:" + resolve(N.Text.substr(13), N.At);
  return N.Text;
}
bool Frame::typeCallee(const std::string &Name, const Token &At) {
  for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
    if (I->Aliases.count(Name))
      return true;
    if (I->Names.count(Name) || I->UnavailableNames.count(Name))
      return false;
  }
  if (builtin(Name) || Env.Types.count(Name))
    return true;
  std::string Tail;
  if (auto Owner = memberQualifier(Name, At, Tail))
    return U.MemberTypes.count(*Owner + "::" + Tail.substr(0, Tail.find('<')));
  auto Base = Name.substr(0, Name.find('<'));
  return !scopeKey(Prefix, Base, [&](const std::string &Key) {
            auto Family = U.Families.find(Key);
            return U.Aliases.count(Key) || U.Records.count(Key) ||
                   (Base != Name && Family != U.Families.end() &&
                    (Family->second.Decl.K == Node::Record ||
                     Family->second.Decl.K == Node::Union));
          }).empty();
}
std::optional<Value> Frame::directConstruction(const Node &Arg,
                                               const std::string &T,
                                               llvm::Value *Dest) {
  if (!U.Records.count(T) || Arg.K != Node::Call ||
      Arg.Children.front().K != Node::Name)
    return {};
  const auto &Callee = Arg.Children.front();
  const auto &Key = Callee.Text;
  for (const auto &Scope : Scopes)
    if (Scope.Names.count(Key))
      return {};
  if (const auto *Case = findCase(Key, Arg.At); Case && Case->Owner == T)
    return variant(*Case, {Arg.Children.begin() + 1, Arg.Children.end()},
                   Arg.At, Dest);
  if (typeCallee(Key, Arg.At) && resolve(Key, Arg.At) == T)
    return construct(T, {Arg.Children.begin() + 1, Arg.Children.end()}, Arg.At,
                     Dest);
  return {};
}
// Bind in the caller's lexical environment. The plan connects the producer
// at its canonical frontier after resolving whole-object versus member input.
Initializer Frame::deferInitializer(const Node &Arg,
                                    const std::string &Expected) {
  llvm::IRBuilderBase::InsertPointGuard Save(B);
  auto *Entry = block("initializer");
  B.SetInsertPoint(Entry);
  auto *Storage = B.CreateAlloca(B.getInt8Ty());
  auto Result = eval(Arg, Expected, Storage);
  return {Result, Entry, B.GetInsertBlock(), Storage};
}

Value Frame::runInitializer(Initializer &Init, Value Target, const Token &At) {
  auto V = Init.Result;
  if (!Init.Storage->use_empty() || V.Address == Init.Storage) {
    auto *Address =
        V.Type == Target.Type ? Target.Address : allocate(V.Type, At);
    Init.Storage->replaceAllUsesWith(Address);
    if (V.Address == Init.Storage) {
      V.Address = Address;
      if (V.Prvalue && U.aggregate(V.Type) && Address != Target.Address)
        Temps.push_back(V);
    }
  }
  Init.Storage->eraseFromParent();
  branch(Init.Entry);
  B.SetInsertPoint(Init.Exit);
  return V;
}

void Frame::runConstructionTail(Value Object, const Node *Tail,
                                bool BoundSlots) {
  if (!Tail)
    return;
  llvm::SaveAndRestore Receiver(Self, Object);
  llvm::SaveAndRestore<Construction *> OuterTransaction(Transaction, nullptr);
  Scopes.emplace_back();
  Scopes.back().Names["this"] = {Object.Type + "*", Object.Address};
  const bool HasSubobjects = U.aggregate(Object.Type);
  if (HasSubobjects) {
    // The tail executes after subobject completion and before the containing
    // object's lifetime begins. A transfer out retires the completed parts.
    Object.Rollback = true;
    Object.DeclaredAt = {Tail->At.Line, Tail->At.Column};
    Scopes.back().Drops.push_back(Object);
  }
  for (const auto &S : Tail->Children) {
    if (S.K == Node::Init) {
      if (!BoundSlots)
        fail(S.At, "unknown initialization target");
    } else
      stmt(S);
  }
  if (Live) {
    if (HasSubobjects)
      Scopes.back().Drops.erase(Scopes.back().Drops.begin());
    cleanup(Scopes.size() - 1);
  }
  Scopes.pop_back();
}

Value Frame::construct(const std::string &T, const std::vector<Node> &Args,
                       const Token &At, llvm::Value *Dest, const Node *Tail,
                       bool AsBase) {
  if (InPredicate && U.aggregate(T))
    fail(At, "contract predicates cannot construct aggregate temporaries");
  if ((T == StorageViewType || memoryIdentity(T)) && Args.empty())
    fail(At, "memory capability requires an authorized source");
  if (!Args.empty() && Args.back().K == Node::Tail)
    return construct(T, {Args.begin(), Args.end() - 1}, At, Dest, &Args.back(),
                     AsBase);
  if (auto Mutable = unconst(T); Mutable != T) {
    auto V = construct(Mutable, Args, At, Dest, Tail, AsBase);
    V.Readonly = true;
    return V;
  }
  if (T == "void" || T == "never")
    fail(At, "object cannot have " + T + " type");
  if (floating(T)) {
    if (Args.size() > 1)
      fail(At, "invalid scalar construction");
    Value V = Args.empty() ? Value{T, llvm::ConstantFP::get(U.ir(T), 0.0)}
                           : floatingConvert(eval(Args[0], T), T, At, true);
    if (Dest)
      B.CreateStore(V.IR, Dest);
    runConstructionTail({T, nullptr, Dest}, Tail);
    return V;
  }
  auto *Ty = U.ir(T, At);
  if (!Ty->isSized())
    fail(At, "construction requires a complete object type");
  if (!IR && U.aggregate(T))
    return constantAggregate(T, Args, At, Tail);
  if (ends(T, "]")) {
    auto *Ptr = Dest ? Dest : allocate(T, At);
    auto *Array = llvm::cast<llvm::ArrayType>(Ty);
    auto Count = ends(T, "[0]") ? 0 : Array->getNumElements();
    auto E = element(T);
    std::optional<Initializer> First;
    if (Args.size() == 1) {
      First = deferInitializer(
          Args.front(),
          Args.front().K == Node::Unary && Args.front().Text == "&" ? E : "");
      if (First->Result.Type == T) {
        materialize(runInitializer(*First, {T, nullptr, Ptr}, At), At, Ptr);
        Value V{T, nullptr, Ptr};
        V.Prvalue = V.Expiring = !Dest;
        if (!Dest)
          Temps.push_back(V);
        return V;
      }
    }
    if (Args.size() > Count)
      fail(At, "too many array initializers");
    for (size_t I = 0; I < Args.size(); ++I) {
      auto *P = B.CreateInBoundsGEP(Ty, Ptr, {B.getInt32(0), B.getInt64(I)});
      if (!First) {
        construct(E, {Args[I]}, At, P);
        continue;
      }
      auto V = runInitializer(*First, {E, nullptr, P}, At);
      if (V.Type == E)
        materialize(V, At, P);
      else {
        Node Ref(Node::Name, At);
        Ref.At.Text = Ref.Text = "$array.initializer";
        Scopes.emplace_back();
        Scopes.back().Names[Ref.Text] = V;
        construct(E, {Ref}, At, P);
        Scopes.pop_back();
      }
    }
    if (Args.size() < Count) {
      // Generate the recursive default producer once, even for large extents.
      auto *Entry = B.GetInsertBlock(), *Loop = block("array.init"),
           *End = block("array.ready");
      branch(Loop);
      B.SetInsertPoint(Loop);
      auto *Index = B.CreatePHI(B.getInt64Ty(), 2);
      Index->addIncoming(B.getInt64(Args.size()), Entry);
      auto *P = B.CreateInBoundsGEP(Ty, Ptr, {B.getInt32(0), Index});
      size_t Mark = Temps.size();
      construct(E, {}, At, P);
      endExpression(Mark);
      auto *Next = B.CreateAdd(Index, B.getInt64(1));
      Index->addIncoming(Next, B.GetInsertBlock());
      B.CreateCondBr(B.CreateICmpULT(Next, B.getInt64(Count)), Loop, End);
      B.SetInsertPoint(End);
    }
    Value V{T, nullptr, Ptr};
    runConstructionTail(V, Tail);
    V.Prvalue = V.Expiring = !Dest;
    if (!Dest)
      Temps.push_back(V);
    return V;
  }
  if (Args.size() == 1 && !Tail && !AsBase)
    if (auto Direct = directConstruction(Args[0], T, Dest))
      return *Direct;
  if (U.Variants.count(T)) {
    if (!IR)
      fail(At, "union construction requires object storage");
    auto *Ptr = Dest ? Dest : allocate(T, At);
    Value Result{T, nullptr, Ptr};
    auto *Previous = pushInvariantLifetime(Result, Tail);
    auto Group = visibleOverloads(T + "::$ctor");
    auto A = evaluateArguments(
        Args, Group.size() == 1 ? Group.front() : nullptr, {T, nullptr, Ptr});
    if (A.Values.size() == 1 && A.Values[0].Type == T) {
      materialize(A.Values.front(), At, Ptr, false);
    } else if (Args.empty() &&
               !llvm::any_of(Group,
                             [](const Function *D) {
                               return D->Params.empty() ||
                                      !D->Decl.Params.front().Children.empty();
                             }) &&
               U.DefaultCase.count(T)) {
      variant(U.Cases.at(U.DefaultCase.at(T)), {}, At, Ptr, true, false);
    } else {
      if (Group.empty())
        fail(At, "union construction requires a selected case");
      Value Receiver{T, nullptr, Ptr};
      auto *D = select("$ctor", Node(Node::Name, At), A.Values, Receiver);
      admitArguments(A, D, At);
      invoke(*D, std::move(A.Values), At, Receiver, true);
    }
    runConstructionTail(Result, Tail);
    popInvariantLifetime(Previous);
    checkInvariants(Result);
    Result.IR = B.CreateLoad(Ty, Ptr);
    if (!Dest) {
      Result.Prvalue = Result.Expiring = true;
      Temps.push_back(Result);
    }
    return Result;
  }
  if (U.Records.count(T)) {
    auto *Ptr = Dest ? Dest : allocate(T, At);
    Value Obj{T, nullptr, Ptr};
    auto &R = U.Records.at(T);
    Obj.BaseView = AsBase;
    auto *Previous = pushInvariantLifetime(Obj, Tail);
    if (!AsBase)
      bindVirtualLayout(Obj);
    enterOwnerLayer(Obj);
    auto It = U.Overloads.find(T + "::$ctor");
    std::vector<Initializer> Inputs;
    std::vector<Value> Actual;
    for (size_t I = 0; I < Args.size(); ++I) {
      std::string Expected;
      if (Args[I].K == Node::Unary && Args[I].Text == "&") {
        if (It != U.Overloads.end() && It->second.size() == 1 &&
            I < It->second.front()->Params.size())
          Expected = It->second.front()->Params[I];
        else if (I + R.Bases.size() < R.Fields.size())
          Expected = R.Fields[I + R.Bases.size()].Type;
      }
      Inputs.push_back(deferInitializer(Args[I], Expected));
      Actual.push_back(Inputs.back().Result);
    }
    std::map<std::string, const Node *> Producers;
    if (Tail)
      for (auto &S : Tail->Children)
        if (S.K == Node::Init && !Producers.emplace(initSlot(S), &S).second)
          fail(S.At, "duplicate initialization producer");
    if (Actual.size() == 1 && Actual[0].Type == T) {
      // An embedded layer shares virtual bases with its complete object.
      auto Target = AsBase && R.VirtualCount ? Value{} : Obj;
      Actual[0] = runInitializer(Inputs.front(), Target, At);
      if (AsBase && R.VirtualCount)
        transfer(Actual[0], Ptr,
                 Actual[0].Expiring ? SpecialOperation::MoveConstruct
                                    : SpecialOperation::CopyConstruct,
                 At, true, false);
      else
        materialize(Actual[0], At, Ptr, false);
    } else {
      Function Aggregate;
      Aggregate.Owner = T;
      Aggregate.Decl = Node(Node::Constructor, At);
      bool Fits = Args.size() <= R.Fields.size() - R.Bases.size();
      if (Fits)
        for (size_t I = 0; I < Args.size(); ++I)
          Aggregate.Params.push_back(R.Fields[R.Bases.size() + I].Type);
      auto *D = &Aggregate;
      if (It != U.Overloads.end()) {
        Node C(Node::Name, At);
        D = select("$ctor", C, Actual, Obj, false, Fits ? &Aggregate : nullptr);
      }
      if (D != &Aggregate) {
        for (size_t I = 0; I < Inputs.size(); ++I) {
          auto Source = runInitializer(Inputs[I], {}, At);
          const auto &Type = D->Params[I];
          Actual[I] = ends(Type, "&")
                          ? bindReference(Source, Type, At)
                          : materialize(convert(Source, Type, At), At);
        }
        if (Producers.empty())
          invoke(*D, Actual, At, Obj, true);
        else {
          Frame Root(U, D, IR);
          Root.B.SetInsertPoint(B.GetInsertBlock());
          Root.BaseLayer = AsBase;
          Root.Self = Obj;
          Root.Scopes[0].Names["this"] = {T + "*", Ptr};
          Root.bindInlineParams(Actual);
          Root.checkContracts(true);
          Root.InlineReturn = block("ctor.done");
          Construction Plan(Root, *D, Obj, Tail, this);
          Plan.run(Root);
          if (Root.Live) {
            Root.checkContracts(false);
            Root.cleanup(0);
          }
          Root.branch(Root.InlineReturn);
          B.SetInsertPoint(Root.InlineReturn);
          Producers.clear();
        }
      } else {
        if (Actual.size() + R.Bases.size() > R.Fields.size())
          fail(At, "too many aggregate initializers");
        if (R.Bases.size() == (AsBase ? R.VirtualCount : 0))
          installTables(Obj);
        auto *SavedObject = PendingObject;
        auto SavedSlots = std::move(PendingSlots);
        PendingSlots.clear();
        PendingObject = Ptr;
        for (auto &Field : R.Fields)
          PendingSlots.insert(Field.Decl.Text);
        Scopes.emplace_back();
        Scopes.back().Names["this"] = {T + "*", Ptr};
        for (auto &Field : R.Fields)
          Scopes.back().Names[Field.Decl.Text] = {};
        for (size_t I = AsBase ? R.VirtualCount : 0; I < R.Fields.size(); ++I) {
          auto &Field = R.Fields[I];
          auto *P = fieldAddress(Obj, I);
          auto Found = Producers.find(Field.Decl.Text);
          if (I >= R.Bases.size() && I - R.Bases.size() < Actual.size()) {
            if (Found != Producers.end())
              fail(At, "duplicate aggregate initialization producer");
            auto V = runInitializer(Inputs[I - R.Bases.size()],
                                    {Field.Type, nullptr, P}, At);
            materialize(convert(V, Field.Type, At), At, P);
          } else {
            llvm::SaveAndRestore Policy(Opt);
            llvm::SaveAndRestore Limit(LookupLimit);
            if (Found == Producers.end() && Field.DefaultSite) {
              Opt = Field.DefaultSite->Configuration;
              LookupLimit = Field.DefaultSite->Through;
            }
            construct(Field.Type,
                      Found == Producers.end() ? Field.Decl.Children
                                               : Found->second->Children,
                      At, P, nullptr, I < R.Bases.size());
            if (Found != Producers.end())
              Producers.erase(Found);
          }
          finishVirtualBase(Obj, I);
          PendingSlots.erase(Field.Decl.Text);
          Scopes.back().Names[Field.Decl.Text] = {Field.Type, nullptr, P};
          if (I + 1 == R.Bases.size())
            installTables(Obj);
        }
        Scopes.pop_back();
        PendingObject = SavedObject;
        PendingSlots = std::move(SavedSlots);
      }
    }
    if (!Producers.empty())
      fail(At, "unknown initialization target");
    runConstructionTail(Obj, Tail, true);
    popInvariantLifetime(Previous);
    checkInvariants(Obj);
    if (!Dest)
      Temps.push_back(Obj);
    if (!AsBase)
      Obj.IR = B.CreateLoad(Ty, Ptr);
    Obj.Expiring = Obj.Prvalue = !Dest;
    return Obj;
  }
  if (Args.empty() && U.Enums.count(T) &&
      llvm::none_of(U.Globals, [&](const auto &G) {
        return G.second.Type == T &&
               llvm::isa_and_nonnull<llvm::ConstantInt>(G.second.IR) &&
               llvm::cast<llvm::ConstantInt>(G.second.IR)->isZero();
      }))
    fail(At, "enum has no zero-valued default");
  if (Args.size() > 1)
    fail(At, "invalid scalar construction");
  Value V{T, llvm::Constant::getNullValue(Ty)};
  if (!Args.empty()) {
    auto Source = eval(Args[0], T);
    if (ends(T, "*") && U.Signatures.count(element(T)) &&
        U.Records.count(Source.Type) &&
        U.Records.at(Source.Type).Decl.K == Node::Lambda)
      V = closurePointer(Source, T, At);
    else
      V = convert(Source, T, At);
  }
  if (Dest) {
    if (carriesPointerBounds(T))
      saveBounds(storedPointerCell(Dest), V);
    B.CreateStore(V.IR, Dest);
  }
  runConstructionTail({T, nullptr, Dest}, Tail);
  return V;
}
void Frame::drop(Value V, bool AsBase) {
  if (!IR || !V.Address)
    return;
  V = V.objectDesignation();
  requirePredicateCleanup(V.Type, F ? F->Decl.At : Token{});
  if (V.Rollback) {
    dropLayer(V, V.BaseView, true);
    return;
  }
  if (!V.Storage.empty() && Extents.count(V.Storage) &&
      Extents.at(V.Storage).Address == V.Address &&
      Registrations.count(V.Storage)) {
    retireStorage(V, true);
    return;
  }
  if (!V.Storage.empty() && Active.count(V.Storage) && !Active[V.Storage])
    return;
  if (U.Whole && !AsBase && U.Records.count(V.Type) &&
      !U.Records.at(V.Type).Views.empty()) {
    B.CreateCall(U.coordinator(V.Type), {V.Address});
    return;
  }
  dropLayer(V, AsBase);
}
void Frame::dropLayer(Value V, bool AsBase, bool Rollback) {
  if (ends(V.Type, "]")) {
    auto E = unconst(element(V.Type));
    if (ends(V.Type, "[0]") ||
        (!TracksStorage && !U.Records.count(E) && !ends(E, "]")))
      return;
    auto *Ty = llvm::cast<llvm::ArrayType>(U.ir(V.Type));
    auto *Entry = B.GetInsertBlock(), *Loop = block("array.drop"),
         *Done = block("array.end");
    branch(Loop);
    B.SetInsertPoint(Loop);
    auto *Count = B.CreatePHI(B.getInt64Ty(), 2);
    Count->addIncoming(B.getInt64(Ty->getNumElements()), Entry);
    auto *Index = B.CreateSub(Count, B.getInt64(1));
    auto *Ptr = B.CreateInBoundsGEP(Ty, V.Address, {B.getInt32(0), Index});
    dropChild(V, {E, nullptr, Ptr});
    Count->addIncoming(Index, B.GetInsertBlock());
    B.CreateCondBr(B.CreateIsNotNull(Index), Loop, Done);
    B.SetInsertPoint(Done);
    return;
  }
  if (!U.Records.count(V.Type))
    return;
  if (auto It = U.Overloads.find(V.Type + "::$drop");
      !Rollback && It != U.Overloads.end()) {
    auto *D = It->second.front();
    B.CreateCall(AsBase && D->BaseIR ? D->BaseIR : D->IR, {V.Address});
    return;
  }
  auto &R = U.Records.at(V.Type);
  if (R.Decl.K == Node::Union) {
    dropPayload(V);
    return;
  }
  installTables(V);
  for (size_t I = R.Fields.size(); I > (AsBase ? R.VirtualCount : 0); --I) {
    auto &F = R.Fields[I - 1];
    Value Child{F.Type, nullptr, fieldAddress(V, I - 1)};
    bool Base = I - 1 < R.Bases.size();
    if (Rollback && Base)
      dropLayer(Child, true);
    else
      dropChild(V, Child, Base);
  }
}
void Frame::cleanup(size_t From, const std::set<SourcePosition> *Exited) {
  for (size_t I = Scopes.size(); I > From; --I)
    cleanupScope(I - 1, Exited);
}
void Frame::cleanupScope(size_t I, const std::set<SourcePosition> *Exited) {
  for (const auto &Drop : llvm::reverse(Scopes[I].Drops)) {
    if (Exited && !Exited->count(Drop.DeclaredAt))
      continue;
    auto V = Drop.objectDesignation();
    drop(V);
    if (V.Slot && !V.Subobject && Extents.count(V.Storage) &&
        Extents.at(V.Storage).Address == V.Address)
      B.CreateCall(U.M.getFunction("cpn.slot.release"), {V.Slot});
  }
}
void Frame::consume(Value V) {
  if (!IR && V.ConstantTemporary) {
    V.ConstantTemporary->ConstantIdentity.Storage.reset();
    llvm::erase_if(Temps, [&](const Value &T) {
      return T.ConstantTemporary == V.ConstantTemporary;
    });
    return;
  }
  if (V.Address)
    Temps.erase(std::remove_if(Temps.begin(), Temps.end(),
                               [&](auto &T) { return T.Address == V.Address; }),
                Temps.end());
}
void Frame::endExpression(size_t From) {
  while (Temps.size() > From) {
    auto V = Temps.back();
    Temps.pop_back();
    if (!IR && V.ConstantTemporary) {
      constantDrop(*V.ConstantTemporary, F ? F->Decl.At : Token{});
      V.ConstantTemporary->ConstantIdentity.Storage.reset();
      continue;
    }
    if (V.OptionalTemp) {
      auto *Run = block("temporary.drop"), *Done = block("temporary.done");
      B.CreateCondBr(B.CreateIsNotNull(V.Address), Run, Done);
      B.SetInsertPoint(Run);
      drop(V);
      branch(Done);
      B.SetInsertPoint(Done);
    } else
      drop(V);
  }
}
void Frame::object(const Node &N, bool Global) {
  if (!Global && !N.Settings.count("storage") &&
      (N.Settings.count("static_id") || N.Settings.count("init_after") ||
       N.Settings.count("init_cancel") || N.Settings.count("init_effect")))
    fail(N.At, "static initialization metadata requires static storage");
  if (auto Cancel = N.Settings.find("init_cancel");
      Cancel != N.Settings.end() && Cancel->second == "cooperative" &&
      (!N.Settings.count("init_effect") ||
       N.Settings.at("init_effect") == "finish"))
    fail(N.At, "cooperative cancellation requires none or compensate effects");
  std::string Name = Global ? Prefix + N.Text : N.Text;
  if (Global && N.Settings.count("identity"))
    Name = N.Settings.at("identity");
  if (!Global && Scopes.back().Aliases.count(N.Text))
    fail(N.At, "duplicate declaration '" + N.Text + "'");
  if (!Global && N.Settings.count("storage")) {
    if (N.Settings.at("storage") != "static")
      fail(N.At, "thread-local storage is unavailable on this configuration");
    if (!F)
      fail(N.At, "block static requires a function");
    if (Scopes.back().Names.count(N.Text))
      fail(N.At, "duplicate declaration '" + N.Text + "'");
    auto ID = F->Name + ".$static." + std::to_string(N.At.Line) + "." +
              std::to_string(N.At.Column) + "." + N.Text;
    if (!U.Globals.count(ID)) {
      Node D = N;
      D.Settings["identity"] = ID;
      if (auto After = D.Settings.find("init_after");
          After != D.Settings.end()) {
        std::string Bound;
        for (auto Dep : splitArguments(After->second)) {
          if (Dep == N.Text)
            Dep = "::" + ID;
          else
            for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
              if (auto Static = I->StaticNames.find(Dep);
                  Static != I->StaticNames.end()) {
                Dep = "::" + Static->second;
                break;
              }
              if (I->Names.count(Dep) || I->Aliases.count(Dep) ||
                  I->UnavailableNames.count(Dep))
                fail(N.At, "initialization dependency '" + Dep +
                               "' does not name a static object");
            }
          if (!Bound.empty())
            Bound += ",";
          Bound += Dep;
        }
        After->second = std::move(Bound);
      }
      Frame Init(U, nullptr, nullptr, Prefix);
      Init.Env = Env;
      Init.Opt = Opt;
      Init.LookupLimit = LookupLimit;
      Init.Scopes.clear();
      // Eager initialization retains the declaration's lexical bindings
      // without importing storage from the invocation that defined them.
      for (const auto &Scope : Scopes) {
        auto &Visible = Init.Scopes.emplace_back();
        Visible.Aliases = Scope.Aliases;
        Visible.StaticNames = Scope.StaticNames;
        Visible.UnavailableNames = Scope.UnavailableNames;
        for (const auto &[Name, V] : Scope.Names)
          if (Scope.StaticNames.count(Name))
            Visible.Names.emplace(Name, V);
          else
            Visible.UnavailableNames.insert(Name);
      }
      Init.object(D, true);
      U.Statics.push_back({ID, Prefix, std::move(D)});
    }
    auto V = U.Globals.at(ID);
    V.DeclaredAt = {N.At.Line, N.At.Column};
    Scopes.back().Names[N.Text] = std::move(V);
    Scopes.back().StaticNames[N.Text] = ID;
    return;
  }
  auto names = [&]() -> std::map<std::string, Value> & {
    return Global ? U.Globals : Scopes.back().Names;
  };
  auto Found = names().find(Name);
  bool Existing = Found != names().end();
  if (Existing && !(Global && N.Foreign))
    fail(N.At, "duplicate declaration '" + Name + "'");
  auto Declared = resolve(N.Type, N.At);
  if (N.Const && (ends(Declared, "&") || ends(Declared, "]")))
    Declared = qualifyConst(Declared);
  auto Ty = unconst(Declared);
  bool Readonly = N.Const || Declared != Ty;
  std::vector<Node> Args = N.Children;
  const Node *Tail = nullptr;
  if (!Args.empty() && Args.back().K == Node::Tail) {
    Tail = &N.Children.back();
    Args.pop_back();
  }
  if (!Existing) {
    auto &Cell = names()[Name];
    Cell.DeclaredAt = {N.At.Line, N.At.Column};
  }
  if (Global && ends(Ty, "&")) {
    if (N.Foreign)
      fail(N.At, "no C ABI transport for a reference object");
    if (N.Settings.count("storage") &&
        N.Settings.at("storage") == "thread_local")
      fail(N.At, "thread-local storage is unavailable on this configuration");
    staticReference(N, Name, Ty);
    return;
  }
  if (Global) {
    if (N.Settings.count("storage") &&
        N.Settings.at("storage") == "thread_local")
      fail(N.At, "thread-local storage is unavailable on this configuration");
    llvm::GlobalVariable *G = nullptr;
    if (Ty == "auto") {
      Ty = materializationType(constantEval(Args.at(0)).Type, N.At);
    }
    auto *LT = U.ir(Ty, N.At);
    if (!LT->isSized())
      fail(N.At, "static requires a complete type");
    if (N.Foreign) {
      auto Prev = U.ExternalObjects.find(N.Text);
      if (Prev != U.ExternalObjects.end()) {
        G = llvm::cast<llvm::GlobalVariable>(Prev->second.Address);
        if (Prev->second.Type != Ty || Prev->second.Readonly != Readonly ||
            (N.Definition && G->hasInitializer()))
          fail(N.At, "conflicting external object declaration");
      } else if (Existing || U.M.getNamedValue(N.Text))
        fail(N.At, "conflicting external symbol '" + N.Text + "'");
    }
    if (!G)
      G = new llvm::GlobalVariable(
          U.M, LT, false,
          N.Foreign ? llvm::GlobalValue::ExternalLinkage
                    : llvm::GlobalValue::InternalLinkage,
          nullptr, N.Foreign ? N.Text : "cpn.g." + Name);
    if (N.Foreign)
      U.ExternalObjects[N.Text] = {Ty, nullptr, G, Readonly};
    if (N.Foreign && !N.Definition) {
      names()[Name] = {Ty, nullptr, G, Readonly};
      return;
    }
    G->setInitializer(llvm::Constant::getNullValue(LT));
    bool Simple = !Tail && !U.Records.count(Ty) && !ends(Ty, "]") &&
                  (Args.empty() ||
                   (Args.size() == 1 &&
                    (Args[0].K == Node::Number || Args[0].K == Node::Real ||
                     Args[0].K == Node::Character ||
                     (Args[0].K == Node::Name &&
                      (Args[0].Text == "true" || Args[0].Text == "false")))));
    llvm::Value *StaticConstant = nullptr;
    if (N.Required && Tail && !U.Records.count(Ty))
      fail(N.At, "constant construction tail requires a record");
    Simple |= N.Required;
    if (Simple) {
      auto V = construct(Ty, Args, N.At, nullptr, Tail);
      endExpression();
      G->setInitializer(llvm::cast<llvm::Constant>(V.IR));
      // A const source object can still change its hidden dispatch state
      // between active destructor layers.
      G->setConstant(Readonly && !containsDispatchState(Ty));
      StaticConstant = N.Required ? V.IR : nullptr;
      if (N.Required)
        U.ConstantObjects.insert(G);
      Value Bound{Ty, StaticConstant, G, Readonly};
      if (carriesPointerBounds(Ty))
        Bound.borrow(V);
      names()[Name] = Bound;
      if ((!U.SlotType || Readonly) &&
          !(N.Required && (carriesPointerBounds(Ty) || U.aggregate(Ty))))
        return;
    }
    auto FT = llvm::FunctionType::get(B.getVoidTy(), false);
    auto *Fn = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                      "cpn.static.init", U.M);
    Frame Init(U, nullptr, Fn, Prefix);
    Init.Env = Env;
    Init.Opt = Opt;
    Init.LookupLimit = LookupLimit;
    Init.Scopes = Scopes;
    Init.B.SetInsertPoint(Init.block("entry"));
    if (!Simple) {
      Init.construct(Ty, Args, N.At, G, Tail);
      Init.endExpression();
      auto *Ready = new llvm::GlobalVariable(U.M, B.getInt1Ty(), false,
                                             llvm::GlobalValue::InternalLinkage,
                                             B.getFalse(), "cpn.ready");
      U.Ready[G] = Ready;
      U.Initializing[Fn] = G;
      Init.B.CreateStore(B.getTrue(), Ready);
    }
    Value Cell{Ty, StaticConstant, G, Readonly};
    if (N.Required && Simple && containsPointerField(Ty)) {
      // The initializer supplies symbolic bytes at translation. Capture the
      // designated storage generations at startup without writing those bytes.
      auto *Temp = Init.allocate(Ty, N.At);
      Init.construct(Ty, Args, N.At, Temp, Tail);
      Init.copyStoredBounds({Ty, nullptr, Temp}, G);
      Init.endExpression();
    }
    if (N.Required && Simple && carriesPointerBounds(Ty)) {
      auto Bound = names().at(Name);
      Cell.borrow(Bound);
      auto V = Init.construct(Ty, Args, N.At);
      Init.saveBounds(Init.storedPointerCell(G), V);
      Init.endExpression();
    }
    if (U.SlotType && !Readonly) {
      auto *GlobalSlot = new llvm::GlobalVariable(
          U.M, U.SlotType, false, llvm::GlobalValue::InternalLinkage,
          llvm::Constant::getNullValue(U.SlotType), "cpn.static.slot");
      Init.track(Cell, GlobalSlot);
      if (ends(Cell.Type, "*"))
        Cell.rememberPointerCell(Cell);
    }
    Init.B.CreateRetVoid();
    U.Startup.emplace_back(Name, Fn);
    names()[Name] = Cell;
    if (Cell.Slot || U.Records.count(Ty) || ends(Ty, "]")) {
      auto *D = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                       "cpn.static.drop", U.M);
      Frame DF(U, nullptr, D);
      DF.B.SetInsertPoint(DF.block("entry"));
      if (Cell.Slot) {
        DF.retireStorage(Cell, true);
        DF.B.CreateCall(U.M.getFunction("cpn.slot.release"), {Cell.Slot});
      } else
        DF.drop(Cell);
      DF.B.CreateRetVoid();
      U.Shutdown.emplace_back(Name, D);
    }
    return;
  }
  if (ends(Ty, "&")) {
    if (Args.size() != 1)
      fail(N.At, "reference requires one initializer");
    if (N.Required) {
      Frame Check(U, F, nullptr, Prefix);
      Check.Env = Env;
      Check.Opt = Opt;
      Check.LookupLimit = LookupLimit;
      Check.Scopes = Scopes;
      Check.symbolicAddress(Check.place(Args[0]), N.At);
    }
    Value V;
    if (!IR && !N.Required) {
      V = eval(Args.front());
      if (!V.Location && !V.Address)
        fail(N.At, "reference initializer requires a designated object");
    } else
      V = place(Args[0]);
    V = bindReference(V, Ty, N.At);
    V.DeclaredAt = {N.At.Line, N.At.Column};
    names()[Name] = V;
    if (!IR)
      endExpression();
    return;
  }
  if (!IR) {
    auto V = Ty == "auto" ? constantEval(Args.at(0))
                          : construct(Ty, Args, N.At, nullptr, Tail);
    if (Ty == "auto")
      V = materialize(V, N.At);
    if (V.Type == "real")
      V = floatingConvert(V, materializationType(V.Type, N.At), N.At);
    if (V.Type == "integer")
      V = convert(V, materializationType(V.Type, N.At), N.At);
    consume(V);
    V.Readonly = Readonly;
    V.Location.reset();
    V.ConstantTemporary.reset();
    V.Prvalue = V.Expiring = false;
    V.Address = nullptr;
    V.DeclaredAt = {N.At.Line, N.At.Column};
    names()[Name] = V;
    Scopes.back().ConstantDrops.push_back(Name);
    endExpression();
    return;
  }
  Value V;
  llvm::Value *Ptr = nullptr;
  if (N.Required) {
    Frame CF(U, F, nullptr, Prefix);
    CF.Env = Env;
    CF.Opt = Opt;
    CF.LookupLimit = LookupLimit;
    CF.Scopes = Scopes;
    V = Ty == "auto" ? CF.constantEval(Args.at(0))
                     : CF.construct(Ty, Args, N.At, nullptr, Tail);
    if (Ty == "auto")
      Ty = materializationType(V.Type, N.At);
    V = CF.convert(V, Ty, N.At);
    if (carriesPointerBounds(Ty) && !Args.empty()) {
      auto Runtime = convert(eval(Args.front(), Ty), Ty, N.At);
      V.borrow(Runtime);
    }
    Ptr = allocate(Ty, N.At);
    if (containsPointerField(Ty))
      construct(Ty, Args, N.At, Ptr, Tail);
    B.CreateStore(V.IR, Ptr);
  } else if (Ty == "auto") {
    V = eval(Args.at(0));
    Ty = materializationType(V.Type, N.At);
    V = convert(V, Ty, N.At);
    if (V.Prvalue && V.Address) {
      Ptr = V.Address;
      consume(V);
    } else {
      Ptr = allocate(Ty, N.At);
      materialize(V, N.At, Ptr);
    }
  } else {
    Ptr = allocate(Ty, N.At);
    V = construct(Ty, Args, N.At, Ptr, Tail);
  }
  if (N.Required && !llvm::isa_and_nonnull<llvm::Constant>(V.IR))
    fail(N.At, "constexpr initializer requires a constant");
  Value Cell{Ty, N.Required ? V.IR : nullptr, Ptr, Readonly};
  if (Ty == StorageViewType || ends(Ty, "*"))
    Cell.borrow(V);
  if (carriesPointerBounds(Ty)) {
    Cell.BoundsCell = storedPointerCell(Ptr);
    saveBounds(Cell.BoundsCell, V);
  }
  trackLocal(Cell, "local.");
  names()[Name] = Cell;
  Cell.DeclaredAt = {N.At.Line, N.At.Column};
  Scopes.back().Drops.push_back(Cell);
  endExpression();
}
void Frame::constructorBody(const Node &Body) {
  try {
    stmt(Body);
  } catch (const ConstantTransfer &T) {
    if (T.Kind != Node::Return)
      throw;
  }
  if (!IR) {
    if (F->Decl.K != Node::Destructor)
      checkContracts(false);
    endConstantScope();
  }
}
namespace {
const Node *enteredLabel(const Node &N, StringRef Label) {
  if (N.K == Node::Label && N.Text == Label)
    return &N;
  // These constructs have separate execution regions or binding scopes that
  // an incoming goto cannot enter.
  if (N.K == Node::Lambda || N.K == Node::Match || N.K == Node::Tail ||
      N.K == Node::Record || N.K == Node::Union || N.K == Node::Enumeration)
    return nullptr;
  for (const auto &Child : N.Children)
    if (auto *Found = enteredLabel(Child, Label))
      return Found;
  return nullptr;
}

bool isLocalTypeDeclaration(const Node &N) {
  if (N.K == Node::Configured || N.K == Node::Label)
    return isLocalTypeDeclaration(N.Children.front());
  return N.K == Node::Alias || N.K == Node::Record || N.K == Node::Union ||
         N.K == Node::Enumeration;
}
} // namespace

void Frame::rewindConstantScope(const ConstantTransfer &Jump,
                                const Token &Destination) {
  auto &Scope = Scopes.back();
  const auto &Exited =
      F->ExitedLifetimes.Exited.at({Jump.At.Line, Jump.At.Column});
  // Nested scopes have already been retired while unwinding the jump. The
  // remaining departed objects in this scope form a suffix in construction
  // order.
  while (!Scope.ConstantDrops.empty()) {
    auto &V = Scope.Names.at(Scope.ConstantDrops.back());
    if (!Exited.count(V.DeclaredAt))
      break;
    retireConstantCell(V, Jump.At);
    Scope.ConstantDrops.pop_back();
  }
  for (auto I = Scope.Names.begin(); I != Scope.Names.end();) {
    if (Exited.count(I->second.DeclaredAt))
      I = Scope.Names.erase(I);
    else
      ++I;
  }
  SourcePosition To{Destination.Line, Destination.Column};
  for (auto I = Scope.ConstantTypeSites.begin();
       I != Scope.ConstantTypeSites.end();) {
    if (I->second < To) {
      ++I;
      continue;
    }
    Scope.Aliases.erase(I->first);
    Scope.Nominals.erase(I->first);
    I = Scope.ConstantTypeSites.erase(I);
  }
}

void Frame::constantSequence(llvm::ArrayRef<Node> Statements,
                             StringRef EntryLabel) {
  auto Find = [&](StringRef Name) -> std::pair<size_t, const Node *> {
    for (size_t I = 0; I < Statements.size(); ++I)
      if (auto *Target = enteredLabel(Statements[I], Name))
        return {I, Target};
    return {Statements.size(), nullptr};
  };
  auto BindTypes = [&](size_t From, size_t To) {
    for (const auto &Skipped : Statements.slice(From, To - From))
      if (isLocalTypeDeclaration(Skipped))
        stmt(Skipped);
  };

  size_t I = 0;
  std::string Pending = EntryLabel.str();
  if (!Pending.empty()) {
    I = Find(Pending).first;
    BindTypes(0, I);
  }
  while (I < Statements.size()) {
    try {
      stmt(Statements[I], Pending);
      Pending.clear();
      ++I;
    } catch (const ConstantTransfer &Jump) {
      if (Jump.Kind != Node::Goto)
        throw;
      auto [Next, Destination] = Find(Jump.Label);
      if (!Destination)
        throw;
      rewindConstantScope(Jump, Destination->At);
      if (Next > I)
        BindTypes(I + 1, Next);
      Pending = Jump.Label;
      I = Next;
    }
  }
}

void Frame::stmt(const Node &N, StringRef EntryLabel) {
  auto &A = N.Children;
  auto Label = std::move(StatementLabel);
  StatementLabel.clear();
  if (N.K == Node::Block || N.K == Node::Tail) {
    Scopes.emplace_back();
    try {
      if (!IR)
        constantSequence(A, EntryLabel);
      else
        for (auto &S : A)
          stmt(S);
    } catch (const ConstantTransfer &) {
      if (!IR)
        endConstantScope();
      Scopes.pop_back();
      throw;
    }
    if (!IR)
      endConstantScope();
    else if (Live)
      cleanup(Scopes.size() - 1);
    Scopes.pop_back();
    return;
  }
  if (N.K == Node::Init || N.K == Node::Empty)
    return;
  if (N.K == Node::Record || N.K == Node::Enumeration || N.K == Node::Union) {
    localType(N);
    if (!IR)
      Scopes.back().ConstantTypeSites.try_emplace(
          N.Text, SourcePosition{N.At.Line, N.At.Column});
    return;
  }
  if (N.K == Node::Alias) {
    auto &Scope = Scopes.back();
    auto Type = resolve(N.Type, N.At);
    if (Scope.Names.count(N.Text) ||
        !Scope.Aliases.emplace(N.Text, Type).second)
      fail(N.At, "duplicate declaration '" + N.Text + "'");
    if (!IR)
      Scope.ConstantTypeSites.try_emplace(
          N.Text, SourcePosition{N.At.Line, N.At.Column});
    return;
  }
  if (N.K == Node::Object) {
    object(N);
    return;
  }
  if (N.K == Node::Expression) {
    eval(A[0]);
    endExpression();
    return;
  }
  if (N.K == Node::Configured) {
    llvm::SaveAndRestore Policy(Opt);
    configure(Opt, N,
              A[0].K == Node::Block ? ConfigScope::Block
                                    : ConfigScope::Declaration);
    stmt(A[0], EntryLabel);
    return;
  }
  if (!IR && U.ConstantDepth)
    U.chargeConstant(N.At);
  if (N.K == Node::Delegate) {
    if (!Transaction)
      fail(N.At, "delegate requires a constructor");
    Transaction->delegate(*this, N);
    return;
  }
  if (N.K == Node::Return && Transaction && Transaction->needsDelegate(*this))
    fail(N.At, "return bypasses required delegation");
  if (N.K == Node::Return && InlineReturn) {
    if (!A.empty())
      fail(N.At, "constructor cannot return a value");
    cleanup(1);
    checkContracts(false);
    cleanupScope(0);
    exitInvariantConstructionLifetimes();
    branch(InlineReturn);
    B.SetInsertPoint(block("unreachable"));
    Live = false;
    return;
  }
  if (N.K == Node::Return) {
    Value V{"void"};
    auto *Result = IR && F && U.aggregate(F->Result) ? IR->getArg(0) : nullptr;
    if (!A.empty()) {
      const auto &Expr = A.front();
      bool Designation = IR && F && ends(F->Result, "&") &&
                         (Expr.K == Node::Name || Expr.K == Node::Member ||
                          Expr.K == Node::Index ||
                          (Expr.K == Node::Unary && Expr.Text == "*"));
      V = Designation ? place(Expr)
                      : eval(Expr, F ? unconst(F->Result) : "", Result);
    }
    if (!F)
      fail(N.At, "return requires a function");
    if (V.Type == "never")
      return;
    if (F->Result == "never")
      fail(N.At, "never function cannot return normally");
    if (ends(F->Result, "*") || ends(F->Result, "&"))
      for (auto Origin : V.Origins)
        if ((F->NoEscape.count(Origin) || !F->BorrowedResult.empty()) &&
            !F->BorrowedResult.count(Origin))
          fail(N.At,
               "returned borrow violates the declared parameter contract");
    if (ends(F->Result, "*") && !V.Storage.empty() && Extents.count(V.Storage))
      fail(N.At, "borrow of automatic storage escapes the function");
    if (F->Result == "void" && V.Type != "void")
      fail(N.At, "void function cannot return a value");
    if (ends(F->Result, "&") && !IR && V.Location) {
      if (!conversionRank(V, F->Result, N.At) ||
          llvm::any_of(Scopes, [&](const Local &S) {
            return llvm::any_of(S.Names, [&](const auto &P) {
              return &P.second == V.Location->Root;
            });
          }))
        fail(N.At, "invalid reference return or borrow of automatic storage");
      V.Readonly |= baseRef(F->Result) != unconst(baseRef(F->Result));
      V.Expiring = ends(F->Result, "&&");
    } else if (ends(F->Result, "&")) {
      if (!V.Address || !conversionRank(V, F->Result, N.At) ||
          llvm::isa<llvm::AllocaInst>(llvm::getUnderlyingObject(V.Address)))
        fail(N.At, "invalid reference return or borrow of automatic storage");
      auto Base = unconst(baseRef(F->Result));
      if (!adjust(V, Base, N.At))
        fail(N.At, "incompatible reference return");
      if (IR)
        V.IR = V.Address;
    } else if (F->Result != "void") {
      V = convert(V, F->Result, N.At);
      V = materialize(V, N.At, Result);
      if (!IR) {
        V.Location.reset();
        V.Address = nullptr;
        V.Prvalue = V.Expiring = true;
      }
    }
    if (Transaction && Live)
      Transaction->checkReturn(N.At);
    if (!IR) {
      endExpression();
      throw ConstantTransfer{Node::Return, V, {}};
    }
    endExpression();
    cleanup(1);
    checkContracts(false, V);
    cleanupScope(0);
    exitInvariantConstructionLifetimes();
    checkMethodInvariant(false);
    publishPointerResult(V);
    if (V.Type == "void" || Result)
      B.CreateRetVoid();
    else
      B.CreateRet(V.IR);
    B.SetInsertPoint(block("unreachable"));
    Live = false;
    return;
  }
  if (N.K == Node::If) {
    if (!EntryLabel.empty()) {
      size_t Arm = enteredLabel(A[1], EntryLabel) ? 1 : 2;
      if (N.Required) {
        auto C = constantEval(A[0]);
        if (C.Type != "bool")
          fail(N.At, "condition requires bool");
        endExpression();
        if (llvm::cast<llvm::ConstantInt>(C.IR)->isZero() != (Arm == 2))
          fail(N.At, "goto enters a discarded if constexpr branch");
      }
      stmt(A[Arm], EntryLabel);
      return;
    }
    auto C = N.Required ? constantEval(A[0]) : boolean(A[0]);
    if (C.Type != "bool")
      fail(N.At, "condition requires bool");
    endExpression();
    if (N.Required || !IR) {
      auto *K = llvm::dyn_cast<llvm::ConstantInt>(C.IR);
      if (!K)
        fail(N.At, "constant expression required");
      if (!K->isZero())
        stmt(A[1]);
      else if (A.size() > 2)
        stmt(A[2]);
      return;
    }
    bool Before = Live;
    auto *Known = llvm::dyn_cast<llvm::ConstantInt>(C.IR);
    auto *Then = block("if.true"), *Else = block("if.false"),
         *End = block("if.end");
    B.CreateCondBr(C.IR, Then, Else);
    B.SetInsertPoint(Then);
    auto Prior = Active;
    auto EntryPositions =
        Transaction ? Transaction->positions() : Construction::Positions{};
    Live = Before && (!Known || !Known->isZero());
    stmt(A[1]);
    bool Y = Live;
    branch(End);
    auto TrueState = Active;
    auto YesPositions =
        Transaction ? Transaction->positions() : Construction::Positions{};
    if (Transaction)
      Transaction->restore(EntryPositions);
    B.SetInsertPoint(Else);
    Live = Before && (!Known || Known->isZero());
    Active = Prior;
    if (A.size() > 2)
      stmt(A[2]);
    bool Z = Live;
    if (Transaction) {
      auto NoPositions = Transaction->positions();
      if (Y && Z) {
        NoPositions.insert(YesPositions.begin(), YesPositions.end());
        Transaction->restore(NoPositions);
      } else if (Y)
        Transaction->restore(YesPositions);
    }
    branch(End);
    if (Y && Z)
      joinStorage(TrueState);
    else if (Y)
      Active = std::move(TrueState);
    Live = Y || Z;
    B.SetInsertPoint(End);
    return;
  }
  if (N.K == Node::Switch) {
    auto RunArms = [&](size_t First, StringRef Start) {
      for (size_t I = First; I && I < A.size(); ++I) {
        auto Body = A[I].Children.back();
        bool Fall = !Body.Children.empty() &&
                    Body.Children.back().K == Node::Fallthrough;
        if (Fall) {
          if (I + 1 == A.size())
            fail(A[I].At, "invalid final fallthrough");
          Body.Children.pop_back();
        }
        try {
          stmt(Body, Start);
        } catch (const ConstantTransfer &T) {
          if (T.Kind != Node::Break || (!T.Label.empty() && T.Label != Label))
            throw;
          break;
        }
        if (!Fall)
          break;
        Start = {};
      }
    };
    if (!EntryLabel.empty()) {
      for (size_t I = 1; I < A.size(); ++I)
        if (enteredLabel(A[I].Children.back(), EntryLabel)) {
          RunArms(I, EntryLabel);
          return;
        }
      fail(N.At, "unknown statement label");
    }
    auto S = eval(A[0]);
    if (S.Type == "integer")
      S = convert(S, materializationType(S.Type, N.At), N.At);
    endExpression();
    if (!integer(S.Type) && !U.Enums.count(S.Type))
      fail(N.At, "switch requires an integer");
    auto *End = IR ? block("switch.end") : nullptr;
    std::vector<llvm::BasicBlock *> Arms;
    for (size_t I = 1; IR && I < A.size(); ++I)
      Arms.push_back(block("case"));
    auto *SW = IR ? B.CreateSwitch(S.IR, End) : nullptr;
    size_t Selected = 0, Fallback = 0;
    Loops.push_back({End, nullptr, Scopes.size(), Label});
    std::set<uint64_t> Cases;
    bool Default = false, CanExit = false;
    for (size_t I = 1; I < A.size(); ++I) {
      auto &Arm = A[I];
      if (IR)
        B.SetInsertPoint(Arms[I - 1]);
      Live = true;
      if (Arm.Children.size() == 1) {
        if (Default)
          fail(Arm.At, "duplicate default arm");
        Default = true;
        Fallback = I;
        if (SW)
          SW->setDefaultDest(Arms[I - 1]);
      } else {
        auto *K = llvm::cast<llvm::ConstantInt>(
            convert(constantEval(Arm.Children[0]), S.Type, Arm.At).IR);
        if (!Cases.insert(K->getZExtValue()).second)
          fail(Arm.At, "duplicate case");
        if (SW)
          SW->addCase(K, Arms[I - 1]);
        else if (K == S.IR)
          Selected = I;
      }
      auto Body = Arm.Children.back();
      bool Fall =
          !Body.Children.empty() && Body.Children.back().K == Node::Fallthrough;
      if (Fall) {
        if (I + 1 == A.size())
          fail(Arm.At, "invalid final fallthrough");
        Body.Children.pop_back();
      }
      if (!IR)
        continue;
      if (Transaction)
        Transaction->restoreFlow(Body);
      stmt(Body);
      CanExit |= Live && !Fall;
      branch(Fall ? Arms[I] : End);
    }
    if (!IR) {
      Loops.pop_back();
      RunArms(Selected ? Selected : Fallback, {});
      return;
    }
    if (Transaction)
      Transaction->restoreFlow(N, true);
    Live = !Default || CanExit || Loops.back().BreakUsed;
    Loops.pop_back();
    B.SetInsertPoint(End);
    return;
  }
  if (!IR) {
    if (N.K == Node::Label) {
      StatementLabel = N.Text;
      stmt(A[0], EntryLabel == N.Text ? StringRef{} : EntryLabel);
      return;
    }
    if (N.K == Node::Match) {
      constantMatch(N);
      return;
    }
    if (N.K == Node::For || N.K == Node::Do || N.K == Node::While) {
      bool For = N.K == Node::For, Do = N.K == Node::Do;
      Scopes.emplace_back();
      try {
        if (For && EntryLabel.empty())
          stmt(A[0]);
        for (bool First = true;; First = false) {
          U.chargeConstant(N.At);
          auto &Test = A[For || Do ? 1 : 0];
          if (!(First && (Do || !EntryLabel.empty())) &&
              Test.K != Node::Empty) {
            bool Stop =
                llvm::cast<llvm::ConstantInt>(boolean(Test).IR)->isZero();
            endExpression();
            if (Stop)
              break;
          }
          try {
            stmt(A[For ? 3 : Do ? 0 : 1], First ? EntryLabel : StringRef{});
          } catch (const ConstantTransfer &C) {
            if (!C.Label.empty() && C.Label != Label)
              throw;
            if (C.Kind == Node::Break)
              break;
            if (C.Kind != Node::Continue)
              throw;
          }
          if (For && A[2].K != Node::Empty) {
            eval(A[2]);
            endExpression();
          }
        }
      } catch (const ConstantTransfer &) {
        endConstantScope();
        Scopes.pop_back();
        throw;
      }
      endConstantScope();
      Scopes.pop_back();
      return;
    }
    if (N.K == Node::Goto && !F)
      fail(N.At, "goto requires a function");
    if (N.K == Node::Break || N.K == Node::Continue || N.K == Node::Goto)
      throw ConstantTransfer{N.K, {}, N.Text, N.At};
    fail(N.At, "statement unavailable in constant evaluation");
  }
  if (N.K == Node::For || N.K == Node::While || N.K == Node::Do) {
    bool For = N.K == Node::For, Do = N.K == Node::Do;
    Scopes.emplace_back();
    if (For)
      stmt(A[0]);
    auto *Cond = block("loop.test"), *Body = block("loop.body"),
         *Next = block("loop.next"), *End = block("loop.end");
    branch(Do ? Body : Cond);
    B.SetInsertPoint(Cond);
    auto &Test = A[For || Do ? 1 : 0];
    if (Transaction && Test.K != Node::Empty)
      Transaction->restoreFlow(Test);
    auto C = Test.K == Node::Empty ? literal(1, "bool") : boolean(Test);
    B.CreateCondBr(C.IR, Body, End);
    B.SetInsertPoint(Body);
    Loops.push_back({End, Next, Scopes.size(), Label});
    if (Transaction)
      Transaction->restoreFlow(A[For ? 3 : Do ? 0 : 1]);
    stmt(A[For ? 3 : Do ? 0 : 1]);
    branch(Next);
    B.SetInsertPoint(Next);
    if (For && A[2].K != Node::Empty) {
      if (Transaction)
        Transaction->restoreFlow(A[2]);
      eval(A[2]);
    }
    branch(Cond);
    if (Transaction)
      Transaction->restoreFlow(N, true);
    auto *K = llvm::dyn_cast<llvm::ConstantInt>(C.IR);
    Live = Loops.back().BreakUsed || !K || K->isZero();
    Loops.pop_back();
    B.SetInsertPoint(End);
    forgetStorage();
    cleanup(Scopes.size() - 1);
    Scopes.pop_back();
    return;
  }
  if (N.K == Node::Break || N.K == Node::Continue) {
    for (auto I = Loops.rbegin(); I != Loops.rend(); ++I) {
      auto *Dest = N.K == Node::Break ? I->Break : I->Continue;
      if (Dest && (N.Text.empty() || N.Text == I->Name)) {
        cleanup(I->Depth);
        exitInvariantConstructionLifetimes(I->Depth);
        branch(Dest);
        I->BreakUsed |= N.K == Node::Break && Live;
        B.SetInsertPoint(block("unreachable"));
        Live = false;
        return;
      }
    }
    fail(N.At, "break or continue outside an eligible control statement");
  }
  if (N.K == Node::Match) {
    match(N);
    return;
  }
  if (N.K == Node::Label || N.K == Node::Goto) {
    auto &Target = Labels[N.Text];
    if (!Target)
      Target = block("label." + N.Text);
    if (N.K == Node::Goto) {
      if (!F)
        fail(N.At, "goto requires a function");
      const auto &Exited =
          F->ExitedLifetimes.Exited.at({N.At.Line, N.At.Column});
      cleanup(0, &Exited);
      exitInvariantConstructionLifetimes(0, &Exited);
      branch(Target);
      B.SetInsertPoint(block("unreachable"));
      Live = false;
      return;
    }
    if (!DefinedLabels.insert(N.Text).second)
      fail(N.At, "duplicate statement label");
    branch(Target);
    B.SetInsertPoint(Target);
    Live |= F && F->ExitedLifetimes.Targets.count(N.Text);
    if (Transaction)
      Transaction->restoreFlow(N);
    StatementLabel = N.Text;
    stmt(A[0]);
    return;
  }
  fail(N.At, "unsupported statement '" + N.Text + "'");
}

bool Frame::adjust(Value &V, const std::string &T, const Token &At, bool Emit) {
  if (V.Type == T)
    return true;
  if (!U.Records.count(V.Type))
    return false;
  std::optional<BasePath> Path;
  for (const auto &[Candidate, Type] : U.Records.at(V.Type).Views) {
    if (Type != T)
      continue;
    if (Path) {
      if (Emit)
        fail(At, "ambiguous inherited base conversion");
      return false;
    }
    Path = Candidate;
  }
  if (!Path)
    return false;
  if (Emit)
    V = baseView(V, *Path);
  return true;
}
