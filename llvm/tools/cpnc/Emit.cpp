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
std::string unconst(std::string T) {
  return StringRef(T).starts_with("const<") && ends(T, ">")
             ? T.substr(6, T.size() - 7)
             : T;
}
bool assignment(StringRef Op) {
  return Op == "=" || Op == "+=" || Op == "-=" || Op == "*=" || Op == "/=" ||
         Op == "%=" || Op == "&=" || Op == "|=" || Op == "^=" || Op == "<<=" ||
         Op == ">>=";
}
struct Transfer {
  Node::Kind Kind;
  Value Result;
};
} // namespace
Value Frame::lookup(const Token &T) {
  for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
    auto V = I->Names.find(T.Text);
    if (V != I->Names.end()) {
      if (V->second.Type.empty())
        fail(T, "use before initialization");
      return V->second;
    }
  }
  if (Env.Values.count(T.Text))
    return Env.Values.at(T.Text);
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
      return U.Globals.at(Key);
    }
  }
  auto Key = scopeKey(Prefix, T.Text,
                      [&](const std::string &K) { return U.Globals.count(K); });
  if (!Key.empty()) {
    if (auto I = U.StaticMembers.find(Key); I != U.StaticMembers.end())
      checkAccess(I->second.second, I->second.first, T);
    return U.Globals.at(Key);
  }
  fail(T, "unknown name '" + T.Text + "'");
}
void Frame::checkAccess(const Node &Decl, const std::string &Owner,
                        const Token &At) {
  auto Access = Decl.Settings.find("access");
  if (Access == Decl.Settings.end() || Access->second == "public" ||
      (F && F->Owner == Owner))
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
    return U.Globals.at(I->first);
  }
  Obj = baseView(Obj, *Path);
  auto &R = U.Records.at(Obj.Type);
  for (size_t I = 0; I < R.Fields.size(); ++I)
    if (R.Fields[I].Decl.Text == T.Text) {
      auto &Field = R.Fields[I];
      if (Obj.Address == PendingObject && PendingSlots.count(T.Text))
        fail(T, "use before initialization");
      if (Transaction && Obj.Address == Self.Address)
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
  size_t I = 0;
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
      }
    } else {
      auto *Ptr = allocate(T, P.At);
      B.CreateStore(A, Ptr);
      V = {T, nullptr, Ptr, P.Const};
      if (TracksStorage && !ends(T, "*")) {
        V.Storage = "parameter." + std::to_string(U.Serial++);
        track(V);
        Extents[V.Storage] = V;
        Active[V.Storage] = 1;
      }
      Scopes[0].Drops.push_back(V);
    }
    if (!P.Text.empty())
      Scopes[0].Names[P.Text] = V;
  }
}
Value Frame::boolean(const Node &N) {
  auto V = eval(N);
  if (V.Type != "bool")
    fail(N.At, "condition requires bool");
  if (N.K == Node::Binary && N.Text == "=")
    Opt.warn(N.At, "assignment used directly as a Boolean condition");
  return V;
}
Value Frame::place(const Node &N, bool NeedLive) {
  Value V;
  if (N.K == Node::Name)
    V = lookup(N.At);
  else if (N.K == Node::Unary && N.Text == "*") {
    auto P = eval(N.Children[0]);
    if (!ends(P.Type, "*") || P.Type == "void*")
      fail(N.At, "typed object pointer required");
    auto Base = element(P.Type);
    V = {unconst(Base), nullptr, P.IR, Base != unconst(Base)};
    V.borrow(P);
    if (llvm::isa<llvm::ConstantPointerNull>(P.IR))
      fail(N.At, "null pointer access");
  } else if (N.K == Node::Member) {
    auto Base = N.Definition ? eval(N.Children[0]) : place(N.Children[0]);
    if (N.Definition) {
      if (!ends(Base.Type, "*"))
        fail(N.At, "typed object pointer required");
      auto T = element(Base.Type);
      Value Receiver{unconst(T), nullptr, Base.IR, unconst(T) != T};
      Receiver.borrow(Base);
      ensureLive(Receiver, N.At);
      Base = Receiver;
    }
    V = member(Base, N.At);
  } else if (N.K == Node::Index)
    V = subscript(N);
  else
    V = eval(N);
  if (!V.Address)
    fail(N.At, "object lvalue required");
  if (NeedLive)
    ensureLive(V, N.At);
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
  if (auto *K = llvm::dyn_cast<llvm::ConstantInt>(Index.IR)) {
    if (K->getValue().uge(Array->getNumElements()))
      fail(N.At, "array index outside extent");
  }
  auto *I = B.CreateIntCast(Index.IR, B.getInt64Ty(), signedType(Index.Type));
  guard(B.CreateICmpUGE(I, B.getInt64(Array->getNumElements())));
  auto E = element(Base.Type);
  return subobject(
      Base, {unconst(E), nullptr,
             B.CreateInBoundsGEP(Array, Base.Address, {B.getInt32(0), I}),
             Base.Readonly || E != unconst(E)});
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
  auto V = eval(N);
  if (!llvm::isa_and_nonnull<llvm::Constant>(V.IR))
    fail(N.At, "constant expression required");
  return V;
}
Value Frame::eval(const Node &N, std::string Expected) {
  auto &A = N.Children;
  auto Op = N.Text;
  if (!IR && U.ConstantDepth && ++U.ConstantSteps > 100000)
    fail(N.At, "constant evaluation step budget exhausted");
  if (!IR && ((N.K == Node::Unary && (Op == "++" || Op == "--")) ||
              (N.K == Node::Binary && assignment(Op)))) {
    if (A[0].K != Node::Name)
      fail(N.At, "constant assignment requires a local variable");
    for (auto It = Scopes.rbegin(); It != Scopes.rend(); ++It) {
      auto Pos = It->Names.find(A[0].Text);
      if (Pos == It->Names.end())
        continue;
      auto Old = Pos->second;
      if (Old.Readonly)
        fail(N.At, "writable lvalue required");
      Value V;
      if (Op == "=")
        V = eval(A[1]);
      else {
        Node Math = N;
        Math.Text = Op == "++"   ? "+"
                    : Op == "--" ? "-"
                                 : Op.substr(0, Op.size() - 1);
        V = binary(Math, Old, N.K == Node::Unary ? literal(1) : eval(A[1]));
      }
      V = convert(V, Old.Type, N.At);
      Pos->second = V;
      return N.Definition ? Old : V;
    }
    fail(N.At, "constant assignment requires a local variable");
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
  case Node::Number: {
    std::string Digits;
    for (char C : Op)
      if (C != '_')
        Digits += C;
    StringRef S(Digits);
    unsigned Radix = 10;
    if (S.consume_front_insensitive("0x"))
      Radix = 16;
    else if (S.consume_front_insensitive("0b"))
      Radix = 2;
    else if (S.consume_front_insensitive("0o"))
      Radix = 8;
    if (S.size() > 65536)
      fail(N.At, "integer literal exceeds compiler resource limit");
    return constant(llvm::APInt(
        std::max(2u, llvm::APInt::getSufficientBitsNeeded(S, Radix) + 1), S,
        Radix));
  }
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
    return {"u8[" + std::to_string(S.size() + 1) + "]", C, G, true};
  }
  case Node::Name:
    if (Op == "true" || Op == "false")
      return literal(Op == "true", "bool");
    else if (Op == "nullptr")
      return {"nullptr_t", llvm::ConstantPointerNull::get(B.getPtrTy())};
    else if (builtinPredicate(Op) || constraint(Op))
      return literal(predicate(N), "bool");
    else
      return load(lookup(N.At));
  case Node::Index:
    return load(subscript(N));
  case Node::Member:
    return load(place(N));
  case Node::Call:
    return call(A[0], std::vector<Node>(A.begin() + 1, A.end()));
  case Node::Configured: {
    auto Old = Opt;
    configure(Opt, N);
    auto V = eval(A[0], Expected);
    Opt = Old;
    return V;
  }
  case Node::Unary: {
    if (Op == "sizeof" || Op == "alignof") {
      auto T = A[0].K == Node::TypeArg ? resolve(A[0].Type, N.At)
               : A[0].K == Node::String
                   ? "u8[" + std::to_string(unquote(A[0].At).size() + 1) + "]"
               : A[0].K == Node::Name ? lookup(A[0].At).Type
                                      : "";
      if (T.empty()) {
        auto *Tmp = llvm::Function::Create(
            llvm::FunctionType::get(B.getVoidTy(), false),
            llvm::GlobalValue::InternalLinkage, "cpn.unevaluated", U.M);
        Frame Probe(U, F, Tmp, Prefix);
        Probe.Scopes = Scopes;
        Probe.Self = Self;
        Probe.Env = Env;
        Probe.B.SetInsertPoint(Probe.block("entry"));
        T = Probe.eval(A[0]).Type;
        Tmp->eraseFromParent();
      }
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
        return {Expected, checkSelected(Match, N.At)->IR};
      }
      auto V = place(A[0]);
      Value P{(V.Readonly ? "const<" + V.Type + ">" : V.Type) + "*", V.Address};
      P.borrow(V);
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
      return N.Definition ? Value(V.Type, V.IR)
                          : Value(Next.Type, Next.IR, D.Address);
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
      V = convert(V, Expected.empty() ? Opt.DefaultInt : Expected, N.At);
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
      B.SetInsertPoint(Yes);
      Value X = N.K == Node::Conditional ? eval(A[1], Expected)
                : Op == "&&"             ? boolean(A[1])
                                         : literal(1, "bool");
      if (N.K != Node::Conditional)
        endExpression(Mark);
      auto *EndYes = B.GetInsertBlock();
      B.SetInsertPoint(No);
      Value Y = N.K == Node::Conditional ? eval(A[2], Expected)
                : Op == "||"             ? boolean(A[1])
                                         : literal(0, "bool");
      if (N.K != Node::Conditional)
        endExpression(Mark);
      auto *EndNo = B.GetInsertBlock();
      auto T = X.Type == "integer" ? Y.Type : X.Type;
      if (T == "integer")
        T = Expected.empty() ? Opt.DefaultInt : Expected;
      B.SetInsertPoint(EndNo);
      Y = convert(Y, T, N.At);
      branch(Done);
      B.SetInsertPoint(EndYes);
      X = convert(X, T, N.At);
      branch(Done);
      B.SetInsertPoint(Done);
      auto *P = B.CreatePHI(U.ir(T), 2);
      P->addIncoming(X.IR, EndYes);
      P->addIncoming(Y.IR, EndNo);
      Value V{T, P};
      if (X.Address && Y.Address) {
        auto *L = B.CreatePHI(B.getPtrTy(), 2);
        L->addIncoming(X.Address, EndYes);
        L->addIncoming(Y.Address, EndNo);
        V.Address = L;
        V.Readonly = X.Readonly || Y.Readonly;
      }
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
      B.CreateStore(R.IR, D.Address);
      return {D.Type, R.IR, D.Address};
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
      auto T = integer(Expected) && Expected != "integer" ? Expected
                                                          : Opt.DefaultInt;
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
  auto Base = baseRef(Param), T = unconst(Base);
  bool Ref = Base != Param, RO = T != Base, Lvalue = V.Address && !V.Expiring;
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
      if (U.Signatures.count(From) && U.Signatures.count(To) &&
          U.Signatures.at(From) == U.Signatures.at(To) &&
          (!callableFlag(To, " noexcept") || callableFlag(From, " noexcept")) &&
          (!callableFlag(From, " whole") || callableFlag(To, " whole")))
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
  if (!Fam.Decl.Generics.empty() && Fam.Decl.Generics.back().Pack) {
    size_t Fixed = Fam.Decl.Generics.size() - 1;
    size_t FixedParams =
        std::count_if(Fam.Decl.Params.begin(), Fam.Decl.Params.end(),
                      [](auto &P) { return !P.Pack; });
    size_t Count = N.TemplateArgs.size() > Fixed ? N.TemplateArgs.size() - Fixed
                   : Args.size() > FixedParams   ? Args.size() - FixedParams
                                                 : 0;
    Fam = expand(Fam, Count, N.At);
  }
  if (Args.size() > Fam.Decl.Params.size() ||
      (Args.size() < Fam.Decl.Params.size() &&
       Fam.Decl.Params[Args.size()].Children.empty()))
    throw DeductionFailure{{N.At, "no viable overload"}};
  auto S = bind(Fam, N.TemplateArgs, Args, N.At);
  std::string ID = Key + "$" + std::to_string(Fam.Site.Through) + "<";
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
  auto *D = U.declare(Fam.Decl, ID, Fam.Prefix, S);
  D->Origin = &Source;
  U.Instances[ID] = D;
  return D;
}

Function *Frame::select(std::string Name, const Node &N,
                        const std::vector<Value> &Args, Value Receiver,
                        bool Operator) {
  auto Key = callKey(Name, Receiver.Type);
  struct Candidate {
    Function *Decl;
    std::vector<unsigned> Ranks;
  };
  auto Better = [](const Candidate &A, const Candidate &B) {
    bool Strict = false;
    for (size_t I = 0; I < A.Ranks.size(); ++I) {
      if (A.Ranks[I] > B.Ranks[I])
        return false;
      Strict |= A.Ranks[I] < B.Ranks[I];
    }
    return Strict ||
           betterPattern(A.Decl->Origin ? A.Decl->Origin->Decl : A.Decl->Decl,
                         B.Decl->Origin ? B.Decl->Origin->Decl : B.Decl->Decl);
  };
  std::vector<Candidate> Best;
  auto Group =
      N.ExplicitApplication ? std::vector<Function *>{} : visibleOverloads(Key);
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
                                       Function *Context) {
  CallArguments A;
  for (size_t I = 0; I < Args.size(); ++I) {
    if (IR) {
      if (I)
        B.SetInsertPoint(block("argument"));
      A.Entries.push_back(B.GetInsertBlock());
    }
    A.Values.push_back(eval(Args[I], Context && I < Context->Params.size()
                                         ? Context->Params[I]
                                         : ""));
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
  if (F && IR)
    F->Calls.insert(&D);
  if (RequireNoexcept && !D.Decl.Noexcept)
    fail(T, "expression requires a nonthrowing call");
  std::vector<llvm::Value *> Values;
  if (!D.Owner.empty() && !D.isStatic())
    Values.push_back(Receiver.Address);
  auto Original = std::move(Scopes);
  auto OldPrefix = Prefix;
  Scopes = {Local{}};
  Prefix = D.DefaultPrefix;
  bool Defaults = Actual.size() < D.Params.size(),
       Constant = !IR || D.Decl.Settings.count("mode");
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
      llvm::SaveAndRestore Bindings(Env, D.Env);
      V = construct(unconst(baseRef(Ty)), P.Children, P.At);
    }
    if (!Prepared || I >= Actual.size())
      V = ends(Ty, "&") ? bindReference(V, Ty, P.At)
                        : materialize(convert(V, Ty, T), T);
    if (!ends(Ty, "&") && Defaults && !Constant) {
      auto *Addr = allocate(Ty, P.At);
      B.CreateStore(V.IR, Addr);
      V = {Ty, nullptr, Addr};
    }
    Cells.push_back(V);
    if (!P.Text.empty())
      Scopes.back().Names[P.Text] = V;
  }
  for (size_t I = 0; I < Cells.size(); ++I) {
    auto &P = D.DefaultParams[I];
    auto V =
        Defaults && !P.Text.empty() ? Scopes.back().Names.at(P.Text) : Cells[I];
    Values.push_back(ends(D.Params[I], "&") && !Constant ? V.Address
                                                         : load(V).IR);
  }
  Scopes = std::move(Original);
  Prefix = std::move(OldPrefix);
  if (!IR || D.Decl.Settings.count("mode")) {
    if (!D.Decl.Required || D.Decl.Prototype)
      fail(T, "constant expression requires a constexpr function");
    struct Budget {
      Context &U;
      ~Budget() { --U.ConstantDepth; }
    } Balance{U};
    if (!U.ConstantDepth++)
      U.ConstantSteps = 0;
    if (U.ConstantDepth > 256)
      fail(T, "constant invocation depth exhausted");
    Frame CF(U, &D, nullptr);
    for (size_t I = 0; I < D.Params.size(); ++I) {
      auto *C = llvm::dyn_cast<llvm::Constant>(Values[I]);
      if (!C)
        fail(T, "constant argument required");
      auto Base = baseRef(D.Params[I]);
      CF.Scopes[0].Names[D.Decl.Params[I].Text] = {unconst(Base), C, nullptr,
                                                   Base != unconst(Base)};
    }
    try {
      CF.stmt(D.Decl.Children[0]);
    } catch (const Transfer &R) {
      if (R.Kind == Node::Return)
        return CF.convert(R.Result, D.Result, T);
      throw;
    }
    fail(T, "constant invocation completed without a result");
  }
  auto *Before = wholeEpoch();
  llvm::CallInst *Call = nullptr;
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
    Values[0] = B.CreateGEP(B.getInt8Ty(), Receiver.Address, Delta);
    Call = B.CreateCall(D.IR->getFunctionType(),
                        B.CreateLoad(B.getPtrTy(), Slot), Values);
  } else
    Call =
        B.CreateCall(Receiver.BaseView && D.BaseIR ? D.BaseIR : D.IR, Values);
  Call->setAttributes(D.IR->getAttributes());
  propagateWhole(Before);
  // A helper can end or replace an extent reached through its receiver or
  // a borrowed argument. Its live state is subsequently checked at runtime.
  if (!Receiver.Storage.empty() && Active.count(Receiver.Storage))
    Active[Receiver.Storage] = -1;
  for (size_t I = 0; I < Actual.size(); ++I)
    if ((ends(D.Params[I], "&") || ends(D.Params[I], "*")) &&
        !Actual[I].Storage.empty() && Active.count(Actual[I].Storage))
      Active[Actual[I].Storage] = -1;
  return callResult(D.Result, Call, T);
}
Value Frame::call(const Node &C, const std::vector<Node> &Args,
                  Value Receiver) {
  if (C.K != Node::Unary && C.K != Node::Name && C.K != Node::Member)
    return callClosure(eval(C), Args, C.At);
  if (C.K == Node::Unary && C.Text == "*" && C.Children.size() == 1)
    return indirect(eval(C.Children[0]), Args, C.At);
  if (C.K == Node::Name) {
    for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
      auto V = I->Names.find(C.Text);
      if (V != I->Names.end() && U.Records.count(V->second.Type))
        return callClosure(V->second, Args, C.At);
      if (V != I->Names.end() && ends(V->second.Type, "*") &&
          U.Signatures.count(element(V->second.Type)))
        return indirect(load(V->second), Args, C.At);
    }
  }
  if (C.K == Node::Member) {
    Receiver = C.Definition ? eval(C.Children[0]) : place(C.Children[0]);
    if (C.Definition) {
      auto T = element(Receiver.Type);
      Receiver = {unconst(T), nullptr, Receiver.IR, T != unconst(T)};
    }
  } else if (C.K != Node::Name)
    fail(C.At, "callable expression required");
  auto Name = C.Text;
  if (const auto *Case = findCase(Name, C.At))
    return variant(*Case, Args, C.At);
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
  if (!FieldFlags.empty() && Args.size() == 1 &&
      (Name == "destroy" || Name == "abandon")) {
    auto Slot = directField(Args[0]);
    if (!Slot.empty()) {
      endField(Slot, C.At, Name == "destroy", true);
      return {"void"};
    }
  }
  if (((Name == "destroy" || Name == "abandon" || Name == "storage_of") &&
       Args.size() == 1) ||
      (Name == "construct_at" && !Args.empty() && C.TemplateArgs.size() == 1))
    return storageCall(C, Args);
  if (C.K == Node::Name && typeCallee(Name))
    return construct(resolve(Name, C.At), Args, C.At);
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
  auto A = evaluateArguments(
      Args, Group.size() == 1 && !U.FunctionFamilies.count(Key) ? Group.front()
                                                                : nullptr);
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
bool Frame::typeCallee(const std::string &Name) const {
  if (builtin(Name) || Env.Types.count(Name))
    return true;
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
  if (typeCallee(Key) && resolve(Key, Arg.At) == T)
    return construct(T, {Arg.Children.begin() + 1, Arg.Children.end()}, Arg.At,
                     Dest);
  return {};
}
Value Frame::construct(const std::string &T, const std::vector<Node> &Args,
                       const Token &At, llvm::Value *Dest, const Node *Tail,
                       bool AsBase) {
  if (T == "void")
    fail(At, "object cannot have void type");
  if (floating(T)) {
    if (Args.size() > 1)
      fail(At, "invalid scalar construction");
    Value V = Args.empty() ? Value{T, llvm::ConstantFP::get(U.ir(T), 0.0)}
                           : floatingConvert(eval(Args[0], T), T, At, true);
    if (Dest)
      B.CreateStore(V.IR, Dest);
    if (Tail) {
      Scopes.emplace_back();
      Scopes.back().Names["this"] = {T + "*", Dest};
      stmt(*Tail);
      Scopes.pop_back();
    }
    return V;
  }
  auto *Ty = U.ir(T, At);
  if (!Ty->isSized())
    fail(At, "construction requires a complete object type");
  if (ends(T, "]")) {
    if (!IR)
      fail(At, "array construction requires object storage");
    auto *Ptr = Dest ? Dest : allocate(T, At);
    auto *Array = llvm::cast<llvm::ArrayType>(Ty);
    auto Count = Array->getNumElements();
    if (Args.size() > Count)
      fail(At, "too many array initializers");
    if (Args.size() == 1 && Args[0].K == Node::Name &&
        lookup(Args[0].At).Type == T) {
      auto V = eval(Args[0]);
      materialize(V, At, Ptr);
      return {T, B.CreateLoad(Ty, Ptr), Ptr};
    }
    if (Count > 65536)
      fail(At, "array construction exceeds compiler resource limit");
    for (size_t I = 0; I < Count; ++I) {
      auto *P = B.CreateInBoundsGEP(Ty, Ptr, {B.getInt32(0), B.getInt64(I)});
      construct(element(T),
                I < Args.size() ? std::vector<Node>{Args[I]}
                                : std::vector<Node>{},
                At, P);
    }
    return {T, B.CreateLoad(Ty, Ptr), Ptr};
  }
  if (Args.size() == 1 && !Tail && !AsBase)
    if (auto Direct = directConstruction(Args[0], T, Dest))
      return *Direct;
  if (U.Variants.count(T)) {
    if (Args.empty() && U.DefaultCase.count(T))
      return variant(U.Cases.at(U.DefaultCase.at(T)), {}, At, Dest, true);
    if (Args.size() != 1)
      fail(At, "union construction requires a selected case");
    const auto &Arg = Args.front();
    auto V = convert(eval(Arg), T, At);
    if (!IR)
      fail(At, "union construction requires object storage");
    auto *Ptr = Dest ? Dest : allocate(T, At);
    materialize(V, At, Ptr);
    Value Result{T, B.CreateLoad(Ty, Ptr), Ptr};
    if (!Dest) {
      Result.Prvalue = Result.Expiring = true;
      Temps.push_back(Result);
    }
    return Result;
  }
  if (U.Records.count(T)) {
    if (!IR)
      fail(At, "constant record construction is unavailable");
    auto *Ptr = Dest ? Dest : allocate(T, At);
    Value Obj{T, nullptr, Ptr};
    auto &R = U.Records.at(T);
    Obj.BaseView = AsBase;
    if (!AsBase)
      bindVirtualLayout(Obj);
    auto Arguments = evaluateArguments(Args);
    auto &Actual = Arguments.Values;
    std::map<std::string, const Node *> Producers;
    if (Tail)
      for (auto &S : Tail->Children)
        if (S.K == Node::Init && !Producers.emplace(initSlot(S), &S).second)
          fail(S.At, "duplicate initialization producer");
    if (Actual.size() == 1 && Actual[0].Type == T) {
      admitArguments(Arguments, nullptr, At);
      if (AsBase && R.VirtualCount)
        transfer(Actual[0], Ptr,
                 Actual[0].Expiring ? SpecialOperation::MoveConstruct
                                    : SpecialOperation::CopyConstruct,
                 At, true);
      else
        materialize(Actual[0], At, Ptr);
    } else {
      auto It = U.Overloads.find(T + "::$ctor");
      bool Authored =
          It != U.Overloads.end() && llvm::any_of(It->second, [&](auto *D) {
            return Actual.size() <= D->Params.size() &&
                   (Actual.size() == D->Params.size() ||
                    !D->Decl.Params[Actual.size()].Children.empty());
          });
      if (Authored) {
        Node C(Node::Name, At);
        auto *D = select("$ctor", C, Actual, Obj);
        admitArguments(Arguments, D, At);
        if (Producers.empty())
          invoke(*D, Actual, At, Obj, true);
        else {
          Frame Root(U, D, IR);
          Root.B.SetInsertPoint(B.GetInsertBlock());
          Root.BaseLayer = AsBase;
          Root.Self = Obj;
          Root.Scopes[0].Names["this"] = {T + "*", Ptr};
          for (size_t I = 0; I < D->Params.size(); ++I) {
            auto &P = D->Decl.Params[I];
            auto Ty = D->Params[I];
            auto V = I < Actual.size() ? Actual[I]
                                       : Root.construct(unconst(baseRef(Ty)),
                                                        P.Children, P.At);
            if (!ends(Ty, "&")) {
              V = convert(V, Ty, At);
              auto *Addr = allocate(Ty, At);
              if (I < Actual.size())
                Root.B.CreateStore(V.IR, Addr);
              else
                Root.materialize(V, At, Addr);
              V = {Ty, nullptr, Addr, P.Const};
              Root.Scopes[0].Drops.push_back(V);
            } else
              V.IR = nullptr;
            Root.Scopes[0].Names[P.Text] = V;
          }
          Root.InlineReturn = block("ctor.done");
          Construction Plan(Root, *D, Obj, Tail, this);
          Plan.run(Root);
          Root.branch(Root.InlineReturn);
          B.SetInsertPoint(Root.InlineReturn);
          Producers.clear();
        }
      } else {
        admitArguments(Arguments, nullptr, At);
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
            auto V = convert(Actual[I - R.Bases.size()], Field.Type, At);
            materialize(V, At, P);
          } else {
            construct(Field.Type,
                      Found == Producers.end() ? Field.Decl.Children
                                               : Found->second->Children,
                      At, P, nullptr, I < R.Bases.size());
            if (Found != Producers.end())
              Producers.erase(Found);
          }
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
    if (Tail) {
      auto Old = Self;
      Self = Obj;
      Scopes.emplace_back();
      Scopes.back().Names["this"] = {T + "*", Ptr};
      for (auto &S : Tail->Children)
        if (S.K != Node::Init)
          stmt(S);
      cleanup(Scopes.size() - 1);
      Scopes.pop_back();
      Self = Old;
    }
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
  Value V = Args.empty() ? Value{T, llvm::Constant::getNullValue(Ty)}
                         : convert(eval(Args[0], T), T, At);
  if (Dest)
    B.CreateStore(V.IR, Dest);
  if (Tail) {
    Scopes.emplace_back();
    Scopes.back().Names["this"] = {T + "*", Dest};
    for (auto &S : Tail->Children)
      stmt(S);
    Scopes.pop_back();
  }
  return V;
}
void Frame::drop(Value V, bool AsBase) {
  if (!IR || !V.Address)
    return;
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
void Frame::dropLayer(Value V, bool AsBase) {
  if (ends(V.Type, "]")) {
    auto E = element(V.Type);
    if (!TracksStorage && !U.Records.count(E) && !ends(E, "]"))
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
  if (auto It = U.Overloads.find(V.Type + "::$drop"); It != U.Overloads.end()) {
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
    dropChild(V, {F.Type, nullptr, fieldAddress(V, I - 1)},
              I - 1 < R.Bases.size());
  }
}
void Frame::cleanup(size_t From) {
  for (size_t I = Scopes.size(); I > From; --I)
    for (auto V = Scopes[I - 1].Drops.rbegin(); V != Scopes[I - 1].Drops.rend();
         ++V) {
      drop(*V);
      if (V->Slot && !V->Subobject && Extents.count(V->Storage) &&
          Extents.at(V->Storage).Address == V->Address)
        B.CreateCall(U.M.getFunction("cpn.slot.release"), {V->Slot});
    }
}
void Frame::consume(Value V) {
  if (V.Address)
    Temps.erase(std::remove_if(Temps.begin(), Temps.end(),
                               [&](auto &T) { return T.Address == V.Address; }),
                Temps.end());
}
void Frame::endExpression(size_t From) {
  while (Temps.size() > From) {
    auto V = Temps.back();
    Temps.pop_back();
    drop(V);
  }
}
void Frame::object(const Node &N, bool Global) {
  std::string Name = Global ? Prefix + N.Text : N.Text;
  if (Global && N.Settings.count("identity"))
    Name = N.Settings.at("identity");
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
      Frame Init(U, nullptr, nullptr, Prefix);
      Init.Env = Env;
      Init.object(D, true);
      U.Statics.emplace_back(ID, D);
    }
    Scopes.back().Names[N.Text] = U.Globals.at(ID);
    return;
  }
  auto names = [&]() -> std::map<std::string, Value> & {
    return Global ? U.Globals : Scopes.back().Names;
  };
  auto Found = names().find(Name);
  bool Existing = Found != names().end();
  if (Existing && !(Global && N.Foreign))
    fail(N.At, "duplicate declaration '" + Name + "'");
  auto Ty = resolve(N.Type, N.At);
  std::vector<Node> Args = N.Children;
  const Node *Tail = nullptr;
  if (!Args.empty() && Args.back().K == Node::Tail) {
    Tail = &N.Children.back();
    Args.pop_back();
  }
  if (!Existing)
    names()[Name] = {};
  if (Global) {
    if (N.Settings.count("storage") &&
        N.Settings.at("storage") == "thread_local")
      fail(N.At, "thread-local storage is unavailable on this configuration");
    llvm::GlobalVariable *G = nullptr;
    if (Ty == "auto") {
      Ty = constantEval(Args.at(0)).Type;
      if (Ty == "real")
        Ty = Opt.DefaultReal;
      if (Ty == "integer")
        Ty = Opt.DefaultInt;
    }
    auto *LT = U.ir(Ty, N.At);
    if (!LT->isSized())
      fail(N.At, "static requires a complete type");
    if (N.Foreign) {
      auto Prev = U.ExternalObjects.find(N.Text);
      if (Prev != U.ExternalObjects.end()) {
        G = llvm::cast<llvm::GlobalVariable>(Prev->second.Address);
        if (Prev->second.Type != Ty || Prev->second.Readonly != N.Const ||
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
      U.ExternalObjects[N.Text] = {Ty, nullptr, G, N.Const};
    if (N.Foreign && !N.Definition) {
      names()[Name] = {Ty, nullptr, G, N.Const};
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
    if (Simple) {
      auto V = construct(Ty, Args, N.At);
      G->setInitializer(llvm::cast<llvm::Constant>(V.IR));
      G->setConstant(N.Const);
      StaticConstant = N.Required ? V.IR : nullptr;
      names()[Name] = {Ty, StaticConstant, G, N.Const};
      if (!U.SlotType || N.Const)
        return;
    }
    auto FT = llvm::FunctionType::get(B.getVoidTy(), false);
    auto *Fn = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                      "cpn.static.init", U.M);
    Frame Init(U, nullptr, Fn, Prefix);
    Init.Env = Env;
    Init.B.SetInsertPoint(Init.block("entry"));
    if (!Simple) {
      Init.construct(Ty, Args, N.At, G, Tail);
      Init.endExpression();
      auto *Ready = new llvm::GlobalVariable(U.M, B.getInt1Ty(), false,
                                             llvm::GlobalValue::InternalLinkage,
                                             B.getFalse(), "cpn.ready");
      U.Ready[G] = Ready;
      Init.B.CreateStore(B.getTrue(), Ready);
    }
    Value Cell{Ty, StaticConstant, G, N.Const};
    if (U.SlotType) {
      auto *GlobalSlot = new llvm::GlobalVariable(
          U.M, U.SlotType, false, llvm::GlobalValue::InternalLinkage,
          llvm::Constant::getNullValue(U.SlotType), "cpn.static.slot");
      Init.track(Cell, GlobalSlot);
    }
    Init.B.CreateRetVoid();
    U.Startup.push_back(Fn);
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
      U.Shutdown.push_back(D);
    }
    return;
  }
  if (ends(Ty, "&")) {
    if (Args.size() != 1)
      fail(N.At, "reference requires one initializer");
    auto V = place(Args[0]);
    if (N.Const && baseRef(Ty) == unconst(baseRef(Ty)))
      Ty = "const<" + baseRef(Ty) + ">" + (ends(Ty, "&&") ? "&&" : "&");
    V = bindReference(V, Ty, N.At);
    names()[Name] = V;
    return;
  }
  if (!IR) {
    auto V =
        Ty == "auto" ? constantEval(Args.at(0)) : construct(Ty, Args, N.At);
    if (V.Type == "real")
      V = floatingConvert(V, Opt.DefaultReal, N.At);
    if (V.Type == "integer")
      V = convert(V, Opt.DefaultInt, N.At);
    V.Readonly = N.Const;
    names()[Name] = V;
    return;
  }
  Value V;
  llvm::Value *Ptr = nullptr;
  if (Ty == "auto") {
    V = eval(Args.at(0));
    Ty = V.Type == "integer" ? Opt.DefaultInt
         : V.Type == "real"  ? Opt.DefaultReal
                             : V.Type;
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
  Value Cell{Ty, N.Required ? V.IR : nullptr, Ptr, N.Const};
  if (Ty == "storage" || ends(Ty, "*"))
    Cell.borrow(V);
  if (Cell.Storage.empty() && Ty != "storage" && !ends(Ty, "*")) {
    Cell.Storage = "local." + std::to_string(U.Serial++);
    Active[Cell.Storage] = true;
    track(Cell);
    Extents[Cell.Storage] = Cell;
  }
  names()[Name] = Cell;
  Scopes.back().Drops.push_back(Cell);
  endExpression();
}
void Frame::stmt(const Node &N) {
  auto &A = N.Children;
  auto Label = std::move(StatementLabel);
  StatementLabel.clear();
  if (N.K == Node::Block || N.K == Node::Tail) {
    Scopes.emplace_back();
    try {
      for (auto &S : A)
        stmt(S);
    } catch (const Transfer &) {
      Scopes.pop_back();
      throw;
    }
    if (IR && Live)
      cleanup(Scopes.size() - 1);
    Scopes.pop_back();
    return;
  }
  if (N.K == Node::Init || N.K == Node::Empty)
    return;
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
    auto Old = Opt;
    configure(Opt, N);
    stmt(A[0]);
    Opt = Old;
    return;
  }
  if (!IR && U.ConstantDepth && ++U.ConstantSteps > 100000)
    fail(N.At, "constant evaluation step budget exhausted");
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
    cleanup(0);
    branch(InlineReturn);
    B.SetInsertPoint(block("unreachable"));
    Live = false;
    return;
  }
  if (N.K == Node::Return) {
    Value V{"void"};
    if (!A.empty())
      V = eval(A[0], F ? F->Result : "");
    if (!F)
      fail(N.At, "return requires a function");
    if (ends(F->Result, "*") && !V.Storage.empty() && Extents.count(V.Storage))
      fail(N.At, "borrow of automatic storage escapes the function");
    if (F->Result == "void" && V.Type != "void")
      fail(N.At, "void function cannot return a value");
    if (ends(F->Result, "&")) {
      if (!V.Address || !conversionRank(V, F->Result, N.At) ||
          llvm::isa<llvm::AllocaInst>(llvm::getUnderlyingObject(V.Address)))
        fail(N.At, "invalid reference return or borrow of automatic storage");
      auto Base = unconst(baseRef(F->Result));
      if (!adjust(V, Base, N.At))
        fail(N.At, "incompatible reference return");
      V.IR = V.Address;
    } else if (F->Result != "void") {
      V = convert(V, F->Result, N.At);
      if (IR)
        V = materialize(V, N.At);
    }
    if (!IR)
      throw Transfer{Node::Return, V};
    endExpression();
    cleanup(0);
    if (V.Type == "void")
      B.CreateRetVoid();
    else
      B.CreateRet(V.IR);
    B.SetInsertPoint(block("unreachable"));
    Live = false;
    return;
  }
  if (N.K == Node::If) {
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
    auto *Then = block("if.true"), *Else = block("if.false"),
         *End = block("if.end");
    B.CreateCondBr(C.IR, Then, Else);
    B.SetInsertPoint(Then);
    auto Prior = Active;
    auto EntryPositions =
        Transaction ? Transaction->positions() : Construction::Positions{};
    stmt(A[1]);
    bool Y = Live;
    branch(End);
    auto TrueState = Active;
    auto YesPositions =
        Transaction ? Transaction->positions() : Construction::Positions{};
    if (Transaction)
      Transaction->restore(EntryPositions);
    B.SetInsertPoint(Else);
    Live = Before;
    Active = Prior;
    if (A.size() > 2)
      stmt(A[2]);
    bool Z = Live;
    if (Transaction) {
      auto NoPositions = Transaction->positions();
      if (auto *K = llvm::dyn_cast<llvm::ConstantInt>(C.IR))
        Transaction->restore(K->isZero() ? NoPositions : YesPositions);
      else if (Y && Z) {
        NoPositions.insert(YesPositions.begin(), YesPositions.end());
        Transaction->restore(NoPositions);
      } else if (Y)
        Transaction->restore(YesPositions);
    }
    branch(End);
    if (auto *K = llvm::dyn_cast<llvm::ConstantInt>(C.IR)) {
      if (!K->isZero()) {
        Live = Y;
        Active = TrueState;
      } else
        Live = Z;
    } else {
      if (Y && Z)
        joinStorage(TrueState);
      else if (Y)
        Active = std::move(TrueState);
      Live = Y || Z;
    }
    B.SetInsertPoint(End);
    return;
  }
  if (!IR) {
    if (N.K == Node::For || N.K == Node::Do || N.K == Node::While) {
      bool For = N.K == Node::For, Do = N.K == Node::Do;
      Scopes.emplace_back();
      if (For)
        stmt(A[0]);
      for (bool First = true;; First = false) {
        auto &Test = A[For || Do ? 1 : 0];
        if (!(Do && First) && Test.K != Node::Empty &&
            llvm::cast<llvm::ConstantInt>(boolean(Test).IR)->isZero())
          break;
        try {
          stmt(A[For ? 3 : Do ? 0 : 1]);
        } catch (const Transfer &C) {
          if (C.Kind == Node::Break)
            break;
          if (C.Kind != Node::Continue)
            throw;
        }
        if (For && A[2].K != Node::Empty)
          eval(A[2]);
      }
      Scopes.pop_back();
      return;
    }
    if (N.K == Node::Break || N.K == Node::Continue)
      throw Transfer{N.K, {}};
    fail(N.At, "statement unavailable in constant evaluation");
  }
  if (N.K == Node::For || N.K == Node::While || N.K == Node::Do) {
    bool For = N.K == Node::For, Do = N.K == Node::Do;
    Scopes.emplace_back();
    if (For)
      stmt(A[0]);
    auto Header =
        Transaction ? Transaction->loopPositions(N) : Construction::Positions{};
    if (Transaction)
      Transaction->restore(Header);
    auto *Cond = block("loop.test"), *Body = block("loop.body"),
         *Next = block("loop.next"), *End = block("loop.end");
    branch(Do ? Body : Cond);
    B.SetInsertPoint(Cond);
    auto &Test = A[For || Do ? 1 : 0];
    auto C = Test.K == Node::Empty ? literal(1, "bool") : boolean(Test);
    B.CreateCondBr(C.IR, Body, End);
    B.SetInsertPoint(Body);
    Loops.push_back({End, Next, Scopes.size(), Label});
    stmt(A[For ? 3 : Do ? 0 : 1]);
    branch(Next);
    B.SetInsertPoint(Next);
    if (For && A[2].K != Node::Empty)
      eval(A[2]);
    branch(Cond);
    if (Transaction && !Do)
      Transaction->restore(Header);
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
  if (N.K == Node::Switch) {
    auto S = eval(A[0]);
    if (S.Type == "integer")
      S = convert(S, Opt.DefaultInt, N.At);
    if (!integer(S.Type) && !U.Enums.count(S.Type))
      fail(N.At, "switch requires an integer");
    auto *End = block("switch.end");
    std::vector<llvm::BasicBlock *> Arms;
    for (size_t I = 1; I < A.size(); ++I)
      Arms.push_back(block("case"));
    auto *SW = B.CreateSwitch(S.IR, End);
    Loops.push_back({End, nullptr, Scopes.size(), Label});
    std::set<uint64_t> Cases;
    bool Default = false, CanExit = false;
    for (size_t I = 1; I < A.size(); ++I) {
      auto &Arm = A[I];
      B.SetInsertPoint(Arms[I - 1]);
      Live = true;
      if (Arm.Children.size() == 1) {
        if (Default)
          fail(Arm.At, "duplicate default arm");
        Default = true;
        SW->setDefaultDest(Arms[I - 1]);
      } else {
        auto *K = llvm::cast<llvm::ConstantInt>(
            convert(constantEval(Arm.Children[0]), S.Type, Arm.At).IR);
        if (!Cases.insert(K->getZExtValue()).second)
          fail(Arm.At, "duplicate case");
        SW->addCase(K, Arms[I - 1]);
      }
      auto Body = Arm.Children.back();
      bool Fall =
          !Body.Children.empty() && Body.Children.back().K == Node::Fallthrough;
      if (Fall) {
        if (I + 1 == A.size())
          fail(Arm.At, "invalid final fallthrough");
        Body.Children.pop_back();
      }
      stmt(Body);
      CanExit |= Live && !Fall;
      branch(Fall ? Arms[I] : End);
    }
    Live = !Default || CanExit || Loops.back().BreakUsed;
    Loops.pop_back();
    B.SetInsertPoint(End);
    return;
  }
  if (N.K == Node::Label || N.K == Node::Goto) {
    auto &Target = Labels[N.Text];
    if (!Target)
      Target = block("label." + N.Text);
    if (N.K == Node::Goto) {
      branch(Target);
      B.SetInsertPoint(block("unreachable"));
      Live = false;
      return;
    }
    if (!DefinedLabels.insert(N.Text).second)
      fail(N.At, "duplicate statement label");
    branch(Target);
    B.SetInsertPoint(Target);
    Live = true;
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
