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
  if (U.Globals.count(Prefix + T.Text))
    return U.Globals.at(Prefix + T.Text);
  if (U.Globals.count(T.Text))
    return U.Globals.at(T.Text);
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
  auto &R = It->second;
  for (size_t I = 0; I < R.Fields.size(); ++I)
    if (R.Fields[I].Decl.Text == T.Text) {
      auto &Field = R.Fields[I];
      if (Obj.Address == PendingObject && PendingSlots.count(T.Text))
        fail(T, "use before initialization");
      if (Transaction && Obj.Address == Self.Address)
        Transaction->checkAccess(*this, T);
      checkAccess(Field.Decl, Obj.Type, T);
      if (Obj.Address)
        return {Field.Type, nullptr, B.CreateStructGEP(R.IR, Obj.Address, I),
                Obj.Readonly};
      return {Field.Type, B.CreateExtractValue(Obj.IR, I)};
    }
  Value Found;
  for (size_t I = 0; I < R.Bases.size(); ++I) {
    Value V;
    try {
      V = member({R.Bases[I], nullptr, B.CreateStructGEP(R.IR, Obj.Address, I),
                  Obj.Readonly},
                 T);
    } catch (const Diagnostic &D) {
      if (!StringRef(D.Message).starts_with("unknown member"))
        throw;
      continue;
    }
    if (!Found.Type.empty())
      fail(T, "ambiguous inherited member");
    Found = V;
  }
  if (!Found.Type.empty())
    return Found;
  fail(T, "unknown member '" + T.Text + "'");
}
void Frame::bindParams() {
  size_t I = 0;
  if (!F->Owner.empty()) {
    Self = {F->Owner, nullptr, IR->getArg(I++), F->Decl.Const};
    Scopes[0].Names["this"] = {F->Owner + "*", Self.Address};
  }
  for (size_t J = 0; J < F->Params.size(); ++J) {
    auto T = F->Params[J];
    auto &P = F->Decl.Params[J];
    auto *A = IR->getArg(I++);
    Value V;
    if (ends(T, "&")) {
      auto Base = baseRef(T);
      V = {unconst(Base), nullptr, A, P.Const || Base != unconst(Base)};
    } else {
      auto *Ptr = allocate(T, P.At);
      B.CreateStore(A, Ptr);
      V = {T, nullptr, Ptr, P.Const};
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
Value Frame::place(const Node &N) {
  Value V;
  if (N.K == Node::Name)
    V = lookup(N.At);
  else if (N.K == Node::Unary && N.Text == "*") {
    auto P = eval(N.Children[0]);
    if (!ends(P.Type, "*") || P.Type == "void*")
      fail(N.At, "typed object pointer required");
    auto Base = element(P.Type);
    V = {unconst(Base), nullptr, P.IR, Base != unconst(Base)};
    V.Storage = P.Storage;
    V.Generation = P.Generation;
    V.BaseView = P.BaseView;
    if (llvm::isa<llvm::ConstantPointerNull>(P.IR))
      fail(N.At, "null pointer access");
  } else if (N.K == Node::Member) {
    auto Base = N.Definition ? eval(N.Children[0]) : place(N.Children[0]);
    if (N.Definition) {
      if (!ends(Base.Type, "*"))
        fail(N.At, "typed object pointer required");
      auto T = element(Base.Type);
      Base = {unconst(T), nullptr, Base.IR, unconst(T) != T};
    }
    V = member(Base, N.At);
  } else if (N.K == Node::Index) {
    auto Base = eval(N.Children[0]);
    auto Index = eval(N.Children[1]);
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
    V = {unconst(E), nullptr,
         B.CreateInBoundsGEP(Array, Base.Address, {B.getInt32(0), I}),
         Base.Readonly || E != unconst(E)};
  } else
    V = eval(N);
  if (!V.Address)
    fail(N.At, "object lvalue required");
  ensureLive(V, N.At);
  return V;
}
Value Frame::constantEval(const Node &N) {
  if (IR) {
    Frame CF(U, F, nullptr, Prefix);
    CF.Opt = Opt;
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
    else if (U.Constraints.count(Op) || Op == "ObjectType" ||
             Op == "CompleteType")
      return literal(predicate(N), "bool");
    else if (Op == "SameType" && N.TemplateArgs.size() == 2)
      return literal(resolve(N.TemplateArgs[0].Type, N.At) ==
                         resolve(N.TemplateArgs[1].Type, N.At),
                     "bool");
    else
      return load(lookup(N.At));
  case Node::Index:
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
      if (A[0].K == Node::Name && U.Overloads.count(A[0].Text)) {
        if (!ends(Expected, "*") || !U.Signatures.count(element(Expected)))
          fail(N.At, "target function-pointer type required");
        auto &Sig = U.Signatures.at(element(Expected));
        Function *Match = nullptr;
        for (auto *Candidate : U.Overloads.at(A[0].Text)) {
          if (Candidate->Result != Sig.front() ||
              Candidate->Params !=
                  std::vector<std::string>(Sig.begin() + 1, Sig.end()) ||
              (ends(element(Expected), " noexcept>") &&
               !Candidate->Decl.Noexcept))
            continue;
          if (Match)
            fail(N.At, "no unique compatible function");
          Match = Candidate;
        }
        if (!Match)
          fail(N.At, "no unique compatible function");
        return {Expected, checkSelected(Match, N.At)->IR};
      }
      auto V = place(A[0]);
      Value P{(V.Readonly ? "const<" + V.Type + ">" : V.Type) + "*", V.Address};
      P.Storage = V.Storage;
      P.Generation = V.Generation;
      P.BaseView = V.BaseView;
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
      auto Next = binary(Bop, V, literal(1));
      B.CreateStore(Next.IR, D.Address);
      return N.Definition ? Value(V.Type, V.IR)
                          : Value(Next.Type, Next.IR, D.Address);
    }
    auto V = eval(A[0], Op == "-" && A[0].K == Node::Real ? "" : Expected);
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
    auto L = eval(A[0], Propagate ? Expected : "");
    auto R = eval(A[1], Propagate ? Expected : "");
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
          (!ends(To, " noexcept>") || ends(From, " noexcept>")))
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
Function *Frame::select(std::string Name, const Node &N,
                        const std::vector<Value> &Args, Value Receiver) {
  std::string Key =
      !Receiver.Type.empty() ? Receiver.Type + "::" + Name
      : U.Overloads.count(Prefix + Name) || U.Families.count(Prefix + Name)
          ? Prefix + Name
          : Name;
  if (auto It = U.Families.find(Key);
      It != U.Families.end() && It->second.Decl.K == Node::Function) {
    Family Fam = It->second;
    if (!Fam.Decl.Generics.empty() && Fam.Decl.Generics.back().Pack) {
      size_t Fixed = Fam.Decl.Generics.size() - 1;
      size_t FixedParams =
          std::count_if(Fam.Decl.Params.begin(), Fam.Decl.Params.end(),
                        [](auto &P) { return !P.Pack; });
      size_t Count = N.TemplateArgs.size() > Fixed
                         ? N.TemplateArgs.size() - Fixed
                     : Args.size() > FixedParams ? Args.size() - FixedParams
                                                 : 0;
      Fam = expand(Fam, Count, N.At);
    }
    auto S = bind(Fam, N.TemplateArgs, Args, N.At);
    std::string ID = Key + "<";
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
    if (!U.Instances.count(ID)) {
      auto *D = U.declare(Fam.Decl, ID, Fam.Prefix, S);
      U.Instances[ID] = D;
      if (!Fam.Decl.TemplateArgs.empty()) {
        Frame Probe(U, D, nullptr);
        if (llvm::cast<llvm::ConstantInt>(
                Probe.constantEval(Fam.Decl.TemplateArgs[0]).IR)
                ->isZero())
          fail(N.At, "constraint is not satisfied");
      }
      U.emit(*D);
    }
    return checkSelected(U.Instances.at(ID), N.At);
  }
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
    return Strict;
  };
  std::vector<Candidate> Best;
  auto It = U.Overloads.find(Key);
  if (It == U.Overloads.end())
    fail(N.At, "unknown name '" + Name + "'");
  for (auto *D : It->second) {
    if (!Receiver.Type.empty()) {
      auto Q = D->Decl.Settings.find("category");
      if (Q != D->Decl.Settings.end() && !Q->second.empty() &&
          Q->second != (Receiver.Expiring ? "&&" : "&"))
        continue;
      if (Receiver.Readonly && !D->Decl.Const && D->Decl.K == Node::Function)
        continue;
    }
    if (Args.size() > D->Params.size() ||
        (Args.size() < D->Params.size() &&
         D->Decl.Params[Args.size()].Children.empty()))
      continue;
    Candidate Current{D, {unsigned(D->Decl.Const && !Receiver.Readonly)}};
    for (size_t I = 0; I < Args.size(); ++I) {
      auto Rank = conversionRank(Args[I], D->Params[I], N.At);
      if (!Rank)
        break;
      Current.Ranks.push_back(*Rank);
    }
    if (Current.Ranks.size() != Args.size() + 1 ||
        llvm::any_of(Best,
                     [&](const Candidate &C) { return Better(C, Current); }))
      continue;
    llvm::erase_if(Best,
                   [&](const Candidate &C) { return Better(Current, C); });
    Best.push_back(std::move(Current));
  }
  if (Best.size() != 1)
    fail(N.At, Best.empty() ? "no viable overload" : "ambiguous overload");
  return checkSelected(Best.front().Decl, N.At);
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
Value Frame::invoke(Function &D, std::vector<Value> Actual, const Token &T,
                    Value Receiver) {
  std::vector<llvm::Value *> Values;
  if (!D.Owner.empty())
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
    auto V = I < Actual.size()
                 ? Actual[I]
                 : construct(unconst(baseRef(Ty)), P.Children, P.At);
    if (ends(Ty, "&")) {
      V = bindReference(V, Ty, P.At);
    } else {
      V = convert(V, Ty, T);
      V = materialize(V, T);
      if (Defaults && !Constant) {
        auto *Addr = allocate(Ty, P.At);
        B.CreateStore(V.IR, Addr);
        V = {Ty, nullptr, Addr};
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
  llvm::CallInst *Call = nullptr;
  if (D.Slot >= 0) {
    auto &R = U.Records.at(D.Owner);
    auto *Vptr = B.CreateStructGEP(R.IR, Receiver.Address, R.Fields.size());
    auto *Table = B.CreateLoad(B.getPtrTy(), Vptr);
    auto *Slot = B.CreateGEP(B.getPtrTy(), Table, B.getInt32(D.Slot));
    Call = B.CreateCall(D.IR->getFunctionType(),
                        B.CreateLoad(B.getPtrTy(), Slot), Values);
  } else
    Call = B.CreateCall(D.IR, Values);
  Call->setAttributes(D.IR->getAttributes());
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
      if (V != I->Names.end() && U.Records.count(V->second.Type) &&
          U.Records.at(V->second.Type).Decl.K == Node::Lambda)
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
  if (U.Cases.count(Prefix + Name))
    return variant(U.Cases.at(Prefix + Name), Args, C.At);
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
  if ((Name == "destroy_base" || Name == "abandon_base") && Args.size() == 1 &&
      C.TemplateArgs.size() == 1) {
    if (!F || F->Decl.K != Node::Destructor || Args[0].K != Node::Name ||
        Args[0].Text != "this" || !InlineReturn)
      fail(C.At, "base request requires the current destructor layer");
    auto Slot = "$base:" + resolve(C.TemplateArgs[0].Type, C.At);
    endField(Slot, C.At, Name == "destroy_base", true);
    cleanup(0);
    branch(InlineReturn);
    B.SetInsertPoint(block("unreachable"));
    Live = false;
    return {"void"};
  }
  if (!FieldFlags.empty() && Args.size() == 1 &&
      (Name == "destroy" || Name == "abandon")) {
    auto Slot = directField(Args[0]);
    if (!Slot.empty()) {
      endField(Slot, C.At, Name == "destroy", true);
      return {"void"};
    }
  }
  if ((Name == "destroy" || Name == "abandon" || Name == "storage_of") &&
      Args.size() == 1) {
    auto V = place(Args[0]);
    if (V.Storage.empty())
      fail(C.At, "automatic storage extent required");
    if (Name == "storage_of") {
      Value S{"storage", V.Address};
      S.Storage = V.Storage;
      return S;
    }
    if (!Extents.count(V.Storage))
      fail(C.At, "local storage extent required");
    if (V.BaseView && Extents.at(V.Storage).Type != V.Type &&
        (!U.Records.count(V.Type) || !U.Records.at(V.Type).VirtualDestructor))
      fail(C.At,
           "complete destruction through a base requires virtual destruction");
    retireStorage(V, Name == "destroy");
    return {"void"};
  }
  if (Name == "construct_at" && !Args.empty() && C.TemplateArgs.size() == 1) {
    auto S = eval(Args[0]);
    if (S.Type != "storage" || S.Storage.empty())
      fail(C.At, "storage view required");
    if (Active[S.Storage] == 1)
      fail(C.At, "storage contains a live generation");
    if (Active[S.Storage] < 0 && Registrations.count(S.Storage))
      guard(B.CreateTrunc(
          B.CreateLoad(B.getInt64Ty(), Registrations.at(S.Storage).Stamp),
          B.getInt1Ty()));
    auto T = resolve(C.TemplateArgs[0].Type, C.At);
    auto *Alloca =
        Extents.count(S.Storage)
            ? llvm::dyn_cast<llvm::AllocaInst>(Extents.at(S.Storage).Address)
            : nullptr;
    auto &DL = U.M.getDataLayout();
    if (!Alloca ||
        DL.getABITypeAlign(Alloca->getAllocatedType()) <
            DL.getABITypeAlign(U.ir(T)) ||
        DL.getTypeAllocSize(Alloca->getAllocatedType()) <
            DL.getTypeAllocSize(U.ir(T)))
      fail(C.At, "insufficient storage capacity");
    construct(T, {Args.begin() + 1, Args.end()}, C.At, S.IR);
    replaceGeneration(S, T, C.At);
    Value V{T + "*", S.IR};
    V.Storage = S.Storage;
    V.Generation =
        B.CreateLoad(B.getInt64Ty(), Registrations.at(S.Storage).Stamp);
    return V;
  }
  if (C.K == Node::Name &&
      (builtin(Name) || Env.Types.count(Name) ||
       U.Aliases.count(Prefix + Name) || U.Records.count(Name) ||
       U.Records.count(Prefix + Name))) {
    return construct(resolve(Name, C.At), Args, C.At);
  }
  if (Receiver.Type.empty() && !Self.Type.empty() &&
      !methodOwner(Self.Type, C.At).empty())
    Receiver = Self;
  if (!Receiver.Type.empty()) {
    auto Owner = methodOwner(Receiver.Type, C.At);
    if (!Owner.empty() && Owner != Receiver.Type)
      adjust(Receiver, Owner, C.At);
  }
  std::vector<Value> V;
  auto Key = Receiver.Type.empty()
                 ? (U.Overloads.count(Prefix + Name) ? Prefix + Name : Name)
                 : Receiver.Type + "::" + Name;
  auto Group = U.Overloads.find(Key);
  for (size_t I = 0; I < Args.size(); ++I) {
    std::string Expected;
    if (Group != U.Overloads.end() && Group->second.size() == 1 &&
        I < Group->second[0]->Params.size())
      Expected = Group->second[0]->Params[I];
    V.push_back(eval(Args[I], Expected));
  }
  auto *D = select(Name, C, V, Receiver);
  return invoke(*D, V, C.At, Receiver);
}
Value Frame::construct(const std::string &T, const std::vector<Node> &Args,
                       const Token &At, llvm::Value *Dest, const Node *Tail) {
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
  if (U.Variants.count(T)) {
    Value V;
    if (Args.size() == 1)
      V = convert(eval(Args[0]), T, At);
    else if (Args.empty() && U.DefaultCase.count(T))
      V = variant(U.Cases.at(U.DefaultCase.at(T)), {}, At);
    else
      fail(At, "union construction requires a selected case");
    if (Dest)
      B.CreateStore(V.IR, Dest);
    return V;
  }
  if (U.Records.count(T)) {
    if (!IR)
      fail(At, "constant record construction is unavailable");
    auto *Ptr = Dest ? Dest : allocate(T, At);
    Value Obj{T, nullptr, Ptr};
    auto &R = U.Records.at(T);
    std::vector<Value> Actual;
    for (auto &A : Args)
      Actual.push_back(eval(A));
    std::map<std::string, const Node *> Producers;
    if (Tail)
      for (auto &S : Tail->Children)
        if (S.K == Node::Init && !Producers.emplace(S.Text, &S).second)
          fail(S.At, "duplicate initialization producer");
    if (Actual.size() == 1 && Actual[0].Type == T) {
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
        if (Producers.empty())
          invoke(*D, Actual, At, Obj);
        else {
          Frame Root(U, D, IR);
          Root.B.SetInsertPoint(B.GetInsertBlock());
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
              materialize(V, At, Addr);
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
        if (Actual.size() + R.Bases.size() > R.Fields.size())
          fail(At, "too many aggregate initializers");
        if (R.Bases.empty())
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
        for (size_t I = 0; I < R.Fields.size(); ++I) {
          auto &Field = R.Fields[I];
          auto *P = B.CreateStructGEP(R.IR, Ptr, I);
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
                      At, P);
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
void Frame::drop(Value V) {
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
  if (ends(V.Type, "]")) {
    auto E = element(V.Type);
    if (!U.Records.count(E) && !ends(E, "]"))
      return;
    auto *Ty = llvm::cast<llvm::ArrayType>(U.ir(V.Type));
    for (size_t I = Ty->getNumElements(); I; --I)
      drop({E, nullptr,
            B.CreateInBoundsGEP(Ty, V.Address,
                                {B.getInt32(0), B.getInt64(I - 1)})});
    return;
  }
  if (!U.Records.count(V.Type))
    return;
  if (auto It = U.Overloads.find(V.Type + "::$drop"); It != U.Overloads.end()) {
    B.CreateCall(It->second.front()->IR, {V.Address});
    return;
  }
  auto &R = U.Records.at(V.Type);
  for (size_t I = R.Fields.size(); I; --I) {
    auto &F = R.Fields[I - 1];
    drop({F.Type, nullptr, B.CreateStructGEP(R.IR, V.Address, I - 1)});
  }
}
void Frame::cleanup(size_t From) {
  for (size_t I = Scopes.size(); I > From; --I)
    for (auto V = Scopes[I - 1].Drops.rbegin(); V != Scopes[I - 1].Drops.rend();
         ++V)
      drop(*V);
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
    if (Simple) {
      auto V = construct(Ty, Args, N.At);
      G->setInitializer(llvm::cast<llvm::Constant>(V.IR));
      G->setConstant(N.Const);
      names()[Name] = {Ty, N.Required ? V.IR : nullptr, G, N.Const};
      return;
    }
    auto FT = llvm::FunctionType::get(B.getVoidTy(), false);
    auto *Fn = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                      "cpn.static.init", U.M);
    Frame Init(U, nullptr, Fn, Prefix);
    Init.Env = Env;
    Init.B.SetInsertPoint(Init.block("entry"));
    Init.construct(Ty, Args, N.At, G, Tail);
    Init.endExpression();
    auto *Ready = new llvm::GlobalVariable(U.M, B.getInt1Ty(), false,
                                           llvm::GlobalValue::InternalLinkage,
                                           B.getFalse(), "cpn.ready");
    U.Ready[G] = Ready;
    Init.B.CreateStore(B.getTrue(), Ready);
    Init.B.CreateRetVoid();
    U.Startup.push_back(Fn);
    names()[Name] = {Ty, nullptr, G, N.Const};
    if (U.Records.count(Ty) || ends(Ty, "]")) {
      auto *D = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                       "cpn.static.drop", U.M);
      Frame DF(U, nullptr, D);
      DF.B.SetInsertPoint(DF.block("entry"));
      DF.drop(names()[Name]);
      DF.B.CreateRetVoid();
      U.Shutdown.push_back(D);
    }
    return;
  }
  if (ends(Ty, "&")) {
    if (Args.size() != 1)
      fail(N.At, "reference requires one initializer");
    auto V = place(Args[0]);
    auto E = baseRef(Ty);
    if (unconst(E) != V.Type)
      fail(N.At, "incompatible reference binding");
    V.Readonly |= N.Const || E != unconst(E);
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
  Cell.Storage = V.Storage;
  Cell.Generation = V.Generation;
  Cell.BaseView = V.BaseView;
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
  std::vector<std::vector<unsigned>> Paths;
  std::function<void(const std::string &, std::vector<unsigned>)> Walk =
      [&](const std::string &Cur, std::vector<unsigned> P) {
        if (Cur == T) {
          Paths.push_back(std::move(P));
          return;
        }
        auto &Bases = U.Records.at(Cur).Bases;
        for (size_t I = 0; I < Bases.size(); ++I) {
          auto Next = P;
          Next.push_back(I);
          Walk(Bases[I], std::move(Next));
        }
      };
  Walk(V.Type, {});
  if (Paths.empty())
    return false;
  if (Paths.size() != 1) {
    if (!Emit)
      return false;
    fail(At, "ambiguous inherited base conversion");
  }
  if (Emit) {
    std::vector<llvm::Value *> Indices{B.getInt32(0)};
    for (auto I : Paths[0])
      Indices.push_back(B.getInt32(I));
    V.Address = B.CreateGEP(U.ir(V.Type), V.Address, Indices);
    V.IR = nullptr;
    V.Type = T;
  }
  return true;
}
