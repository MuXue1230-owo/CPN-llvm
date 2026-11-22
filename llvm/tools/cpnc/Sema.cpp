#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace cpn;
using llvm::StringRef;
std::vector<std::string> cpn::splitArguments(StringRef S) {
  std::vector<std::string> Out;
  unsigned Depth = 0;
  size_t Start = 0;
  for (size_t I = 0; I < S.size(); ++I) {
    char C = S[I];
    if (C == '<' || C == '(' || C == '[')
      ++Depth;
    else if (C == '>' || C == ')' || C == ']') {
      if (Depth)
        --Depth;
    } else if (C == ',' && !Depth) {
      Out.push_back(S.slice(Start, I).str());
      Start = I + 1;
    }
  }
  if (Start < S.size())
    Out.push_back(S.drop_front(Start).str());
  return Out;
}
namespace {
std::string appliedName(std::string Name, const Family &Family,
                        const Substitution &S) {
  Name += "<";
  for (auto &G : Family.Decl.Generics) {
    if (G.K == Node::TypeParam)
      Name += S.Types.at(G.Text);
    else {
      llvm::SmallString<32> Buf;
      llvm::cast<llvm::ConstantInt>(S.Values.at(G.Text).IR)
          ->getValue()
          .toString(Buf, 10, signedType(G.Type));
      Name += Buf.str();
    }
    Name += ",";
  }
  return Name + ">";
}
} // namespace
std::string cpn::element(const std::string &T) {
  if (StringRef(T).ends_with("]"))
    return T.substr(0, T.rfind('['));
  return T.empty() ? T : T.substr(0, T.size() - 1);
}
std::string cpn::unconst(const std::string &T) {
  return StringRef(T).starts_with("const<") && StringRef(T).ends_with(">")
             ? T.substr(6, T.size() - 7)
             : T;
}
std::string cpn::qualifyConst(const std::string &T) {
  if (StringRef(T).ends_with("]")) {
    auto Extent = T.rfind('[');
    return qualifyConst(T.substr(0, Extent)) + T.substr(Extent);
  }
  if (StringRef(T).ends_with("&")) {
    auto Ref = T.find_last_not_of('&') + 1;
    return qualifyConst(T.substr(0, Ref)) + T.substr(Ref);
  }
  return unconst(T) == T ? "const<" + T + ">" : T;
}
llvm::Type *Context::ir(const std::string &T, const Token &At) {
  if (auto Mutable = unconst(T); Mutable != T)
    return ir(Mutable, At);
  if (T == "f32")
    return llvm::Type::getFloatTy(C);
  if (T == "f64")
    return llvm::Type::getDoubleTy(C);
  if (T == "void" || T == "never")
    return llvm::Type::getVoidTy(C);
  if (T == "nullptr_t")
    return llvm::Type::getInt8Ty(C);
  if (T == "storage" || StringRef(T).ends_with("*") ||
      StringRef(T).ends_with("&"))
    return llvm::PointerType::getUnqual(C);
  if (integer(T) || T == "bool" || T == "char") {
    unsigned Bits = width(T);
    if (Bits)
      return llvm::IntegerType::get(C, Bits);
  }
  if (StringRef(T).ends_with("]")) {
    auto I = T.rfind('[');
    uint64_t N = 0;
    if (I == std::string::npos ||
        StringRef(T).slice(I + 1, T.size() - 1).getAsInteger(10, N))
      fail(At, "invalid array extent");
    auto *Element = ir(T.substr(0, I), At);
    if (Element->isStructTy() && !Element->isSized())
      fail(At, "incomplete record element");
    if (!llvm::ArrayType::isValidElementType(Element) || !Element->isSized())
      fail(At, "array requires a complete object element type");
    // Empty arrays reserve addressable, element-aligned storage on this target.
    return llvm::ArrayType::get(Element, std::max<uint64_t>(1, N));
  }
  if (Signatures.count(T))
    fail(At, "function type requires a pointer");
  if (Enums.count(T))
    return ir(Enums.at(T), At);
  if (Records.count(T))
    return Records.at(T).IR;
  fail(At, "unsupported or unknown type '" + T + "'");
}
Frame::Frame(Context &U, Function *F, llvm::Function *IR, std::string P)
    : U(U), F(F), B(U.M), Opt(F ? F->Definition.Configuration : U.Opt),
      LookupLimit(F ? F->Definition.Through : U.site().Through),
      Prefix(F ? F->Prefix : std::move(P)), IR(IR),
      Env(F ? F->Env : Substitution()) {
  Scopes.emplace_back();
  TracksStorage = IR && U.SlotType;
}
llvm::BasicBlock *Frame::block(llvm::StringRef Name) {
  return llvm::BasicBlock::Create(U.C, Name, IR);
}
void Frame::branch(llvm::BasicBlock *Dest) {
  if (!B.GetInsertBlock()->hasTerminator())
    B.CreateBr(Dest);
}
llvm::AllocaInst *Frame::allocate(const std::string &T, const Token &At) {
  auto *Ty = U.ir(T, At);
  if (!Ty->isSized())
    fail(At, "object requires a complete object type");
  llvm::IRBuilder<> Entry(IR->getEntryBlock().begin());
  auto *Ptr = Entry.CreateAlloca(Ty);
  Ptr->setMetadata("cpn.object", llvm::MDNode::get(U.C, {}));
  return Ptr;
}
cpn::Value Frame::load(cpn::Value V) {
  if (!IR && V.Location) {
    auto Current = V.Location->read(*this, {});
    Current.Readonly |= V.Readonly;
    Current.Expiring = V.Expiring;
    Current.Prvalue = V.Prvalue;
    Current.Location = V.Location;
    Current.ConstantTemporary = V.ConstantTemporary;
    V = std::move(Current);
  }
  if (V.Type != "storage" && !StringRef(V.Type).ends_with("*"))
    ensureLive(V, {});
  if (V.Address && U.Ready.count(V.Address)) {
    if (!IR)
      fail({}, "dynamic static read is unavailable in a constant expression");
    guard(B.CreateNot(B.CreateLoad(B.getInt1Ty(), U.Ready.at(V.Address))));
  }
  if (IR && V.Address && !U.Ready.count(V.Address))
    U.checkStaticRead(B, V.Address);
  if (IR && V.Address &&
      (!V.IR || llvm::isa<llvm::GlobalVariable>(V.Address)) && !V.BoundsCell &&
      carriesPointerBounds(V.Type))
    V.BoundsCell = storedPointerCell(V.Address);
  if (!V.IR && V.Address && !StringRef(V.Type).ends_with("]")) {
    if (!IR) {
      if (auto *Address = llvm::dyn_cast<llvm::Constant>(V.Address)) {
        auto *Object = llvm::dyn_cast<llvm::GlobalVariable>(
            llvm::getUnderlyingObject(Address));
        if (Object && U.ConstantObjects.count(Object))
          V.IR = llvm::ConstantFoldLoadFromConstPtr(Address, U.ir(V.Type),
                                                    U.M.getDataLayout());
      }
      if (!V.IR || llvm::isa<llvm::UndefValue>(V.IR))
        fail({}, "constant expression required");
      return V;
    }
    V.IR = U.Records.count(V.Type) && U.Records.at(V.Type).VirtualCount
               ? snapshot(V)
               : B.CreateLoad(U.ir(V.Type), V.Address);
  }
  if (V.BoundsCell && IR)
    readBounds(V, V.BoundsCell);
  return V;
}
void Frame::readBounds(Value &V, llvm::Value *Cell) {
  auto *Meta = pointerMetadataType();
  auto read = [&](unsigned I) {
    return B.CreateLoad(Meta->getElementType(I),
                        B.CreateStructGEP(Meta, Cell, I));
  };
  V.Lower = read(0);
  V.Upper = read(1);
  if (TracksStorage) {
    V.ArraySlot = read(2);
    V.ArrayGeneration = read(3);
    V.Slot = read(4);
    V.Generation = read(5);
  }
}
llvm::StructType *Frame::pointerMetadataType() {
  auto *P = B.getPtrTy();
  auto *I = B.getInt64Ty();
  return TracksStorage ? llvm::StructType::get(U.C, {P, P, P, I, P, I})
                       : llvm::StructType::get(U.C, {P, P});
}
void Frame::saveBounds(llvm::Value *Cell, Value V) {
  auto *Meta = pointerMetadataType();
  auto write = [&](unsigned I, llvm::Value *Val) {
    B.CreateStore(Val ? Val
                      : llvm::Constant::getNullValue(Meta->getElementType(I)),
                  B.CreateStructGEP(Meta, Cell, I));
  };
  write(0, V.Lower);
  write(1, V.Upper);
  if (TracksStorage) {
    write(2, V.ArraySlot);
    write(3, V.ArrayGeneration);
    write(4, V.Slot);
    write(5, V.Generation);
  }
}
std::string
cpn::scopeKey(StringRef Prefix, StringRef Name,
              llvm::function_ref<bool(const std::string &)> Contains) {
  if (Name.consume_front("::"))
    Prefix = {};
  while (true) {
    auto Key = (Prefix + Name).str();
    if (Contains(Key))
      return Key;
    if (Prefix.empty())
      return {};
    Prefix = Prefix.drop_back(2);
    auto Sep = Prefix.rfind("::");
    Prefix = Sep == StringRef::npos ? StringRef() : Prefix.take_front(Sep + 2);
  }
}
static void requireBorrowable(const std::string &T, const Token &At,
                              bool Result) {
  auto Type = unconst(T);
  if (!StringRef(Type).ends_with("&") && !StringRef(Type).ends_with("*"))
    fail(At,
         Result ? "borrowed return requires a pointer or reference result"
                : "borrow contract must name a pointer or reference parameter");
}
std::string cpn::parameterEffects(const std::set<unsigned> &NoEscape,
                                  const std::set<unsigned> &Borrowed,
                                  const std::set<unsigned> &Consumes) {
  std::string Effects;
  auto append = [&](StringRef Key, const std::set<unsigned> &Positions) {
    for (auto I : Positions)
      Effects += (" " + Key + "#").str() + std::to_string(I);
  };
  append("noescape", NoEscape);
  append("borrow", Borrowed);
  append("consumes", Consumes);
  return Effects;
}
std::string Context::callableType(const Function &D) {
  std::string T = "function<" + D.Result + "(";
  for (size_t I = 0; I < D.Params.size(); ++I) {
    if (I)
      T += ",";
    T += D.Params[I];
  }
  T += ")";
  if (D.Decl.Noexcept)
    T += " noexcept";
  if (D.MayWhole)
    T += " whole";
  T += parameterEffects(D.NoEscape, D.BorrowedResult, D.Consumes) + ">";
  if (!Signatures.count(T)) {
    std::vector<std::string> Sig{D.Result};
    Sig.insert(Sig.end(), D.Params.begin(), D.Params.end());
    Signatures.emplace(T, std::move(Sig));
  }
  return T;
}
std::set<StringRef> cpn::callableFlags(StringRef T) {
  llvm::SmallVector<StringRef> Parts;
  T.drop_back().drop_front(T.rfind(')') + 1).split(Parts, ' ', -1, false);
  return {Parts.begin(), Parts.end()};
}
bool Context::compatibleCallable(const std::string &From,
                                 const std::string &To) const {
  if (!Signatures.count(From) || !Signatures.count(To) ||
      Signatures.at(From) != Signatures.at(To))
    return false;
  if ((callableFlag(To, " noexcept") && !callableFlag(From, " noexcept")) ||
      (callableFlag(From, " whole") && !callableFlag(To, " whole")))
    return false;
  auto Source = callableFlags(From), Target = callableFlags(To);
  for (auto Flag : Target)
    if ((Flag.starts_with("noescape#") || Flag.starts_with("consumes#")) &&
        !Source.count(Flag))
      return false;
  // A caller and its target must agree on which ownership obligations transfer.
  for (auto Flag : Source)
    if (Flag.starts_with("consumes#") && !Target.count(Flag))
      return false;
  if (llvm::any_of(Target,
                   [](StringRef F) { return F.starts_with("borrow#"); })) {
    bool Bounded = false;
    for (auto F : Source)
      if (F.starts_with("borrow#")) {
        Bounded = true;
        if (!Target.count(F))
          return false;
      }
    if (!Bounded)
      return false;
  }
  return true;
}
// Split at the last qualification outside generic arguments. Constant
// arguments can contain parenthesized shifts and comparisons.
std::optional<std::string> Frame::memberQualifier(const std::string &S,
                                                  const Token &At,
                                                  std::string &Tail) {
  size_t Member = std::string::npos;
  unsigned Depth = 0, Parens = 0;
  for (size_t I = 0; I + 1 < S.size(); ++I) {
    if (S[I] == '(')
      ++Parens;
    else if (S[I] == ')' && Parens)
      --Parens;
    else if (!Parens && S[I] == '<')
      ++Depth;
    else if (!Parens && S[I] == '>' && Depth)
      --Depth;
    else if (!Parens && !Depth && S[I] == ':' && S[I + 1] == ':' && I)
      Member = I;
  }
  if (Member != std::string::npos) {
    auto Qualifier = S.substr(0, Member);
    auto Head = StringRef(Qualifier).split('<').first;
    if (Env.Types.count(Qualifier) ||
        llvm::any_of(Scopes,
                     [&](const auto &Scope) {
                       return Scope.Aliases.count(Qualifier);
                     }) ||
        !scopeKey(Prefix, Head, [&](const std::string &K) {
           return U.Records.count(K) || U.Aliases.count(K) ||
                  U.Families.count(K);
         }).empty()) {
      Tail = S.substr(Member + 2);
      return resolve(Qualifier, At);
    }
  }
  return {};
}
std::string Frame::resolve(std::string S, const Token &At) {
  if (auto Q = U.TypeQueries.find(S); Q != U.TypeQueries.end())
    return unevaluatedType(Q->second.Children.front(), true);
  if (StringRef(S).starts_with("function<") && StringRef(S).ends_with(">")) {
    size_t Open = 9, Close = S.rfind(')');
    unsigned Depth = 0;
    for (; Open < S.size(); ++Open) {
      if (S[Open] == '(' && !Depth)
        break;
      if (S[Open] == '<')
        ++Depth;
      if (S[Open] == '>' && Depth)
        --Depth;
    }
    if (Open >= S.size() || Close == std::string::npos || Close < Open)
      fail(At, "invalid function type");
    std::vector<std::string> Sig = {resolve(S.substr(9, Open - 9), At)};
    for (auto &P : splitArguments(StringRef(S).slice(Open + 1, Close)))
      Sig.push_back(unconst(resolve(P, At)));
    auto Canonical = "function<" + Sig.front() + "(";
    for (size_t I = 1; I < Sig.size(); ++I) {
      if (I > 1)
        Canonical += ",";
      Canonical += Sig[I];
    }
    Canonical += S.substr(Close);
    for (auto Flag : callableFlags(Canonical)) {
      bool Result = Flag.consume_front("borrow#");
      bool Consuming = Flag.consume_front("consumes#");
      if (!Result && !Consuming && !Flag.consume_front("noescape#"))
        continue;
      unsigned Position;
      if (Flag.getAsInteger(10, Position) || Position >= Sig.size() - 1)
        fail(At, "unknown borrow-contract parameter");
      if (Result)
        requireBorrowable(Sig.front(), At, true);
      if (!Consuming)
        requireBorrowable(Sig[Position + 1], At, false);
    }
    U.Signatures.try_emplace(Canonical, std::move(Sig));
    return Canonical;
  }
  if (StringRef(S).starts_with("::") && builtin(StringRef(S).drop_front(2)))
    S.erase(0, 2);
  if (S == "byte")
    S = "u8";
  if (floating(S) && !Opt.FloatFormats.count(S))
    fail(At, "CFG002: floating format " + S + " is disabled");
  if (integer(S) && S != "integer" && !StringRef(S).ends_with("size") &&
      !Opt.IntegerWidths.count(width(S)))
    fail(At, "CFG002: integer type " + S + " is disabled");
  if (builtin(S) || S == "auto")
    return S;
  for (auto I = Scopes.rbegin(); I != Scopes.rend(); ++I) {
    if (auto Alias = I->Aliases.find(S); Alias != I->Aliases.end())
      return Alias->second;
    if (I->Names.count(S))
      fail(At, "object name '" + S + "' does not name a type");
  }
  if (auto I = Env.Types.find(S); I != Env.Types.end())
    return I->second;
  if (StringRef(S).ends_with("]")) {
    auto I = S.rfind('[');
    auto N = constantEval(
        parseExpression(StringRef(S).slice(I + 1, S.size() - 1), Opt));
    auto *C = llvm::dyn_cast_or_null<llvm::ConstantInt>(N.IR);
    if (!C || (signedType(N.Type) && C->isNegative()) ||
        C->getValue().getActiveBits() > 31)
      fail(At, "array extent is outside the range of nonnegative extents");
    return resolve(S.substr(0, I), At) + "[" +
           std::to_string(C->getZExtValue()) + "]";
  }
  if (StringRef(S).ends_with("&") || StringRef(S).ends_with("*"))
    return resolve(element(S), At) + S.back();
  if (StringRef(S).starts_with("const<") && StringRef(S).ends_with(">"))
    return qualifyConst(resolve(S.substr(6, S.size() - 7), At));
  if (StringRef(S).starts_with("forward ")) {
    auto T = resolve(S.substr(8), At);
    return StringRef(T).ends_with("&") ? T : T + "&&";
  }
  std::string Tail;
  if (auto Owner = memberQualifier(S, At, Tail)) {
    auto Key = *Owner + "::" + Tail.substr(0, Tail.find('<'));
    auto It = U.MemberTypes.find(Key);
    if (It == U.MemberTypes.end())
      fail(At, "unknown nested type '" + Tail + "'");
    checkAccess(It->second.second, *Owner, At);
    if (U.Aliases.count(Key))
      return U.Aliases.at(Key);
    if (U.Records.count(Key) || U.Enums.count(Key))
      return Key;
    // Instantiate a nested family using the fully resolved owning scope.
    llvm::SaveAndRestore Scope(Prefix, *Owner + "::");
    return resolve(Tail, At);
  }
  auto Base = S.substr(0, S.find('<'));
  auto Key = scopeKey(Prefix, Base, [&](const std::string &K) {
    return U.Aliases.count(K) || U.Records.count(K) || U.Enums.count(K) ||
           U.Families.count(K);
  });
  if (!Key.empty()) {
    if (auto It = U.MemberTypes.find(Key); It != U.MemberTypes.end())
      checkAccess(It->second.second, It->second.first, At);
    if (U.Families.count(Key) && S.find('<') != std::string::npos) {
      auto Fam = U.Families.at(Key);
      std::vector<Node> Explicit;
      auto Parts =
          splitArguments(StringRef(S).slice(S.find('<') + 1, S.size() - 1));
      if (!Fam.Decl.Generics.empty() && Fam.Decl.Generics.back().Pack) {
        auto Fixed = Fam.Decl.Generics.size() - 1;
        Fam = expand(Fam, Parts.size() > Fixed ? Parts.size() - Fixed : 0, At);
      }
      for (size_t I = 0; I < Parts.size(); ++I) {
        if (I >= Fam.Decl.Generics.size())
          fail(At, "too many generic arguments");
        if (Fam.Decl.Generics[I].K == Node::TypeParam) {
          Node A(Node::TypeArg, At);
          A.Type = Parts[I];
          Explicit.push_back(A);
        } else
          Explicit.push_back(parseExpression(Parts[I], Opt));
      }
      auto E = bind(Fam, Explicit, {}, At);
      auto Full = appliedName(Key, Fam, E);
      if (!U.Records.count(Full)) {
        selectTypeSpecialization(Key, Fam, E, At);
        EnterDefinition Site(U, Fam.Site);
        llvm::SaveAndRestore Depth(U.SpecializationDepth,
                                   U.SpecializationDepth + 1);
        if (U.SpecializationDepth > 128)
          throw ResourceExhausted{
              {At, "generic specialization nesting resource exhausted"}};
        U.chargeInstance(At);
        Frame Probe(U, nullptr, nullptr, Fam.Prefix);
        Probe.Env = E;
        if (!Fam.Decl.Params.empty() &&
            !llvm::cast<llvm::ConstantInt>(
                 Probe.constantEval(Fam.Decl.Params[0]).IR)
                 ->getZExtValue())
          fail(At, "constraint is not satisfied");
        if (Fam.Decl.K == Node::Union)
          U.tagged(Fam.Decl, Full, Fam.Prefix, E);
        else
          U.record(Fam.Decl, Full, Fam.Prefix, E);
      }
      return Full;
    }
    if (U.Aliases.count(Key))
      return U.Aliases.at(Key);
    if (U.Records.count(Key) || U.Enums.count(Key))
      return Key;
  }
  fail(At, "unsupported or unknown type '" + S + "'");
}
Substitution Frame::bind(const Family &Fam, const std::vector<Node> &Explicit,
                         const std::vector<cpn::Value> &Actual,
                         const Token &At) {
  auto Reject = [&](const std::string &Why) {
    throw DeductionFailure{{At, Why}};
  };
  Substitution S = Fam.Enclosing;
  auto &G = Fam.Decl.Generics;
  if (Explicit.size() > G.size())
    Reject("too many generic arguments");
  for (size_t I = 0; I < G.size(); ++I) {
    auto &P = G[I];
    Frame Defaults(U, nullptr, nullptr, Fam.Prefix);
    Defaults.Env = S;
    Defaults.Opt = Fam.Site.Configuration;
    Defaults.LookupLimit = Fam.Site.Through;
    const Node *A = I < Explicit.size() ? &Explicit[I] : nullptr;
    if (P.K == Node::TypeParam) {
      if (A) {
        if (A->K != Node::TypeArg)
          Reject("expected a type argument");
        S.Types[P.Text] = resolve(A->Type, At);
      } else {
        for (size_t J = 0; J < Actual.size() && J < Fam.Decl.Params.size();
             ++J) {
          auto Formal = Fam.Decl.Params[J].Type, Ty = Actual[J].Type;
          if (StringRef(Formal).starts_with("forward ")) {
            Formal = Formal.substr(8);
            if (Actual[J].Address && !Actual[J].Expiring)
              Ty += "&";
          }
          while (StringRef(Formal).ends_with("&"))
            Formal.pop_back();
          if (StringRef(Formal).starts_with("const<") &&
              StringRef(Formal).ends_with(">"))
            Formal = Formal.substr(6, Formal.size() - 7);
          while (StringRef(Formal).ends_with("*") &&
                 StringRef(Ty).ends_with("*")) {
            Formal.pop_back();
            Ty.pop_back();
          }
          if (Formal == P.Text) {
            if (Ty == "real")
              Ty = Opt.DefaultReal;
            if (Ty == "integer")
              Ty = Opt.DefaultInt;
            if (S.Types.count(P.Text) && S.Types[P.Text] != Ty)
              Reject("conflicting deduction");
            S.Types[P.Text] = Ty;
          }
        }
        if (!S.Types.count(P.Text) && !P.Children.empty()) {
          auto Ty = P.Children[0].Type;
          S.Types[P.Text] = Defaults.resolve(Ty, At);
        }
        if (!S.Types.count(P.Text))
          Reject("cannot deduce generic type");
      }
    } else {
      if (A && A->K == Node::TypeArg)
        Reject("expected a constant argument");
      if (!A && !P.Children.empty())
        A = &P.Children[0];
      if (!A)
        Reject("missing generic constant");
      auto Ty = Defaults.resolve(P.Type, At);
      if (!integer(Ty) && Ty != "bool" && Ty != "char" && !U.Enums.count(Ty))
        fail(P.At, "invalid generic constant parameter type");
      auto V =
          I < Explicit.size() ? constantEval(*A) : Defaults.constantEval(*A);
      S.Values[P.Text] = convert(V, Ty, At);
    }
  }
  return S;
}
static void checkOperator(const Function &F, const Context &U) {
  auto Op = StringRef(F.Decl.Text).drop_front(8);
  bool Member = !F.Owner.empty();
  bool Assignment =
      Op.ends_with("=") && Op != "==" && Op != "!=" && Op != "<=" && Op != ">=";
  if (F.Decl.Settings.count("static") || F.Decl.Foreign)
    fail(F.Decl.At, "operators require native nominal operands");
  if ((Assignment || Op == "()" || Op == "[]") && !Member)
    fail(F.Decl.At,
         "assignment, call and index operators require a nonstatic member");
  bool Nominal = Member;
  for (auto P : F.Params) {
    while (StringRef(P).ends_with("&"))
      P.pop_back();
    if (StringRef(P).starts_with("const<") && P.back() == '>')
      P = P.substr(6, P.size() - 7);
    Nominal |= U.Records.count(P) != 0;
  }
  if (!Nominal)
    fail(F.Decl.At, "operator requires a nominal operand");
  unsigned Arity = F.Params.size() + unsigned(Member);
  if (Op.starts_with(" ")) {
    std::string T = F.Owner;
    if (!Member && Arity == 1 && StringRef(F.Params[0]).ends_with("&"))
      T = F.Params[0].substr(0, F.Params[0].size() - 1);
    if (Arity != 1 || !U.Records.count(T) || F.Decl.Const ||
        (F.Decl.Settings.count("category") &&
         F.Decl.Settings.at("category") == "&&") ||
        F.Result != (Op.starts_with(" prefix") ? T + "&" : T))
      fail(F.Decl.At, "increment or decrement requires a writable nominal "
                      "lvalue and the matching result type");
  } else if (Op != "()") {
    bool Unary = Op == "!" || Op == "~";
    bool Either = Op == "+" || Op == "-";
    if (Arity != (Unary ? 1u : 2u) && !(Either && Arity == 1))
      fail(F.Decl.At, "invalid operator operand count");
  }
}
Function *Context::declare(const Node &N, const std::string &Name,
                           const std::string &P, const Substitution &E,
                           const std::string &Owner) {
  Frame Resolver(*this, nullptr, nullptr, P);
  Resolver.Env = E;
  Function D;
  D.ExitedLifetimes = validate(N, P, Owner);
  D.Decl = N;
  D.MayWhole = N.Settings.count("lifecycle_effect");
  D.DefaultParams = N.Params;
  D.Name = Name;
  D.Owner = Owner;
  D.Prefix = D.DefaultPrefix = P;
  D.Env = D.DefaultEnv = E;
  D.Definition = D.Defaults = site();
  D.DeclaredAt = Sequence;
  D.Result = N.K == Node::Constructor || N.K == Node::Destructor
                 ? "void"
                 : Resolver.resolve(N.Type, N.At);
  std::vector<llvm::Type *> Types;
  if (aggregate(D.Result))
    Types.push_back(llvm::PointerType::getUnqual(C));
  if (!Owner.empty() && !D.isStatic())
    Types.push_back(llvm::PointerType::getUnqual(C));
  bool HasDefault = false;
  std::set<std::string> Names;
  for (auto &Arg : N.Params) {
    if (!Arg.Text.empty() && !Names.insert(Arg.Text).second)
      fail(Arg.At, "duplicate parameter");
    if (!Arg.Children.empty() &&
        (Arg.Children[0].Text == "true" || Arg.Children[0].Text == "false") &&
        integer(Resolver.resolve(Arg.Type, Arg.At)))
      fail(Arg.At, "cannot convert bool to integer");
    if (!Arg.Children.empty())
      HasDefault = true;
    else if (HasDefault)
      fail(Arg.At, "default arguments must form a trailing suffix");
    auto Type = Resolver.resolve(Arg.Type, Arg.At);
    if (Arg.Const && StringRef(Type).ends_with("&"))
      Type = qualifyConst(Type);
    auto ValueType = unconst(Type);
    if (ir(ValueType, Arg.At)->isVoidTy())
      fail(Arg.At, "ordinary parameter requires an object or reference type");
    D.Decl.Params[D.Params.size()].Const |= Type != ValueType;
    D.Params.push_back(ValueType);
    Types.push_back(aggregate(D.Params.back()) ? llvm::PointerType::getUnqual(C)
                                               : ir(D.Params.back(), Arg.At));
  }
  for (auto Key : {"requires_initialized", "initializes"}) {
    auto Attr = N.Settings.find(Key);
    if (Attr == N.Settings.end())
      continue;
    if (Owner.empty() || D.isStatic() || N.K != Node::Function)
      fail(N.At, "construction-state contract requires an instance method");
    bool Builds = StringRef(Key) == "initializes";
    if (Builds && N.Const)
      fail(N.At, "initializes requires a mutable receiver");
    const auto &Fields = Records.at(Owner).Fields;
    for (const auto &Slot : splitArguments(Attr->second)) {
      auto I = llvm::find_if(Fields, [&](const Field &F) {
        return F.Decl.K == Node::Field && F.Decl.Text == Slot;
      });
      if (I == Fields.end())
        fail(N.At, "unknown construction-state slot '" + Slot + "'");
      (Builds ? D.Initializes : D.RequiresAlive).insert(I - Fields.begin());
    }
  }
  if (!D.Initializes.empty() && !D.RequiresAlive.empty() &&
      *D.RequiresAlive.rbegin() >= *D.Initializes.begin())
    fail(N.At, "LIFE001: incompatible construction-state entry requirements");
  if (!D.Initializes.empty())
    Types.push_back(llvm::PointerType::getUnqual(C));
  if (operatorSpelling(N.Text))
    checkOperator(D, *this);
  for (auto Attr : {"noescape", "returns_borrowed_from", "consumes"}) {
    auto It = N.Settings.find(Attr);
    if (It == N.Settings.end())
      continue;
    bool Result = llvm::StringRef(Attr) == "returns_borrowed_from";
    if (Result)
      requireBorrowable(D.Result, N.At, true);
    bool Consuming = StringRef(Attr) == "consumes";
    auto &Positions = Consuming ? D.Consumes
                      : Result  ? D.BorrowedResult
                                : D.NoEscape;
    for (const auto &Param : splitArguments(It->second)) {
      auto I = llvm::find_if(N.Params,
                             [&](const Node &P) { return P.Text == Param; });
      if (I == N.Params.end())
        fail(N.At, "unknown borrow-contract parameter");
      unsigned Position = I - N.Params.begin();
      if (!Consuming)
        requireBorrowable(D.Params[Position], I->At, false);
      Positions.insert(Position);
    }
  }
  auto &Group = Overloads[Name];
  if (N.Foreign) {
    auto Scalar = [&](const std::string &T) {
      return integer(T) || floating(T) || T == "bool" || T == "char" ||
             StringRef(T).ends_with("*") || Enums.count(T);
    };
    if ((D.Result != "void" && !Scalar(D.Result)) ||
        !llvm::all_of(D.Params, Scalar))
      fail(N.At, "no C ABI transport for this function signature");
    if (auto Previous = ExternalFunctions.find(N.Text);
        Previous != ExternalFunctions.end()) {
      auto *Prev = Previous->second;
      if (Prev->Params != D.Params || Prev->Result != D.Result ||
          Prev->Decl.Noexcept != N.Noexcept)
        fail(N.At, "conflicting C function declarations for '" + N.Text + "'");
      if (!llvm::is_contained(Group, Prev))
        Group.push_back(Prev);
    }
  }
  for (auto *Prev : Group)
    if (!Owner.empty() && Prev->Params == D.Params &&
        Prev->Decl.Const == N.Const &&
        (Prev->Decl.Settings["category"].empty() !=
         (N.Settings.count("category") == 0 ||
          N.Settings.at("category").empty())))
      fail(N.At, "duplicate category-unqualified method");
  for (auto *Prev : Group)
    if (Prev->Params == D.Params && Prev->Decl.Const == N.Const &&
        Prev->Decl.Settings["category"] ==
            (N.Settings.count("category") ? N.Settings.at("category") : "")) {
      if ((N.Settings.count("initializes") &&
           Prev->Initializes != D.Initializes) ||
          (N.Settings.count("requires_initialized") &&
           Prev->RequiresAlive != D.RequiresAlive) ||
          Prev->NoEscape != D.NoEscape ||
          Prev->BorrowedResult != D.BorrowedResult ||
          Prev->Consumes != D.Consumes || Prev->Result != D.Result ||
          Prev->Decl.Foreign != N.Foreign ||
          Prev->Decl.Noexcept != N.Noexcept || Prev->Decl.K != N.K ||
          Prev->Decl.Settings.count("lifecycle_effect") !=
              N.Settings.count("lifecycle_effect") ||
          (!N.Settings.count("qualifier") &&
           Prev->isStatic() != D.isStatic()) ||
          Prev->Decl.Required != N.Required ||
          Prev->Decl.Settings.count("mode") != N.Settings.count("mode"))
        fail(N.At, "incompatible redeclaration");
      if (N.Prototype)
        return Prev;
      if (!Prev->Decl.Prototype)
        fail(N.At, "function already defined");
      for (auto &Arg : N.Params)
        if (!Arg.Children.empty())
          fail(Arg.At, "defaults belong to the canonical declaration");
      auto Defaults = Prev->Decl.Params;
      auto Canonical = Prev->Decl.Settings;
      Prev->Decl = D.Decl;
      Prev->ExitedLifetimes = std::move(D.ExitedLifetimes);
      for (const auto *Key :
           {"access", "virtual", "static", "override", "final"})
        if (Canonical.count(Key))
          Prev->Decl.Settings[Key] = Canonical[Key];
      Prev->Prefix = P;
      Prev->Env = E;
      Prev->Definition = site();
      for (size_t I = 0; I < Defaults.size(); ++I)
        if (!Defaults[I].Children.empty())
          Prev->Decl.Params[I].Children = Defaults[I].Children;
      return Prev;
    }
  if (N.Settings.count("qualifier"))
    fail(N.At, "qualified definition must match an existing declaration");
  bool Export = N.Foreign || Name == "main";
  if (Name == "main" && (D.Result != "i32" || !D.Params.empty()))
    fail(N.At, "the hosted entry point must be i32 main()");
  auto *FT = llvm::FunctionType::get(
      aggregate(D.Result) ? llvm::Type::getVoidTy(C) : ir(D.Result, N.At),
      Types, false);
  std::string Symbol = N.Foreign ? N.Text
                       : Export
                           ? Name
                           : "cpn." + std::to_string(Serial++) + "." + Name;
  if (Export && M.getNamedValue(Symbol)) {
    auto *Existing = M.getFunction(Symbol);
    if (!SlotType || !N.Foreign || (Symbol != "malloc" && Symbol != "free") ||
        !Existing || !Existing->isDeclaration() ||
        Existing->getFunctionType() != FT)
      fail(N.At, "conflicting external symbol '" + Symbol + "'");
    D.IR = Existing;
  } else
    D.IR = llvm::Function::Create(FT,
                                  Export ? llvm::GlobalValue::ExternalLinkage
                                         : llvm::GlobalValue::InternalLinkage,
                                  Symbol, M);
  if (D.Result == "never")
    D.IR->addFnAttr(llvm::Attribute::NoReturn);
  if (N.Foreign) {
    auto ext = [&](const std::string &Ty) {
      return signedType(Ty) ? llvm::Attribute::SExt : llvm::Attribute::ZExt;
    };
    if ((integer(D.Result) || D.Result == "bool") && width(D.Result) < 32)
      D.IR->addRetAttr(ext(D.Result));
    for (size_t I = 0; I < D.Params.size(); ++I)
      if ((integer(D.Params[I]) || D.Params[I] == "bool") &&
          width(D.Params[I]) < 32)
        D.IR->addParamAttr(I, ext(D.Params[I]));
  }
  Functions.push_back(std::move(D));
  Group.push_back(&Functions.back());
  if (N.Foreign)
    ExternalFunctions[N.Text] = Group.back();
  return Group.back();
}
// The first declaration in a block owns the nominal identity, including a
// forward declaration. Emitting an inlined activation again reuses that type.
void Frame::localType(const Node &N) {
  auto &Scope = Scopes.back();
  auto [It, New] = Scope.Nominals.emplace(N.Text, N.K);
  if (New) {
    auto Key = (F ? F->Name : Prefix) + "::$local." +
               std::to_string(N.At.Line) + "." + std::to_string(N.At.Column) +
               "::" + N.Text;
    if (Scope.Names.count(N.Text) || !Scope.Aliases.emplace(N.Text, Key).second)
      fail(N.At, "duplicate declaration '" + N.Text + "'");
  } else if (It->second != N.K)
    fail(N.At, "conflicting local type declaration");
  auto Key = Scope.Aliases.at(N.Text);
  if (!U.LocalTypeSites.emplace(Key, SourcePosition{N.At.Line, N.At.Column})
           .second)
    return;
  Substitution Lexical = Env;
  for (const auto &Scope : Scopes) {
    for (const auto &[Name, T] : Scope.Aliases)
      Lexical.Types[Name] = T;
    for (const auto &[Name, V] : Scope.Names)
      if (V.Readonly && llvm::isa_and_nonnull<llvm::Constant>(V.IR))
        Lexical.Values[Name] = V;
  }
  if (N.K == Node::Enumeration)
    U.enumeration(*this, N, Key);
  else if (N.K == Node::Union)
    U.tagged(N, Key, Prefix, Lexical);
  else
    U.record(N, Key, Prefix, Lexical);
}

void Context::enumeration(Frame &F, const Node &D, const std::string &Name) {
  auto Ty = F.resolve(D.Type, D.At);
  if (!integer(Ty))
    fail(D.At, "integer enum underlying type required");
  if (Enums.count(Name) && Enums.at(Name) != Ty)
    fail(D.At, "incompatible enum declaration");
  if (!D.Prototype && !DefinedEnums.insert(Name).second)
    fail(D.At, "duplicate enum definition '" + Name + "'");
  Enums[Name] = Ty;
  std::set<uint64_t> Values;
  for (auto &Case : D.Children) {
    if (Case.Children.empty())
      fail(Case.At, "enum case requires an explicit value");
    auto V = F.convert(F.constantEval(Case.Children[0]), Ty, Case.At);
    auto K = llvm::cast<llvm::ConstantInt>(V.IR)->getZExtValue();
    if (!Values.insert(K).second)
      fail(Case.At, "duplicate enum value");
    V.Type = Name;
    if (!Globals.emplace(Name + "::" + Case.Text, V).second)
      fail(Case.At, "duplicate enumerator '" + Case.Text + "'");
  }
}

bool Context::nestedType(const Node &D, const std::string &Owner,
                         Frame &Check) {
  if (D.K != Node::Alias && D.K != Node::Enumeration && D.K != Node::Record &&
      D.K != Node::Union)
    return false;
  std::string Prefix = Owner + "::", Key = Prefix + D.Text;
  auto [It, New] = MemberTypes.try_emplace(Key, Owner, D);
  if (!New &&
      (It->second.second.K != D.K ||
       It->second.second.Settings.at("access") != D.Settings.at("access")))
    fail(D.At, "conflicting nested type declaration");
  auto &Parent = Records.at(Owner);
  llvm::SaveAndRestore Policy(Opt);
  for (auto &Config : D.Policies)
    configure(Opt, Config, ConfigScope::Declaration);
  llvm::SaveAndRestore LocalPolicy(Check.Opt, Opt);
  if (!D.Generics.empty()) {
    validate(D, Prefix);
    checkDomain(D, Prefix);
    if (!Families.emplace(Key, Family{D, Prefix, site(), Parent.Env}).second)
      fail(D.At, "duplicate nested generic declaration");
  } else if (D.K == Node::Alias) {
    if (!Aliases.emplace(Key, Check.resolve(D.Type, D.At)).second)
      fail(D.At, "duplicate nested type alias");
  } else if (D.K == Node::Enumeration)
    enumeration(Check, D, Key);
  else if (D.K == Node::Record)
    record(D, Key, Prefix, Parent.Env);
  else
    tagged(D, Key, Prefix, Parent.Env);
  return true;
}

void Context::record(const Node &N, const std::string &Name,
                     const std::string &P, const Substitution &E) {
  auto &R = Records[Name];
  if (R.Complete)
    fail(N.At, "duplicate record definition");
  if (R.IR && R.Decl.K != Node::Record)
    fail(N.At, "conflicting nominal declaration");
  if (!R.IR)
    R.IR = llvm::StructType::create(C, "cpn." + Name);
  if (N.Prototype) {
    R.Decl = N;
    return;
  }
  R.Decl = N;
  R.EnclosingScope = StringRef(P).rtrim(':').str();
  R.Env = E;
  R.Env.Types[N.Text] = Name;
  Frame Check(*this, nullptr, nullptr, Name + "::");
  Check.Env = R.Env;
  std::vector<llvm::Type *> Layout;
  std::vector<std::pair<std::string, bool>> Direct;
  std::set<std::string> Seen;
  for (const auto &Base : N.TemplateArgs) {
    auto T = Check.resolve(Base.Type, Base.At);
    if (!Records.count(T) || !Records.at(T).Complete ||
        Records.at(T).Decl.K != Node::Record)
      fail(Base.At, "base requires a complete record");
    if (!Seen.insert(T).second)
      fail(Base.At, "duplicate direct base");
    auto &BR = Records.at(T);
    if (BR.Decl.Settings.count("final"))
      fail(Base.At, "base must be a complete non-final record");
    for (unsigned I = 0; I < BR.VirtualCount; ++I)
      if (!llvm::is_contained(R.Bases, BR.Bases[I]))
        R.Bases.push_back(BR.Bases[I]);
    if (Base.Definition && !llvm::is_contained(R.Bases, T))
      R.Bases.push_back(T);
    Direct.emplace_back(T, Base.Definition);
  }
  R.VirtualCount = R.Bases.size();
  for (auto &[T, Virtual] : Direct) {
    if (Virtual)
      R.Direct.push_back(llvm::find(R.Bases, T) - R.Bases.begin());
    else {
      R.Direct.push_back(R.Bases.size());
      R.Bases.push_back(T);
    }
  }
  for (unsigned I = 0; I < R.Bases.size(); ++I) {
    const auto &T = R.Bases[I];
    Node Slot(Node::TypeArg, N.At);
    Slot.Text = Slot.At.Text =
        (I < R.VirtualCount ? "$virtual:" : "$base:") + T;
    R.Fields.push_back({Slot, T});
    Layout.push_back(I < R.VirtualCount
                         ? static_cast<llvm::Type *>(llvm::ArrayType::get(
                               llvm::Type::getInt8Ty(C), 0))
                         : Records.at(T).Layer);
  }
  for (auto &D : N.Children) {
    if (nestedType(D, Name, Check))
      continue;
    if (D.K == Node::Field) {
      if (D.Settings.count("storage")) {
        if (!StaticMembers
                 .emplace(Name + "::" + D.Text, std::make_pair(Name, D))
                 .second)
          fail(D.At, "duplicate static member");
        continue;
      }
      llvm::SaveAndRestore Policy(Check.Opt);
      for (const auto &Config : D.Policies)
        configure(Check.Opt, Config, ConfigScope::Declaration);
      auto T = Check.resolve(D.Type, D.At);
      auto *Ty = ir(T, D.At);
      if (!Ty->isSized())
        fail(D.At, "field requires a complete object type");
      if (StaticMembers.count(Name + "::" + D.Text) ||
          llvm::any_of(R.Fields,
                       [&](auto &F) { return F.Decl.Text == D.Text; }))
        fail(D.At, "duplicate member");
      auto Member = D;
      Member.Const |= unconst(T) != T;
      R.Fields.push_back(
          {Member, unconst(T), DefinitionSite{Check.Opt, Check.LookupLimit}});
      Layout.push_back(Ty);
    }
  }
  R.Polymorphic =
      llvm::any_of(R.Bases,
                   [&](auto &Base) { return Records.at(Base).Polymorphic; }) ||
      llvm::any_of(N.Children,
                   [](auto &C) { return C.Settings.count("virtual"); });
  if (R.Polymorphic) {
    Layout.push_back(llvm::PointerType::getUnqual(C));
    size_t Slots = N.Children.size();
    for (auto I : R.Direct)
      Slots += Records.at(R.Bases[I]).Virtuals.size();
    Layout.push_back(llvm::ArrayType::get(llvm::Type::getInt64Ty(C), Slots));
  }
  Layout.insert(Layout.end(), R.VirtualCount, llvm::Type::getInt64Ty(C));
  if (Layout.empty())
    Layout.push_back(llvm::Type::getInt8Ty(C));
  R.Layer = R.IR;
  if (R.VirtualCount) {
    Layout.insert(Layout.end(), R.VirtualCount, llvm::Type::getInt64Ty(C));
    Layout.push_back(llvm::Type::getInt32Ty(C));
    Layout.push_back(llvm::Type::getInt1Ty(C));
    R.Layer = llvm::StructType::create(C, Layout, "cpn.layer." + Name);
    // Align the tail after the full size of the embedded nonvirtual prefix.
    Layout.push_back(llvm::ArrayType::get(R.Layer, 0));
    for (unsigned I = 0; I < R.VirtualCount; ++I)
      Layout.push_back(Records.at(R.Bases[I]).Layer);
    Layout.push_back(llvm::ArrayType::get(ownerRecordType(), R.VirtualCount));
  }
  R.IR->setBody(Layout);
  R.Complete = true;
  declareMembers(Name, Name + "::");
}
void Context::declareMembers(const std::string &Name, const std::string &P) {
  auto &R = Records.at(Name);
  const auto &N = R.Decl;
  Frame Check(*this, nullptr, nullptr, P);
  Check.Env = R.Env;
  for (auto &D : R.Decl.Children)
    if (D.K == Node::Init && D.Type == "Complete") {
      auto Sep = D.Text.find(':');
      if (Sep != std::string::npos)
        D.Text = D.Text.substr(0, Sep + 1) +
                 Check.resolve(D.Text.substr(Sep + 1), D.At);
    }
  for (const auto &D : N.Children)
    if ((D.K == Node::Field || D.K == Node::Function || D.K == Node::Variant) &&
        MemberTypes.count(Name + "::" + D.Text))
      fail(D.At, "member name conflicts with nested type");
  buildViews(Name);
  bindOwners(Name, P);
  std::vector<Function *> Members;
  for (auto &D : N.Children)
    if (D.K == Node::Constructor || D.K == Node::Destructor ||
        D.K == Node::Function) {
      llvm::SaveAndRestore Policy(Opt);
      for (const auto &PrefixPolicy : D.Policies)
        configure(Opt, PrefixPolicy, ConfigScope::Declaration);
      llvm::SaveAndRestore MemberPolicy(Check.Opt, Opt);
      if (!D.Generics.empty()) {
        genericFunction(D, Name + "::" + D.Text, P, Name);
        continue;
      }
      bool Assign = D.Text == "operator=";
      bool Defaulted =
          D.Settings.count("control") && D.Settings.at("control") == "default";
      std::optional<SpecialOperation> Op;
      if ((Assign || D.K == Node::Constructor) && D.Params.size() == 1) {
        auto T = Check.resolve(D.Params[0].Type, D.At);
        if (T == "const<" + Name + ">&")
          Op = Assign ? SpecialOperation::CopyAssign
                      : SpecialOperation::CopyConstruct;
        if (T == Name + "&&")
          Op = Assign ? SpecialOperation::MoveAssign
                      : SpecialOperation::MoveConstruct;
      }
      if (Op && Assign && Check.resolve(D.Type, D.At) != Name + "&")
        fail(
            D.At,
            "copy and move assignment must return a reference to the receiver");
      if (Defaulted && !Op &&
          !(D.Params.empty() &&
            (D.K == Node::Destructor || D.K == Node::Constructor)))
        fail(D.At, "no generated default definition for this signature");
      Function *Body = nullptr;
      if (!Defaulted &&
          !(D.K == Node::Destructor && D.Settings.count("control"))) {
        auto Key = Name + "::" +
                   (D.K == Node::Constructor  ? "$ctor"
                    : D.K == Node::Destructor ? "$drop"
                                              : D.Text);
        Body = declare(D, Key, P, R.Env, Name);
        Members.push_back(Body);
      }
      if (Op && !R.Special.emplace(*Op, SpecialMember{D, Body}).second)
        fail(D.At, "duplicate special operation");
    }
  if (R.VirtualCount)
    for (auto *F : Members)
      if ((F->Decl.K == Node::Constructor || F->Decl.K == Node::Destructor) &&
          !F->Decl.Settings.count("control"))
        F->BaseIR = llvm::Function::Create(F->IR->getFunctionType(),
                                           llvm::GlobalValue::InternalLinkage,
                                           F->IR->getName() + ".base", M);
  for (auto D : N.Children) {
    if (D.K != Node::Field || !D.Settings.count("storage"))
      continue;
    auto ID = Name + "::" + D.Text;
    if (llvm::any_of(R.Fields,
                     [&](const Field &F) { return F.Decl.Text == D.Text; }))
      fail(D.At, "duplicate member");
    D.Settings["identity"] = ID;
    Statics.emplace_back(ID, D);
    llvm::SaveAndRestore MemberPolicy(Check.Opt);
    for (const auto &Config : D.Policies)
      configure(Check.Opt, Config, ConfigScope::Declaration);
    Check.object(D, true);
  }
  buildTables(Name, Members);
  if (auto Bodies = OwnerBodies.find({N.At.Line, N.At.Column});
      Bodies != OwnerBodies.end())
    for (const auto &[Site, Definition] : Bodies->second)
      bindFamilyMember(Name, Definition);
  for (auto *F : Members)
    emit(*F);
}
void Context::defineQualified(const Node &D, const std::string &P,
                              const Substitution *Bindings) {
  const bool Ctor = D.K == Node::Constructor, Dtor = D.K == Node::Destructor;
  auto Method = Ctor ? "$ctor" : Dtor ? "$drop" : D.Text;
  auto Key = scopeKey(P, D.Settings.at("qualifier") + Method,
                      [&](const std::string &K) { return Overloads.count(K); });
  if (Key.empty())
    fail(D.At, "qualified definition must match an existing declaration");
  auto *Previous = Overloads.at(Key).front();
  auto Owner = Previous->Owner;
  if ((Ctor || Dtor) &&
      (Owner.empty() || Records.at(Owner).Decl.Text != D.Text))
    fail(D.At, "special member must name its owning record");
  if (Owner.empty() && (D.Const || D.Settings.count("category")))
    fail(D.At, "a namespace function has no receiver");
  auto *F = declare(D, Key, Previous->Prefix,
                    Bindings ? *Bindings : Previous->Env, Owner);
  if (!Owner.empty())
    for (auto &[Op, Special] : Records.at(Owner).Special)
      if (Special.Body == F)
        Special.Decl = F->Decl;
  if (D.Settings.count("control")) {
    auto Control = D.Settings.at("control");
    if (Control == "delete") {
      if (!F->IR->use_empty() || (F->BaseIR && !F->BaseIR->use_empty()))
        fail(D.At, "selected function is deleted");
    } else {
      if (!Ctor && !Dtor && D.Text != "operator=")
        fail(D.At, "no generated default definition for this signature");
      F->Decl.Children.emplace_back(Node::Block, D.At);
      F->Decl.Settings.erase("control");
      if (!D.Params.empty()) {
        auto &R = Records.at(Owner);
        auto Special = llvm::find_if(R.Special, [&](const auto &Entry) {
          return Entry.second.Body == F;
        });
        if (Special == R.Special.end())
          fail(D.At, "no generated default definition for this signature");
        Special->second.Body = nullptr;
        for (auto *Entry : {F->IR, F->BaseIR}) {
          if (!Entry)
            continue;
          Frame Generated(*this, F, Entry);
          Generated.B.SetInsertPoint(Generated.block("entry"));
          Generated.transfer({Owner, nullptr, Entry->getArg(1)},
                             Entry->getArg(0), Special->first, D.At,
                             Entry == F->BaseIR);
          if (D.Text == "operator=")
            Generated.B.CreateRet(Entry->getArg(0));
          else
            Generated.B.CreateRetVoid();
        }
        F->Emitted = true;
      }
    }
  }
  emit(*F);
}
// The declaration retains the overload identity, defaults and substitution
// order. An out-of-line body uses its own parameter names and definition site.
void Context::attachGenericBody(Function &F, const Family &FamilyDecl) {
  if (!FamilyDecl.Body)
    return;
  auto Body = *FamilyDecl.Body;
  const auto &Public = F.Decl;
  if (Body.Generics.back().Pack) {
    Family Expanded{Body, FamilyDecl.Prefix, *FamilyDecl.BodySite};
    Body = expand(Expanded, Public.Generics.size() - (Body.Generics.size() - 1),
                  Body.At)
               .Decl;
  }
  auto Original = F.Env;
  for (size_t I = 0; I < Body.Generics.size(); ++I) {
    const auto &P = Public.Generics[I], &Q = Body.Generics[I];
    if (P.K == Node::TypeParam)
      F.Env.Types[Q.Text] = Original.Types.at(P.Text);
    else
      F.Env.Values[Q.Text] = Original.Values.at(P.Text);
  }
  F.ExitedLifetimes = validate(Body, F.Prefix, F.Owner);
  for (size_t I = 0; I < Body.Params.size(); ++I) {
    Body.Params[I].Children = Public.Params[I].Children;
    Body.Params[I].Const |= Public.Params[I].Const;
  }
  Body.Settings.erase("qualifier");
  Body.Settings.insert(Public.Settings.begin(), Public.Settings.end());
  F.Decl = std::move(Body);
  F.Definition = *FamilyDecl.BodySite;
}

void Context::genericFunction(const Node &D, const std::string &Name,
                              const std::string &P, const std::string &Owner) {
  bool Qualified = D.Settings.count("qualifier");
  auto Key = Qualified ? scopeKey(P, D.Settings.at("qualifier") + D.Text,
                                  [&](const std::string &K) {
                                    return FunctionFamilies.count(K);
                                  })
                       : Name;
  if (Key.empty())
    fail(D.At,
         "qualified generic definition must match an existing declaration");
  auto &Group = FunctionFamilies[Key];
  auto It = llvm::find_if(Group, [&](const Family &Other) {
    return sameGenericSignature(Other.Decl, D);
  });
  if (It == Group.end() && Qualified)
    fail(D.At,
         "qualified generic definition must match an existing declaration");
  auto Scope = Qualified ? It->Prefix : P;
  auto Class = Qualified ? It->Owner : Owner;
  for (const auto &Requirement : D.TemplateArgs)
    checkNormalForm(Requirement);
  validate(D, Scope, Class);
  checkDomain(D, Scope);
  if (It == Group.end()) {
    Family F{D, Scope, site(),
             Class.empty() ? Substitution{} : Records.at(Class).Env, Class};
    Families.try_emplace(Key, F);
    Group.push_back(std::move(F));
    return;
  }
  if (!It->Decl.Prototype || D.Prototype || It->Body)
    fail(D.At, "duplicate generic signature");
  if (!sameGenericResult(It->Decl, D) || D.Noexcept != It->Decl.Noexcept ||
      D.Required != It->Decl.Required || D.Foreign != It->Decl.Foreign ||
      D.Settings.count("mode") != It->Decl.Settings.count("mode"))
    fail(D.At, "incompatible generic definition");
  for (auto &G : D.Generics)
    if (!G.Children.empty())
      fail(G.At, "a separate definition cannot redeclare defaults");
  for (auto &Arg : D.Params)
    if (!Arg.Children.empty())
      fail(Arg.At, "a separate definition cannot redeclare defaults");
  for (auto &[Effect, Value] : D.Settings)
    if (Effect != "qualifier" && Effect != "category" &&
        (!It->Decl.Settings.count(Effect) ||
         It->Decl.Settings.at(Effect) != Value))
      fail(D.At, "incompatible generic definition contract");
  It->Body = D;
  It->BodySite = site();
  std::vector<Function *> Pending;
  for (auto &F : Functions)
    if (F.Origin == &*It)
      Pending.push_back(&F);
  for (auto *F : Pending) {
    attachGenericBody(*F, *It);
    emit(*F);
  }
}

void Context::unit(const std::vector<Node> &Decls, std::string P) {
  for (auto &D : Decls) {
    if (D.K == Node::TypeQuery)
      continue;
    ++Sequence;
    auto Name = P + D.Text;
    if (D.K == Node::Config) {
      configure(Opt, D, ConfigScope::File);
      continue;
    }
    llvm::SaveAndRestore Policy(Opt);
    for (const auto &PrefixPolicy : D.Policies)
      configure(Opt, PrefixPolicy, ConfigScope::Declaration);
    if (D.K != Node::Linkage && !D.Settings.count("qualifier") &&
        !D.Settings.count("specialize")) {
      auto [Bound, Inserted] = Declarations.emplace(Name, D.K);
      if (!Inserted && Bound->second != D.K)
        fail(D.At,
             "conflicting nominal or ordinary declaration of '" + Name + "'");
    }
    if (D.K == Node::Linkage || D.K == Node::Namespace) {
      unit(D.Children, D.K == Node::Linkage ? P : Name + "::");
      continue;
    }
    if (D.K == Node::Constraint) {
      checkNormalForm(D);
      if (!Constraints.emplace(Name, Family{D, P, site()}).second)
        fail(D.At, "duplicate constraint declaration");
      validate(D, P);
      continue;
    }
    if (D.Settings.count("specialize")) {
      auto Primary = Families.find(Name);
      if (Primary == Families.end() || Primary->second.Decl.K != D.K ||
          Primary->second.Decl.Type != D.Type)
        fail(D.At, "specialization must match its owning type family");
      if (D.Pattern.size() != Primary->second.Decl.Generics.size())
        fail(D.At, "specialization pattern has the wrong arity");
      for (auto &Req : D.Params)
        checkNormalForm(Req);
      validate(D, P);
      Specializations[Name].push_back({D, P, site()});
      continue;
    }
    if (D.Settings.count("qualifier") &&
        D.Settings.at("qualifier").find('<') != std::string::npos) {
      defineFamilyMember(D, P);
      continue;
    }
    if (!D.Generics.empty()) {
      if (D.K == Node::Function) {
        genericFunction(D, Name, P);
        continue;
      }
      for (auto &Req : D.TemplateArgs)
        checkNormalForm(Req);
      validate(D, P);
      checkDomain(D, P);
      if (!Families.emplace(Name, Family{D, P, site()}).second)
        fail(D.At, "duplicate generic declaration");
      continue;
    }
    if (D.Settings.count("qualifier")) {
      defineQualified(D, P);
      continue;
    }
    if (D.K == Node::Function) {
      auto *F = declare(D, Name, P, {});
      if (!D.Prototype)
        emit(*F);
      continue;
    }
    if (D.K == Node::Union) {
      tagged(D, Name, P);
      continue;
    }
    if (D.K == Node::Record) {
      record(D, Name, P, {});
      continue;
    }
    Frame F(*this, nullptr, nullptr, P);
    if (D.K == Node::Alias) {
      if (!Aliases.emplace(Name, F.resolve(D.Type, D.At)).second)
        fail(D.At, "duplicate alias '" + Name + "'");
      continue;
    }
    if (D.K == Node::Enumeration) {
      enumeration(F, D, Name);
      continue;
    }
    if (D.K == Node::Object) {
      Statics.emplace_back(Name, D);
      F.object(D, true);
      continue;
    }
    fail(D.At, "unsupported declaration");
  }
}
void Context::emit(Function &D) {
  if (D.Emitted || D.Emitting || D.Decl.Prototype ||
      D.Decl.Settings.count("control"))
    return;
  D.Emitting = true;
  emitBody(D, D.IR, false);
  if (D.BaseIR)
    emitBody(D, D.BaseIR, true);
  D.Emitting = false;
  D.Emitted = true;
}
void Context::emitBody(Function &D, llvm::Function *Entry, bool AsBase) {
  Frame F(*this, &D, Entry);
  F.BaseLayer = AsBase;
  F.B.SetInsertPoint(F.block("entry"));
  F.bindParams();
  if (D.Decl.Settings.count("closure"))
    F.bindCaptures();
  auto &Body = D.Decl.Children.front();
  if (D.Decl.K == Node::Constructor &&
      Records.at(D.Owner).Decl.K == Node::Union) {
    for (auto &S : Body.Children)
      if (S.K == Node::Init)
        fail(S.At, "a union case is not a common field initializer");
    F.beginUnionConstructor();
    F.stmt(Body);
  } else if (D.Decl.K == Node::Constructor) {
    Construction Transaction(F, D, F.Self, nullptr, nullptr);
    Transaction.run(F);
  } else if (D.Decl.K == Node::Destructor)
    F.retirement();
  else if (!D.Initializes.empty() || !D.RequiresAlive.empty()) {
    Construction Contract(F, D);
    F.Transaction = &Contract;
    F.stmt(Body);
    if (F.Live)
      Contract.checkReturn(D.Decl.At);
    F.Transaction = nullptr;
  } else
    F.stmt(Body);
  if (F.Live) {
    if (D.Result != "void")
      fail(D.Decl.At, "function can finish without returning a value");
    F.cleanup(0);
    F.B.CreateRetVoid();
  } else if (!F.B.GetInsertBlock()->hasTerminator())
    F.B.CreateUnreachable();
  for (auto &L : F.Labels)
    if (!F.DefinedLabels.count(L.first))
      fail(D.Decl.At, "unknown statement label");
}
void cpn::compile(llvm::Module &M, const std::vector<Node> &AST, Options O) {
  Context U(M, std::move(O));
  for (const auto &N : AST)
    if (N.K == Node::TypeQuery)
      U.TypeQueries.emplace(N.Text, N);
  U.Whole = llvm::any_of(AST, Frame::usesWhole);
  if (U.Whole || llvm::any_of(AST, Frame::usesStorage))
    U.enableStorage();
  U.unit(AST);
  U.checkWholeContracts();
  U.checkBorrowEscapes();
  for (auto &F : U.Functions)
    for (auto *Entry : {F.IR, F.BaseIR})
      if (Entry && Entry->isDeclaration() && !F.Decl.Foreign) {
        if (!Entry->use_empty())
          fail(F.Decl.At, "function needs a definition");
        Entry->eraseFromParent();
      }
  std::set<std::string> Ids, Previous;
  for (auto &[Name, N] : U.Statics) {
    if (N.Settings.count("static_id") &&
        !Ids.insert(N.Settings.at("static_id")).second)
      fail(N.At, "STAT001: duplicate static identity");
    if (N.Settings.count("init_after")) {
      auto Owner = StringRef(Name).rsplit("::");
      auto Prefix =
          Owner.second.empty() ? std::string{} : Owner.first.str() + "::";
      for (const auto &Spelling : splitArguments(N.Settings.at("init_after"))) {
        auto Dep = scopeKey(Prefix, Spelling, [&](const auto &Key) {
          return U.Globals.count(Key);
        });
        if (Dep.empty())
          fail(N.At, "unknown static dependency");
        // One root source file has a declaration-order edge between successive
        // definitions. A backward dependency is already ordered and a forward
        // dependency closes a cycle, including through a constant object.
        if (!Previous.count(Dep))
          fail(N.At, "cyclic static initialization");
      }
    }
    Previous.insert(Name);
  }
  U.finishStaticReads();
  auto Hook = [&](std::vector<llvm::Function *> &List, bool IsStartup) {
    if (List.empty())
      return;
    if (!IsStartup)
      std::reverse(List.begin(), List.end());
    auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(U.C), false);
    auto *F =
        llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                               IsStartup ? "cpn.startup" : "cpn.shutdown", M);
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(U.C, "entry", F));
    for (auto *Call : List) {
      if (IsStartup && U.CurrentInitializer) {
        auto It = U.Initializing.find(Call);
        // Metadata setup for precommitted objects has no construction
        // authority.
        llvm::Value *Owner = It == U.Initializing.end()
                                 ? static_cast<llvm::Value *>(F)
                                 : It->second;
        B.CreateStore(Owner, U.CurrentInitializer);
      }
      B.CreateCall(Call);
    }
    if (IsStartup && U.CurrentInitializer)
      B.CreateStore(llvm::ConstantPointerNull::get(B.getPtrTy()),
                    U.CurrentInitializer);
    B.CreateRetVoid();
    if (IsStartup)
      llvm::appendToGlobalCtors(M, F, 65535);
    else
      llvm::appendToGlobalDtors(M, F, 65535);
  };
  Hook(U.Startup, true);
  Hook(U.Shutdown, false);
  U.finishPointerStorage();
}
