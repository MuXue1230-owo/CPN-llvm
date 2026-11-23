#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
using namespace cpn;
using llvm::StringRef;

std::optional<CallableTypeParts> cpn::splitCallableType(StringRef Type) {
  if (!Type.consume_front("function<") || !Type.consume_back(">"))
    return {};
  unsigned Angles = 0, Brackets = 0;
  for (size_t I = 0; I < Type.size(); ++I) {
    char C = Type[I];
    if (C == '[')
      ++Brackets;
    else if (C == ']' && Brackets)
      --Brackets;
    else if (!Brackets && C == '<')
      ++Angles;
    else if (!Brackets && C == '>' && Angles)
      --Angles;
    else if (!Brackets && !Angles && C == '(') {
      auto Close = Type.rfind(')');
      if (!I || Close == StringRef::npos || Close < I)
        return {};
      return CallableTypeParts{Type.take_front(I), Type.slice(I + 1, Close),
                               Type.drop_front(Close + 1)};
    }
  }
  return {};
}

namespace {
std::string substitute(StringRef S, const std::set<std::string> &Names,
                       size_t Index) {
  std::string R;
  auto IdentifierByte = [](char C) {
    return llvm::isAlnum(C) || C == '_' || C == '$' ||
           static_cast<unsigned char>(C) >= 128;
  };
  while (!S.empty()) {
    if (IdentifierByte(S[0])) {
      auto W = S.take_while(IdentifierByte);
      R += W;
      if (Names.count(W.str()))
        R += "$" + std::to_string(Index);
      S = S.drop_front(W.size());
    } else {
      R += S.front();
      S = S.drop_front();
    }
  }
  return R;
}
size_t angleEnd(StringRef S, size_t Open) {
  unsigned Angles = 1, Groups = 0;
  char Quote = 0;
  for (size_t I = Open + 1; I < S.size(); ++I) {
    char C = S[I];
    if (Quote) {
      if (C == '\\' && I + 1 < S.size())
        ++I;
      else if (C == Quote)
        Quote = 0;
    } else if (C == '\'' || C == '"')
      Quote = C;
    else if (C == '(' || C == '[' || C == '{')
      ++Groups;
    else if (C == ')' || C == ']' || C == '}') {
      if (Groups)
        --Groups;
    } else if (!Groups && C == '<')
      ++Angles;
    else if (!Groups && C == '>' && !--Angles)
      return I;
  }
  return StringRef::npos;
}

std::string
expandCallableFlags(StringRef Type,
                    llvm::ArrayRef<std::pair<unsigned, unsigned>> Positions) {
  auto Remap = [&](StringRef Digits, auto Add) {
    unsigned Old;
    if (Digits.getAsInteger(10, Old) || Old >= Positions.size())
      return;
    auto [Start, Count] = Positions[Old];
    for (unsigned I = Start; I < Start + Count; ++I)
      Add(I);
  };
  std::string Flags;
  if (callableFlag(Type, " noexcept"))
    Flags += " noexcept";
  if (callableFlag(Type, " whole"))
    Flags += " whole";
  std::set<unsigned> NoEscape, Borrowed, Consumes;
  for (auto Flag : callableFlags(Type)) {
    if (Flag.consume_front("noescape#"))
      Remap(Flag, [&](unsigned I) { NoEscape.insert(I); });
    else if (Flag.consume_front("borrow#"))
      Remap(Flag, [&](unsigned I) { Borrowed.insert(I); });
    else if (Flag.consume_front("consumes#"))
      Remap(Flag, [&](unsigned I) { Consumes.insert(I); });
  }
  auto RemapEffects = [&](EffectSet &Set) {
    EffectSet Mapped;
    for (const auto &Item : Set) {
      auto [Kind, Region] = StringRef(Item).split(':');
      if (Region.consume_front("#"))
        Remap(Region, [&](unsigned I) {
          Mapped.insert((Kind + ":#").str() + std::to_string(I));
        });
      else
        Mapped.insert(Item);
    }
    Set = std::move(Mapped);
  };
  auto Effects = callableEffects(Type);
  auto Predicate = callablePredicateEffects(Type);
  if (Effects)
    RemapEffects(*Effects);
  RemapEffects(Predicate);
  return Flags + parameterEffects(NoEscape, Borrowed, Consumes) +
         effectFlags(Effects) + predicateEffectFlags(Predicate);
}

std::string expandPackLists(StringRef Text, const std::set<std::string> &Names,
                            size_t Count, std::optional<size_t> Index,
                            const Token &At,
                            const std::set<std::string> &Deferred) {
  auto Rewrite = [&](StringRef Part) {
    return Index ? substitute(Part, Names, *Index) : Part.str();
  };
  auto Open = Text.find('<');
  if (!Text.contains("...") || Open == StringRef::npos)
    return Rewrite(Text);
  auto Close = angleEnd(Text, Open);
  if (Close == StringRef::npos)
    return Rewrite(Text);

  auto Callable = splitCallableType(Text.take_front(Close + 1));
  std::string Out;
  if (Callable)
    Out = "function<" +
          expandPackLists(Callable->Result, Names, Count, Index, At, Deferred) +
          "(";
  else
    Out = Rewrite(Text.take_front(Open + 1));
  llvm::SmallVector<std::pair<unsigned, unsigned>> Positions;
  unsigned Next = 0;
  bool First = true;
  auto Append = [&](StringRef Arg, std::optional<size_t> I) {
    if (!First)
      Out += ",";
    First = false;
    Out += expandPackLists(Arg, Names, Count, I, At, Deferred);
  };
  auto List = Callable ? Callable->Parameters : Text.slice(Open + 1, Close);
  for (const auto &Spelling : splitArguments(List)) {
    StringRef Arg = Spelling;
    if (!Arg.consume_back("...")) {
      Positions.emplace_back(Next++, 1);
      Append(Arg, Index);
      continue;
    }
    if (substitute(Arg, Deferred, 0) != Arg) {
      Positions.emplace_back(Next++, 1);
      Append(Spelling, Index);
      continue;
    }
    if (substitute(Arg, Names, 0) == Arg)
      fail(At, "generic argument expansion requires a pack binding");
    Positions.emplace_back(Next, Count);
    Next += Count;
    for (size_t I = 0; I < Count; ++I)
      Append(Arg, I);
  }
  if (Callable)
    Out += ")" + expandCallableFlags(Text.take_front(Close + 1), Positions);
  Out += ">";
  Out += expandPackLists(Text.drop_front(Close + 1), Names, Count, Index, At,
                         Deferred);
  return Out;
}

const TypeApplication *matchingApplication(const Context &U, const Family &Fam,
                                           StringRef Formal, StringRef Actual,
                                           size_t &Open) {
  Open = Formal.find('<');
  if (Open == StringRef::npos || angleEnd(Formal, Open) + 1 != Formal.size())
    return nullptr;
  auto Instance = U.TypeApplications.find(Actual.str());
  if (Instance == U.TypeApplications.end())
    return nullptr;
  auto Key = scopeKey(Fam.Prefix, Formal.take_front(Open),
                      [&](const std::string &Name) {
                        auto I = U.Families.find(Name);
                        return I != U.Families.end() &&
                               I->second.Site.Through <= Fam.Site.Through;
                      });
  return Key == Instance->second.Family ? &Instance->second : nullptr;
}

struct OwnerPattern {
  StringRef FormalOwner, ActualOwner, Member;
};

std::optional<OwnerPattern> matchOwnerPattern(const Context &U,
                                              const Family &Fam,
                                              StringRef Formal,
                                              StringRef Actual) {
  auto Instance = U.Records.find(Actual.str());
  if (Instance == U.Records.end() ||
      !U.Records.count(Instance->second.EnclosingScope))
    return {};
  size_t Member = StringRef::npos;
  for (size_t I = 0; I + 1 < Formal.size(); ++I) {
    if (Formal[I] == '<') {
      I = angleEnd(Formal, I);
      if (I == StringRef::npos)
        return {};
    } else if (I && Formal[I] == ':' && Formal[I + 1] == ':') {
      Member = I;
      ++I;
    }
  }
  if (Member == StringRef::npos)
    return {};
  const auto Owner = Formal.take_front(Member);
  const auto Tail = Formal.drop_front(Member + 2);
  if (Tail.split('<').first != Instance->second.Decl.Text)
    return {};
  StringRef ActualOwner = Instance->second.EnclosingScope;
  size_t Open;
  if (matchingApplication(U, Fam, Owner, ActualOwner, Open) ||
      matchOwnerPattern(U, Fam, Owner, ActualOwner))
    return OwnerPattern{Owner, ActualOwner, Tail};
  // A projection such as T::Member cannot independently deduce T.
  if (llvm::any_of(Fam.Decl.Generics, [&](const Node &Parameter) {
        return Parameter.K == Node::TypeParam && Parameter.Text == Owner;
      }))
    return {};
  if (auto Binding = Fam.Enclosing.Types.find(Owner.str());
      Binding != Fam.Enclosing.Types.end()) {
    if (Binding->second == ActualOwner)
      return OwnerPattern{Owner, ActualOwner, Tail};
    return {};
  }
  auto Key = scopeKey(Fam.Prefix, Owner, [&](const std::string &Name) {
    return U.Records.count(Name) || U.Aliases.count(Name);
  });
  if (auto Alias = U.Aliases.find(Key); Alias != U.Aliases.end())
    Key = Alias->second;
  if (Key == ActualOwner)
    return OwnerPattern{Owner, ActualOwner, Tail};
  return {};
}

std::string deductionType(StringRef Formal, const Value &Actual,
                          StringRef &Pattern) {
  auto Type = Actual.Type;
  if (Formal.consume_front("forward ") && Actual.Address && !Actual.Expiring)
    Type += "&";
  while (Formal.consume_back("&")) {
  }
  if (Formal.starts_with("const<") && Formal.ends_with(">"))
    Formal = Formal.slice(6, Formal.size() - 1);
  Pattern = Formal;
  return Type;
}

void visitTypeArguments(Frame &F, const Family &Fam, StringRef Formal,
                        StringRef Actual,
                        llvm::function_ref<void(StringRef, Value)> Deduce) {
  Deduce(Formal, {Actual.str()});
  for (StringRef Suffix : {"&&", "&", "*"}) {
    if (Formal.ends_with(Suffix) && Actual.ends_with(Suffix)) {
      visitTypeArguments(F, Fam, Formal.drop_back(Suffix.size()),
                         Actual.drop_back(Suffix.size()), Deduce);
      return;
    }
  }
  if (Formal.starts_with("const<") && Formal.ends_with(">") &&
      Actual.starts_with("const<") && Actual.ends_with(">")) {
    visitTypeArguments(F, Fam, Formal.slice(6, Formal.size() - 1),
                       Actual.slice(6, Actual.size() - 1), Deduce);
    return;
  }
  if (Formal.ends_with("]") && Actual.ends_with("]")) {
    auto P = Formal.rfind('['), A = Actual.rfind('[');
    uint64_t Extent;
    if (P != StringRef::npos && A != StringRef::npos &&
        !Actual.slice(A + 1, Actual.size() - 1).getAsInteger(10, Extent)) {
      Deduce(Formal.slice(P + 1, Formal.size() - 1),
             F.literal(Extent, "usize"));
      visitTypeArguments(F, Fam, Formal.take_front(P), Actual.take_front(A),
                         Deduce);
    }
    return;
  }
  if (auto P = splitCallableType(Formal)) {
    if (auto A = splitCallableType(Actual)) {
      auto Parameters = splitArguments(P->Parameters);
      auto Arguments = splitArguments(A->Parameters);
      if (Parameters.size() != Arguments.size())
        return;
      visitTypeArguments(F, Fam, P->Result, A->Result, Deduce);
      for (size_t I = 0; I < Parameters.size(); ++I)
        visitTypeArguments(F, Fam, Parameters[I], Arguments[I], Deduce);
    }
    return;
  }
  const TypeApplication *App = nullptr;
  size_t Open;
  if (auto Owner = matchOwnerPattern(F.U, Fam, Formal, Actual)) {
    visitTypeArguments(F, Fam, Owner->FormalOwner, Owner->ActualOwner, Deduce);
    Formal = Owner->Member;
    Open = Formal.find('<');
    auto It = F.U.TypeApplications.find(Actual.str());
    if (Open != StringRef::npos && It != F.U.TypeApplications.end())
      App = &It->second;
  } else
    App = matchingApplication(F.U, Fam, Formal, Actual, Open);
  if (!App)
    return;
  const auto Params = splitArguments(Formal.slice(Open + 1, Formal.size() - 1));
  if (Params.size() != App->Arguments.size())
    return;
  for (size_t I = 0; I < Params.size(); ++I) {
    const auto &Arg = App->Arguments[I];
    if (Arg.IR)
      Deduce(Params[I], Arg);
    else
      visitTypeArguments(F, Fam, Params[I], Arg.Type, Deduce);
  }
}

void inferNestedPack(Frame &F, const Family &Fam, StringRef Formal,
                     StringRef Actual, const std::set<std::string> &Pack,
                     llvm::function_ref<void(size_t)> DeduceCount,
                     const Token &At) {
  for (StringRef Suffix : {"&&", "&", "*"}) {
    if (Formal.ends_with(Suffix) && Actual.ends_with(Suffix)) {
      inferNestedPack(F, Fam, Formal.drop_back(Suffix.size()),
                      Actual.drop_back(Suffix.size()), Pack, DeduceCount, At);
      return;
    }
  }
  if (Formal.starts_with("const<") && Formal.ends_with(">") &&
      Actual.starts_with("const<") && Actual.ends_with(">")) {
    inferNestedPack(F, Fam, Formal.slice(6, Formal.size() - 1),
                    Actual.slice(6, Actual.size() - 1), Pack, DeduceCount, At);
    return;
  }
  if (Formal.ends_with("]") && Actual.ends_with("]")) {
    inferNestedPack(F, Fam, Formal.take_front(Formal.rfind('[')),
                    Actual.take_front(Actual.rfind('[')), Pack, DeduceCount,
                    At);
    return;
  }
  auto InferList = [&](StringRef List, llvm::ArrayRef<Value> Arguments) {
    const auto Patterns = splitArguments(List);
    const size_t Expansions = llvm::count_if(Patterns, [&](StringRef P) {
      return P.consume_back("...") && substitute(P, Pack, 0) != P;
    });
    const size_t Fixed = Patterns.size() - Expansions;
    if (Arguments.size() < Fixed || (!Expansions && Arguments.size() != Fixed))
      return;
    size_t Count = 0;
    if (Expansions) {
      size_t Remaining = Arguments.size() - Fixed;
      if (Remaining % Expansions)
        throw DeductionFailure{{At, "inconsistent nested pack pattern arity"}};
      Count = Remaining / Expansions;
      DeduceCount(Count);
    }
    size_t I = 0;
    for (StringRef P : Patterns) {
      if (P.consume_back("...") && substitute(P, Pack, 0) != P)
        I += Count;
      else {
        const auto &Arg = Arguments[I++];
        if (!Arg.IR)
          inferNestedPack(F, Fam, P, Arg.Type, Pack, DeduceCount, At);
      }
    }
  };
  if (auto P = splitCallableType(Formal)) {
    if (auto A = splitCallableType(Actual)) {
      inferNestedPack(F, Fam, P->Result, A->Result, Pack, DeduceCount, At);
      std::vector<Value> Arguments;
      for (const auto &Argument : splitArguments(A->Parameters))
        Arguments.emplace_back(Argument);
      InferList(P->Parameters, Arguments);
    }
    return;
  }
  if (auto Owner = matchOwnerPattern(F.U, Fam, Formal, Actual)) {
    inferNestedPack(F, Fam, Owner->FormalOwner, Owner->ActualOwner, Pack,
                    DeduceCount, At);
    auto Open = Owner->Member.find('<');
    auto It = F.U.TypeApplications.find(Actual.str());
    if (Open != StringRef::npos && It != F.U.TypeApplications.end())
      InferList(Owner->Member.slice(Open + 1, Owner->Member.size() - 1),
                It->second.Arguments);
  } else {
    size_t Open;
    if (auto *App = matchingApplication(F.U, Fam, Formal, Actual, Open))
      InferList(Formal.slice(Open + 1, Formal.size() - 1), App->Arguments);
  }
}
// Compare the admitted structural type patterns symbolically. A repeated
// parameter has to match the same pattern at every occurrence.
bool acceptsPattern(const Node &General, const Node &Specific) {
  std::set<std::string> Variables;
  for (auto &P : General.Generics)
    Variables.insert(P.Text);
  std::map<std::string, std::string> Bound;
  StringRef Pack;
  if (!General.Generics.empty() && General.Generics.back().Pack)
    Pack = General.Generics.back().Text;
  std::optional<std::pair<size_t, bool>> PackShape;
  std::optional<size_t> PackIndex;
  auto MatchList = [&](llvm::ArrayRef<std::string> Left,
                       llvm::ArrayRef<std::string> Right,
                       llvm::function_ref<bool(StringRef, StringRef)> Match) {
    auto Splice = [](StringRef S) { return S.ends_with("..."); };
    const size_t LC = llvm::count_if(Left, Splice);
    const size_t RC = llvm::count_if(Right, Splice);
    if (LC > 1 || RC > 1 || (LC && !Splice(Left.back())) ||
        (RC && !Splice(Right.back())))
      return false;
    const size_t LF = Left.size() - LC, RF = Right.size() - RC;
    if (LF > RF || (!LC && (RC || LF != RF)))
      return false;
    for (size_t I = 0; I < LF; ++I)
      if (!Match(Left[I], Right[I]))
        return false;
    if (!LC)
      return true;
    const auto Shape = std::make_pair(RF - LF, RC != 0);
    if (PackShape && *PackShape != Shape)
      return false;
    PackShape = Shape;
    auto Expanded = StringRef(Left.back()).drop_back(3);
    for (size_t I = LF; I < Right.size(); ++I) {
      StringRef Target = Right[I];
      if (RC && I == RF)
        Target = Target.drop_back(3);
      llvm::SaveAndRestore Index(PackIndex);
      PackIndex = I - LF;
      if (!Match(Expanded, Target))
        return false;
    }
    return true;
  };
  auto Match = [&](auto &&Self, llvm::StringRef A, llvm::StringRef B) -> bool {
    if (Variables.count(A.str())) {
      std::string Name = A.str();
      if (A == Pack && PackIndex)
        Name += "$" + std::to_string(*PackIndex);
      auto [It, New] = Bound.emplace(std::move(Name), B.str());
      return New || It->second == B;
    }
    for (auto S : {"&&", "&", "*"})
      if (A.consume_back(S))
        return B.consume_back(S) && Self(Self, A, B);
    if (A.consume_front("const<") && A.consume_back(">"))
      return B.consume_front("const<") && B.consume_back(">") &&
             Self(Self, A, B);
    if (A.ends_with("]") && B.ends_with("]")) {
      auto I = A.rfind('['), J = B.rfind('[');
      return I != llvm::StringRef::npos && J != llvm::StringRef::npos &&
             Self(Self, A.take_front(I), B.take_front(J)) &&
             Self(Self, A.slice(I + 1, A.size() - 1),
                  B.slice(J + 1, B.size() - 1));
    }
    if (auto L = splitCallableType(A)) {
      auto R = splitCallableType(B);
      if (!R || L->Flags != R->Flags || !Self(Self, L->Result, R->Result))
        return false;
      auto LP = splitArguments(L->Parameters),
           RP = splitArguments(R->Parameters);
      return MatchList(
          LP, RP, [&](StringRef P, StringRef Q) { return Self(Self, P, Q); });
    }
    auto I = A.find('<'), J = B.find('<');
    if (I != llvm::StringRef::npos && J != llvm::StringRef::npos &&
        A.take_front(I) == B.take_front(J)) {
      auto L = splitArguments(A.slice(I + 1, A.size() - 1));
      auto R = splitArguments(B.slice(J + 1, B.size() - 1));
      return MatchList(
          L, R, [&](StringRef P, StringRef Q) { return Self(Self, P, Q); });
    }
    return A == B;
  };
  std::vector<std::string> Left, Right;
  for (const auto &P : General.Params)
    Left.push_back(P.Type + (P.Pack ? "..." : ""));
  for (const auto &P : Specific.Params)
    Right.push_back(P.Type + (P.Pack ? "..." : ""));
  return MatchList(Left, Right, [&](StringRef L, StringRef R) {
    return Match(Match, L, R);
  });
}
std::string substituteBinders(llvm::StringRef Text, const Node &Decl,
                              const Node *New) {
  std::string Key;
  while (!Text.empty()) {
    auto Word = Text.take_while([](char C) {
      return llvm::isAlnum(C) || C == '_' || C == '$' ||
             static_cast<unsigned char>(C) >= 128;
    });
    if (Word.empty()) {
      Key += Text.front();
      Text = Text.drop_front();
      continue;
    }
    auto I =
        llvm::find_if(Decl.Generics, [&](auto &G) { return G.Text == Word; });
    if (I == Decl.Generics.end())
      Key += Word.str();
    else {
      size_t Pos = I - Decl.Generics.begin();
      Key += New ? New->Generics[Pos].Text : "$" + std::to_string(Pos);
    }
    Text = Text.drop_front(Word.size());
  }
  return Key;
}
std::string normalized(llvm::StringRef Text, const Node &Decl) {
  return substituteBinders(Text, Decl, nullptr);
}
std::string numberSpelling(const Node &N) {
  llvm::SmallString<32> Digits;
  integerLiteral(N.At).toString(Digits, 10, false);
  return Digits.str().str();
}
Node normalizedValueContracts(const Node &Decl) {
  Node Copy;
  Copy.Params = Decl.Params;
  Copy.Contracts = Decl.Contracts;
  normalizeContracts(Copy);
  auto Bind = [&](auto &&Self, Node &N) -> void {
    if (N.K == Node::Name) {
      // A generic binder can be the head of a dependent qualified name.
      // Member names, qualified tail components, and literals keep their
      // spelling.
      auto Head = llvm::StringRef(N.Text).take_until(
          [](char C) { return C == ':' || C == '<'; });
      if (llvm::any_of(Decl.Generics,
                       [&](const Node &G) { return G.Text == Head; }))
        N.Text = normalized(Head, Decl) + N.Text.substr(Head.size());
    } else if (N.K == Node::TypeArg) {
      // A type argument's token text is only its leading source token.
      N.Text.clear();
    }
    N.Type = normalized(N.Type, Decl);
    for (auto &A : N.TemplateArgs)
      Self(Self, A);
    for (auto &C : N.Children)
      Self(Self, C);
  };
  for (auto &Clause : Copy.Contracts)
    Bind(Bind, Clause);
  return Copy;
}
std::string atom(const Node &N, const Node &Decl) {
  auto Spelling =
      N.K == Node::Number ? numberSpelling(N) : normalized(N.Text, Decl);
  std::string Key =
      std::to_string(N.K) + "(" + Spelling + "|" + normalized(N.Type, Decl);
  for (const auto &A : N.TemplateArgs)
    Key += "<" + atom(A, Decl) + ">";
  for (const auto &C : N.Children)
    Key += "[" + atom(C, Decl) + "]";
  return Key + ")";
}
std::set<std::string> requirements(const Node &Decl) {
  std::set<std::string> Set;
  auto Add = [&](auto &&Self, const Node &R) -> void {
    if (R.K == Node::Binary && R.Text == "&&") {
      Self(Self, R.Children[0]);
      Self(Self, R.Children[1]);
    } else
      Set.insert(atom(R, Decl));
  };
  for (auto &Req : Decl.TemplateArgs)
    Add(Add, Req);
  return Set;
}

enum class PatternMatch { Established, Different, Unestablished };

struct SymbolicValue {
  std::optional<Value> Concrete;
  std::string Key;
  std::set<std::string> Parameters;
  bool Rigid = false;
};
using SymbolicValues = std::map<std::string, SymbolicValue>;

bool expressionUses(const Node &N, StringRef Binder) {
  const std::set<std::string> Name{Binder.str()};
  if ((N.K == Node::Name && substitute(N.Text, Name, 0) != N.Text) ||
      substitute(N.Type, Name, 0) != N.Type)
    return true;
  auto Visit = [&](const Node &C) { return expressionUses(C, Binder); };
  return llvm::any_of(N.Children, Visit) || llvm::any_of(N.TemplateArgs, Visit);
}

std::string constantIdentity(const Value &V) {
  auto *C = llvm::dyn_cast_or_null<llvm::ConstantInt>(V.IR);
  if (!C)
    return {};
  llvm::SmallString<32> Digits;
  C->getValue().toString(Digits, 10, signedType(V.Type));
  return V.Type + "(" + Digits.str().str() + ")";
}

SymbolicValue symbolicValue(Frame &F, const Family &Family, const Node &Expr,
                            const std::string &Domain,
                            const SymbolicValues &Bindings) {
  if (Expr.K == Node::Name) {
    if (auto I = Bindings.find(Expr.Text); I != Bindings.end()) {
      if (!I->second.Concrete || I->second.Concrete->Type == Domain)
        return I->second;
    }
  }
  Frame Probe(F.U, nullptr, nullptr, Family.Prefix);
  Probe.Opt = Family.Site.Configuration;
  Probe.LookupLimit = Family.Site.Through;
  Probe.Env = Family.Enclosing;
  bool NeedsSymbols = false;
  for (const auto &Parameter : Family.Decl.Generics) {
    auto I = Bindings.find(Parameter.Text);
    if (I != Bindings.end() && I->second.Concrete)
      Probe.Env.Values[Parameter.Text] = *I->second.Concrete;
    else if (expressionUses(Expr, Parameter.Text))
      NeedsSymbols = true;
  }
  if (!NeedsSymbols) {
    try {
      auto V = Probe.convert(Probe.constantEval(Expr), Domain, Expr.At);
      auto Key = constantIdentity(V);
      if (!Key.empty())
        return SymbolicValue{V, std::move(Key), {}, false};
    } catch (const ResourceExhausted &) {
      throw;
    } catch (const Diagnostic &) {
      // A comparison against a symbolic head can fail to establish a
      // value that the concrete use itself never needs to evaluate.
    }
    return {};
  }
  auto Compose = [&](auto &&Visit, const Node &N) -> SymbolicValue {
    if (N.K == Node::Name) {
      if (auto I = Bindings.find(N.Text); I != Bindings.end())
        return I->second;
      if (N.Text == "true" || N.Text == "false")
        return {{}, N.Text, {}, false};
      return {};
    }
    if (N.K == Node::Number)
      return {{}, "numeric:" + numberSpelling(N), {}, false};
    if (N.K != Node::Unary && N.K != Node::Binary && N.K != Node::Conditional)
      return {};
    SymbolicValue Result;
    Result.Key = std::to_string(N.K) + ":" + N.Text + "(";
    for (const auto &Child : N.Children) {
      auto Part = Visit(Visit, Child);
      if (Part.Key.empty())
        return {};
      Result.Key += Part.Key + ",";
      Result.Parameters.insert(Part.Parameters.begin(), Part.Parameters.end());
    }
    Result.Key += ")";
    return Result;
  };
  auto Result = Compose(Compose, Expr);
  if (!Result.Key.empty())
    Result.Key +=
        "@" + Domain + "/" + Probe.Opt.Overflow + "/" + Probe.Opt.DefaultInt;
  return Result;
}

PatternMatch compareTerms(const SymbolicValue &Expected,
                          const SymbolicValue &Found) {
  if (Expected.Key.empty() || Found.Key.empty())
    return PatternMatch::Unestablished;
  if (Expected.Key == Found.Key)
    return PatternMatch::Established;
  if ((Expected.Concrete && Found.Concrete) ||
      (Expected.Rigid && !Found.Parameters.count(Expected.Key)) ||
      (Found.Rigid && !Expected.Parameters.count(Found.Key)))
    return PatternMatch::Different;
  return PatternMatch::Unestablished;
}

PatternMatch compareSpecializationHeads(Frame &F, const Family &General,
                                        const Node &GeneralTypes,
                                        const Family &Specific,
                                        const Node &SpecificTypes,
                                        const std::vector<Node> &Domains,
                                        const Substitution &Actual,
                                        const Token &At) {
  F.U.chargeSolver(At);
  if (!acceptsPattern(GeneralTypes, SpecificTypes))
    return PatternMatch::Different;
  SymbolicValues Rigid, Deduced;
  for (const auto &Parameter : Specific.Decl.Generics) {
    if (Parameter.K != Node::ValueParam)
      continue;
    auto Key = "$value." + std::to_string(Rigid.size()) + ":" + Parameter.Type;
    Rigid.emplace(Parameter.Text, SymbolicValue{{}, Key, {Key}, true});
  }
  auto Outcome = PatternMatch::Established;
  auto Satisfy = [&](PatternMatch Match) {
    if (Match != PatternMatch::Established)
      Outcome = Match;
    return Outcome != PatternMatch::Different;
  };
  std::vector<std::pair<size_t, SymbolicValue>> Deferred;
  for (size_t I = 0; I < Domains.size(); ++I) {
    if (Domains[I].K == Node::TypeParam)
      continue;
    const auto &Expected = General.Decl.Pattern[I];
    auto Found = symbolicValue(F, Specific, Specific.Decl.Pattern[I],
                               Actual.Values.at(Domains[I].Text).Type, Rigid);
    if (Expected.K == Node::Name &&
        llvm::any_of(General.Decl.Generics, [&](const Node &Parameter) {
          return Parameter.K == Node::ValueParam &&
                 Parameter.Text == Expected.Text;
        })) {
      auto [Binding, New] = Deduced.try_emplace(Expected.Text, Found);
      if (!New && !Satisfy(compareTerms(Binding->second, Found)))
        return Outcome;
    } else {
      Deferred.emplace_back(I, std::move(Found));
    }
  }
  for (const auto &[I, Found] : Deferred) {
    auto Expected =
        symbolicValue(F, General, General.Decl.Pattern[I],
                      Actual.Values.at(Domains[I].Text).Type, Deduced);
    if (!Satisfy(compareTerms(Expected, Found)))
      break;
  }
  return Outcome;
}
} // namespace
std::string cpn::rebindTypeNames(llvm::StringRef Text, const Node &Old,
                                 const Node &New) {
  return substituteBinders(Text, Old, &New);
}
bool cpn::betterPattern(const Node &A, const Node &B) {
  if (A.Generics.empty() || B.Generics.empty())
    return A.Generics.empty() && !B.Generics.empty() && B.TemplateArgs.empty();
  return betterTypePattern(A, B);
}
bool cpn::betterTypePattern(const Node &A, const Node &B) {
  if (!acceptsPattern(B, A))
    return false;
  if (!acceptsPattern(A, B))
    return true;
  auto Left = requirements(A), Right = requirements(B);
  return Left.size() > Right.size() &&
         std::includes(Left.begin(), Left.end(), Right.begin(), Right.end());
}
bool cpn::sameGenericResult(const Node &A, const Node &B) {
  return normalized(A.Type, A) == normalized(B.Type, B);
}
bool cpn::sameGenericValueContracts(const Node &A, const Node &B) {
  return sameContracts(normalizedValueContracts(A),
                       normalizedValueContracts(B));
}

bool cpn::sameGenericArgument(const Node &A, const Node &B, const Node &From,
                              const Node &To) {
  if (A.K != B.K || A.Pack != B.Pack || A.Definition != B.Definition ||
      A.ExplicitApplication != B.ExplicitApplication ||
      A.Settings != B.Settings || A.Children.size() != B.Children.size() ||
      A.TemplateArgs.size() != B.TemplateArgs.size() ||
      normalized(A.Type, From) != normalized(B.Type, To))
    return false;
  if (A.K == Node::Number) {
    auto X = integerLiteral(A.At), Y = integerLiteral(B.At);
    unsigned W = std::max(X.getBitWidth(), Y.getBitWidth());
    if (X.zextOrTrunc(W) != Y.zextOrTrunc(W))
      return false;
  } else if (A.K != Node::TypeArg && A.K != Node::Call &&
             normalized(A.Text, From) != normalized(B.Text, To))
    return false;
  auto Match = [&](const Node &L, const Node &R) {
    return sameGenericArgument(L, R, From, To);
  };
  return std::equal(A.Children.begin(), A.Children.end(), B.Children.begin(),
                    Match) &&
         std::equal(A.TemplateArgs.begin(), A.TemplateArgs.end(),
                    B.TemplateArgs.begin(), Match);
}

EffectBound cpn::genericEffectBound(const Node &D, bool HasReceiver) {
  auto E = D.Settings.find("effects");
  if (E == D.Settings.end())
    return std::nullopt;
  auto Bound = bindEffectNames(E->second, D.Params, HasReceiver, D.At);
  if (D.Noexcept && Bound.count("throw"))
    fail(D.At, "noexcept contradicts a throw effect");
  return Bound;
}
bool cpn::sameGenericSignature(const Node &A, const Node &B) {
  auto category = [](const Node &N) {
    auto I = N.Settings.find("category");
    return I == N.Settings.end() ? std::string() : I->second;
  };
  if (A.Const != B.Const || category(A) != category(B))
    return false;
  if (A.Generics.size() != B.Generics.size() ||
      A.Params.size() != B.Params.size())
    return false;
  for (size_t I = 0; I < A.Generics.size(); ++I) {
    auto &L = A.Generics[I], &R = B.Generics[I];
    if (L.K != R.K || L.Pack != R.Pack ||
        normalized(L.Type, A) != normalized(R.Type, B))
      return false;
  }
  for (size_t I = 0; I < A.Params.size(); ++I)
    if (normalized(A.Params[I].Type, A) != normalized(B.Params[I].Type, B) ||
        A.Params[I].Pack != B.Params[I].Pack)
      return false;
  return requirements(A) == requirements(B);
}

size_t Frame::deducePackArity(const Family &Fam, const Node &Call,
                              llvm::ArrayRef<Value> Actual) {
  const auto &D = Fam.Decl;
  const size_t Fixed = D.Generics.size() - 1;
  if (Call.TemplateArgs.size() > Fixed)
    return Call.TemplateArgs.size() - Fixed;
  std::optional<size_t> Count;
  auto Establish = [&](size_t N) {
    if (Count && *Count != N)
      throw DeductionFailure{{Call.At, "conflicting deduced pack lengths"}};
    Count = N;
  };
  const size_t Expanded =
      llvm::count_if(D.Params, [](const Node &P) { return P.Pack; });
  const size_t FixedParams = D.Params.size() - Expanded;
  if (Expanded && Actual.size() >= FixedParams) {
    const size_t Remaining = Actual.size() - FixedParams;
    if (Remaining % Expanded)
      throw DeductionFailure{{Call.At, "inconsistent parameter pack arity"}};
    Establish(Remaining / Expanded);
  }
  const std::set<std::string> Pack{D.Generics.back().Text};
  size_t I = 0;
  for (const auto &Param : D.Params) {
    if (Param.Pack) {
      I += Count.value_or(0);
      continue;
    }
    if (I >= Actual.size())
      break;
    StringRef Formal;
    auto Type = deductionType(Param.Type, Actual[I++], Formal);
    inferNestedPack(*this, Fam, Formal, Type, Pack, Establish, Call.At);
  }
  return Count.value_or(0);
}

std::optional<Value>
Frame::deduceGenericArgument(const Family &Fam, const Node &Param,
                             llvm::ArrayRef<Value> Actual, const Token &At,
                             const std::string &ValueType) {
  std::optional<Value> Result;
  auto Establish = [&](StringRef Name, Value Candidate) {
    if (Name != Param.Text || bool(Candidate.IR) != !ValueType.empty())
      return;
    try {
      if (!ValueType.empty())
        Candidate = convert(Candidate, ValueType, At);
      else
        Candidate.Type = materializationType(Candidate.Type, At);
    } catch (const ResourceExhausted &) {
      throw;
    } catch (const Diagnostic &D) {
      throw DeductionFailure{D};
    }
    if (Result &&
        (Result->Type != Candidate.Type || Result->IR != Candidate.IR))
      throw DeductionFailure{{At, "conflicting deduction"}};
    Result = std::move(Candidate);
  };
  for (size_t I = 0; I < Actual.size() && I < Fam.Decl.Params.size(); ++I) {
    StringRef Formal;
    auto Type = deductionType(Fam.Decl.Params[I].Type, Actual[I], Formal);
    visitTypeArguments(*this, Fam, Formal, Type, Establish);
  }
  return Result;
}

Family cpn::expand(const Family &Source, size_t Count, const Token &At) {
  Family Result = Source;
  auto &D = Result.Decl;
  auto P = D.Generics.back();
  std::set<std::string> Names{P.Text};
  auto InnerPacks = [&](const Node &N, std::set<std::string> Inherited) {
    if (&N != &D && !N.Generics.empty() && N.Generics.back().Pack)
      Inherited.insert(N.Generics.back().Text);
    for (const auto &Param : N.Params)
      if (Param.Pack && substitute(Param.Type, Inherited, 0) != Param.Type)
        Inherited.insert(Param.Text);
    return Inherited;
  };
  auto collect = [&](auto &&Visit, const Node &N,
                     const std::set<std::string> &Inherited) -> void {
    auto Deferred = InnerPacks(N, Inherited);
    for (auto &Param : N.Params)
      if (Param.Pack && !Deferred.count(Param.Text))
        Names.insert(Param.Text);
    for (auto &Child : N.Children)
      Visit(Visit, Child, Deferred);
  };
  collect(collect, D, {});
  std::set<std::string> Deferred;
  auto InvolvesDeferred = [&](auto &&Visit, const Node &N) -> bool {
    if (substitute(N.Text, Deferred, 0) != N.Text ||
        substitute(N.Type, Deferred, 0) != N.Type)
      return true;
    auto Includes = [&](const Node &C) { return Visit(Visit, C); };
    return llvm::any_of(N.Children, Includes) ||
           llvm::any_of(N.TemplateArgs, Includes);
  };
  std::function<void(Node &, std::optional<size_t>)> transform;
  std::function<void(std::vector<Node> &, std::optional<size_t>)> sequence =
      [&](std::vector<Node> &Nodes, std::optional<size_t> I) {
        std::vector<Node> Out;
        for (auto N : Nodes) {
          if (N.Pack && !InvolvesDeferred(InvolvesDeferred, N)) {
            N.Pack = false;
            for (size_t J = 0; J < Count; ++J) {
              auto Copy = N;
              transform(Copy, J);
              Out.push_back(std::move(Copy));
            }
          } else {
            transform(N, I);
            Out.push_back(std::move(N));
          }
        }
        Nodes = std::move(Out);
      };
  transform = [&](Node &N, std::optional<size_t> I) {
    llvm::SaveAndRestore Scope(Deferred);
    Deferred = InnerPacks(N, Deferred);
    auto Active = Names;
    for (const auto &Hidden : Deferred)
      Active.erase(Hidden);
    if (!I && N.K == Node::Name && Active.count(N.Text))
      fail(N.At, "unexpanded pack in expression");
    N.Text = expandPackLists(N.Text, Active, Count, I, N.At, Deferred);
    N.At.Text = expandPackLists(N.At.Text, Active, Count, I, N.At, Deferred);
    N.Type = expandPackLists(N.Type, Active, Count, I, N.At, Deferred);
    if (auto E = N.Settings.find("effects"); E != N.Settings.end()) {
      std::string Bound;
      auto Add = [&](llvm::StringRef Effect) {
        if (!Bound.empty())
          Bound += ",";
        Bound += Effect;
      };
      llvm::SmallVector<llvm::StringRef> Items;
      llvm::StringRef(E->second).split(Items, ',');
      for (auto Item : Items) {
        const auto [Kind, Region] = Item.split(':');
        bool Pack = Kind != "trap" && Region != "any" && Region != "global" &&
                    Region != "this" &&
                    llvm::any_of(N.Params, [&](const Node &Param) {
                      return Param.Pack && Param.Text == Region &&
                             !Deferred.count(Param.Text);
                    });
        if (!Pack)
          Add(Item);
        else
          for (size_t J = 0; J < Count; ++J)
            Add(Item.str() + "$" + std::to_string(J));
      }
      E->second = Bound.empty() ? "none" : std::move(Bound);
    }
    if (&N != &D)
      sequence(N.Generics, I);
    sequence(N.Params, I);
    sequence(N.Children, I);
    sequence(N.TemplateArgs, I);
    sequence(N.Pattern, I);
    sequence(N.Contracts, I);
  };
  sequence(D.Generics, {});
  transform(D, {});
  return Result;
}
void Context::chargeInstance(const Token &At) {
  if (Instantiations >= Opt.MaxInstantiations)
    throw ResourceExhausted{{At, "generic instantiation resource exhausted"}};
  ++Instantiations;
}
void Context::chargeSolver(const Token &At) {
  if (SolverSteps >= Opt.MaxSolverSteps)
    throw ResourceExhausted{{At, "generic solver step resource exhausted"}};
  ++SolverSteps;
}
void Context::checkNormalForm(const Node &N) {
  uint64_t Count = 0;
  auto Visit = [&](auto &&Self, const Node &Item) -> void {
    if (++Count > Opt.MaxNormalNodes)
      throw ResourceExhausted{
          {Item.At, "generic normalization resource exhausted"}};
    for (const auto &Child : Item.Children)
      Self(Self, Child);
    for (const auto &Arg : Item.TemplateArgs)
      Self(Self, Arg);
  };
  Visit(Visit, N);
}
bool cpn::builtinPredicate(llvm::StringRef Name) {
  return Name == "SameType" || Name == "ObjectType" || Name == "CompleteType" ||
         Name == "CopyConstructible" || Name == "MoveConstructible";
}
const Family *Frame::constraint(const std::string &Name) const {
  auto Key = scopeKey(Prefix, Name, [&](const std::string &K) {
    auto It = U.Constraints.find(K);
    return It != U.Constraints.end() && It->second.Site.Through <= LookupLimit;
  });
  return Key.empty() ? nullptr : &U.Constraints.at(Key);
}
bool Frame::predicate(const Node &N) {
  U.chargeSolver(N.At);
  if (builtinPredicate(N.Text)) {
    if (N.TemplateArgs.size() != (N.Text == "SameType" ? 2u : 1u))
      fail(N.At, "invalid number of predicate type arguments");
    auto T = resolve(N.TemplateArgs[0].Type, N.At);
    if (N.Text == "SameType")
      return T == resolve(N.TemplateArgs[1].Type, N.At);
    if (T == "void" || llvm::StringRef(T).ends_with("&"))
      return false;
    if (N.Text == "ObjectType" || N.Text == "CompleteType")
      return N.Text == "ObjectType" || U.ir(T, N.At)->isSized();
    return constructible(T,
                         N.Text == "CopyConstructible"
                             ? SpecialOperation::CopyConstruct
                             : SpecialOperation::MoveConstruct,
                         N.At);
  }
  auto C = *constraint(N.Text);
  if (!C.Decl.Generics.empty() && C.Decl.Generics.back().Pack) {
    auto Fixed = C.Decl.Generics.size() - 1;
    C = expand(
        C, N.TemplateArgs.size() > Fixed ? N.TemplateArgs.size() - Fixed : 0,
        N.At);
  }
  llvm::SaveAndRestore Depth(U.SpecializationDepth, U.SpecializationDepth + 1);
  if (U.SpecializationDepth > 128)
    throw ResourceExhausted{
        {N.At, "constraint evaluation nesting resource exhausted"}};
  auto S = bind(C, N.TemplateArgs, {}, N.At);
  auto *Fn = llvm::Function::Create(
      llvm::FunctionType::get(B.getVoidTy(), false),
      llvm::GlobalValue::InternalLinkage, "cpn.requirement", U.M);
  EnterDefinition Site(U, C.Site);
  Frame Probe(U, nullptr, Fn, C.Prefix);
  Probe.Env = std::move(S);
  Probe.B.SetInsertPoint(Probe.block("entry"));
  bool OK = true;
  try {
    for (auto &R : C.Decl.Children) {
      if (!OK)
        break;
      U.chargeSolver(R.At);
      Probe.Scopes.emplace_back();
      if (R.Text == "type")
        Probe.resolve(R.Type, R.At);
      else if (R.Text == "requires")
        OK &=
            !llvm::cast<llvm::ConstantInt>(Probe.constantEval(R.Children[0]).IR)
                 ->isZero();
      else {
        for (auto &P : R.Params) {
          auto T = Probe.resolve(P.Type, P.At);
          while (llvm::StringRef(T).ends_with("&"))
            T.pop_back();
          bool RO = llvm::StringRef(T).starts_with("const<") && T.back() == '>';
          if (RO)
            T = T.substr(6, T.size() - 7);
          Probe.Scopes.back().Names[P.Text] = {
              T, nullptr, Probe.allocate(T, P.At), RO || P.Const};
        }
        for (auto &E : R.Children) {
          U.chargeSolver(E.At);
          Probe.RequireNoexcept = E.Noexcept;
          auto V = Probe.eval(E);
          auto T = Probe.resolve(E.Type, E.At);
          bool Xvalue = llvm::StringRef(T).ends_with("&&");
          bool Reference = llvm::StringRef(T).ends_with("&");
          if (Reference)
            T.resize(T.size() - (Xvalue ? 2 : 1));
          bool Const =
              llvm::StringRef(T).starts_with("const<") && T.back() == '>';
          if (Const)
            T = T.substr(6, T.size() - 7);
          if (V.Type != T ||
              (Reference ? (!V.Address || V.Prvalue || V.Expiring != Xvalue ||
                            V.Readonly != Const)
                         : (V.Address && !V.Prvalue))) {
            OK = false;
            break;
          }
        }
      }
      Probe.Scopes.pop_back();
    }
  } catch (const ResourceExhausted &) {
    Fn->eraseFromParent();
    throw;
  } catch (const Diagnostic &) {
    OK = false;
  }
  Fn->eraseFromParent();
  return OK;
}

// Deduce each specialization's own parameters from the primary's canonical
// arguments. Only matched heads enter constraint evaluation and ordering.
void Frame::selectTypeSpecialization(const std::string &Key, Family &Primary,
                                     Substitution &Actual, const Token &At) {
  auto Group = U.Specializations.find(Key);
  if (Group == U.Specializations.end())
    return;
  struct Candidate {
    Family Definition;
    Node Head;
    Substitution Env;
    bool VariableArity;
  };
  auto Better = [&](const Candidate &A, const Candidate &B) {
    auto AB =
        compareSpecializationHeads(*this, A.Definition, A.Head, B.Definition,
                                   B.Head, Primary.Decl.Generics, Actual, At);
    auto BA =
        compareSpecializationHeads(*this, B.Definition, B.Head, A.Definition,
                                   A.Head, Primary.Decl.Generics, Actual, At);
    if (AB == PatternMatch::Different && BA == PatternMatch::Established)
      return true;
    if (AB == PatternMatch::Established && BA == PatternMatch::Different)
      return false;
    if (AB == PatternMatch::Different && BA == PatternMatch::Different)
      return false;
    if (A.VariableArity != B.VariableArity && AB == PatternMatch::Established &&
        BA == PatternMatch::Established)
      return !A.VariableArity;
    auto Left = requirements(A.Head), Right = requirements(B.Head);
    return Left.size() > Right.size() &&
           std::includes(Left.begin(), Left.end(), Right.begin(), Right.end());
  };
  std::vector<Candidate> Best;
  for (const auto &Declaration : Group->second) {
    if (Declaration.Site.Through > LookupLimit)
      continue;
    Family Spec = Declaration;
    const bool Packed =
        !Spec.Decl.Generics.empty() && Spec.Decl.Generics.back().Pack;
    if (Packed) {
      const auto &Patterns = Spec.Decl.Pattern;
      const auto &Params = Primary.Decl.Generics;
      const size_t Expansions =
          llvm::count_if(Patterns, [](const Node &P) { return P.Pack; });
      const size_t Fixed = Patterns.size() - Expansions;
      if (Params.size() < Fixed || (!Expansions && Params.size() != Fixed))
        continue;
      std::optional<size_t> Count;
      auto Establish = [&](size_t N) {
        if (Count && *Count != N)
          throw DeductionFailure{
              {At, "conflicting specialization pack lengths"}};
        Count = N;
      };
      if (Expansions) {
        const size_t Remaining = Params.size() - Fixed;
        if (Remaining % Expansions)
          continue;
        Establish(Remaining / Expansions);
      }
      const std::set<std::string> Pack{Spec.Decl.Generics.back().Text};
      size_t I = 0;
      try {
        for (const auto &Pattern : Patterns) {
          if (Pattern.Pack) {
            I += Count.value_or(0);
            continue;
          }
          const auto &Param = Params[I++];
          if (Param.K == Node::TypeParam && Pattern.K == Node::TypeArg)
            inferNestedPack(*this, Spec, Pattern.Type,
                            Actual.Types.at(Param.Text), Pack, Establish, At);
        }
      } catch (const DeductionFailure &) {
        continue;
      }
      if (!Count)
        continue;
      Spec = expand(Spec, *Count, At);
    }
    Frame Probe(U, nullptr, nullptr, Spec.Prefix);
    Probe.Opt = Spec.Site.Configuration;
    Probe.LookupLimit = Spec.Site.Through;
    Node Head;
    Head.Generics = Spec.Decl.Generics;
    Head.TemplateArgs = Spec.Decl.Params;
    auto binder = [&](llvm::StringRef Name, Node::Kind K) {
      return llvm::any_of(Head.Generics, [&](const Node &P) {
        return P.K == K && P.Text == Name;
      });
    };
    bool Fits = Spec.Decl.Pattern.size() == Primary.Decl.Generics.size();
    auto Deduce = [&](StringRef Name, Value Arg) {
      if (Arg.IR && binder(Name, Node::ValueParam)) {
        auto [I, New] = Probe.Env.Values.emplace(Name.str(), Arg);
        Fits &= New || I->second.IR == Arg.IR;
      } else if (!Arg.IR && binder(Name, Node::TypeParam)) {
        auto [I, New] = Probe.Env.Types.emplace(Name.str(), Arg.Type);
        Fits &= New || I->second == Arg.Type;
      }
    };
    std::vector<std::pair<const Node *, StringRef>> TypeChecks;
    std::vector<std::pair<const Node *, Value>> ValueChecks;
    for (size_t I = 0; Fits && I < Spec.Decl.Pattern.size(); ++I) {
      const auto &Pattern = Spec.Decl.Pattern[I],
                 &Param = Primary.Decl.Generics[I];
      Node Slot(Node::Parameter, Pattern.At);
      if (Param.K == Node::TypeParam) {
        Fits = Pattern.K == Node::TypeArg;
        if (Fits) {
          StringRef T = Actual.Types.at(Param.Text);
          visitTypeArguments(Probe, Spec, Pattern.Type, T, Deduce);
          TypeChecks.emplace_back(&Pattern, T);
          Slot.Type = normalized(Pattern.Type, Spec.Decl) == Pattern.Type
                          ? T.str()
                          : Pattern.Type;
        }
        Head.Params.push_back(std::move(Slot));
      } else {
        auto V = Actual.Values.at(Param.Text);
        bool Direct =
            Pattern.K == Node::Name && binder(Pattern.Text, Node::ValueParam);
        if (Direct) {
          auto [It, New] = Probe.Env.Values.emplace(Pattern.Text, V);
          Fits = New || It->second.IR == V.IR;
        } else {
          Fits = Pattern.K != Node::TypeArg;
          ValueChecks.emplace_back(&Pattern, V);
        }
      }
    }
    if (!Fits || Probe.Env.Types.size() + Probe.Env.Values.size() !=
                     Head.Generics.size())
      continue;
    for (const auto &[Pattern, T] : TypeChecks)
      if (Probe.resolve(Pattern->Type, At) != T) {
        Fits = false;
        break;
      }
    if (!Fits)
      continue;
    // A computed argument checks previously deduced values. It cannot infer
    // a binder merely because an equation could be solved for it.
    for (const auto &[Pattern, V] : ValueChecks)
      if (Probe.convert(Probe.constantEval(*Pattern), V.Type, At).IR != V.IR) {
        Fits = false;
        break;
      }
    if (!Fits)
      continue;
    if (!Spec.Decl.Params.empty() &&
        !llvm::cast<llvm::ConstantInt>(
             Probe.constantEval(Spec.Decl.Params.front()).IR)
             ->isOne())
      continue;
    Candidate Current{std::move(Spec), std::move(Head), std::move(Probe.Env),
                      Packed};
    if (llvm::any_of(Best, [&](const Candidate &Entry) {
          return Better(Entry, Current);
        }))
      continue;
    llvm::erase_if(
        Best, [&](const Candidate &Entry) { return Better(Current, Entry); });
    Best.push_back(std::move(Current));
  }
  if (Best.size() > 1)
    fail(At, "ambiguous type specialization");
  if (!Best.empty()) {
    Primary = std::move(Best.front().Definition);
    Actual = std::move(Best.front().Env);
  }
}
