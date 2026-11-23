#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
using namespace cpn;
using llvm::StringRef;
namespace {
std::string substitute(StringRef S, const std::set<std::string> &Names,
                       size_t Index) {
  std::string R;
  auto IdentifierByte = [](char C) {
    return llvm::isAlnum(C) || C == '_' || static_cast<unsigned char>(C) >= 128;
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

std::string expandPackLists(StringRef Text, const std::set<std::string> &Names,
                            size_t Count, std::optional<size_t> Index,
                            const Token &At) {
  auto Rewrite = [&](StringRef Part) {
    return Index ? substitute(Part, Names, *Index) : Part.str();
  };
  auto Open = Text.find('<');
  if (!Text.contains("...") || Open == StringRef::npos)
    return Rewrite(Text);
  auto Close = angleEnd(Text, Open);
  if (Close == StringRef::npos)
    return Rewrite(Text);

  std::string Out = Rewrite(Text.take_front(Open + 1));
  bool First = true;
  auto Append = [&](StringRef Arg, std::optional<size_t> I) {
    if (!First)
      Out += ",";
    First = false;
    Out += expandPackLists(Arg, Names, Count, I, At);
  };
  for (const auto &Spelling : splitArguments(Text.slice(Open + 1, Close))) {
    StringRef Arg = Spelling;
    if (!Arg.consume_back("...")) {
      Append(Arg, Index);
      continue;
    }
    if (substitute(Arg, Names, 0) == Arg)
      fail(At, "generic argument expansion requires a pack binding");
    for (size_t I = 0; I < Count; ++I)
      Append(Arg, I);
  }
  Out += ">";
  Out += expandPackLists(Text.drop_front(Close + 1), Names, Count, Index, At);
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
  size_t Open;
  auto *App = matchingApplication(F.U, Fam, Formal, Actual, Open);
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
  size_t Open;
  auto *App = matchingApplication(F.U, Fam, Formal, Actual, Open);
  if (!App)
    return;
  const auto Patterns =
      splitArguments(Formal.slice(Open + 1, Formal.size() - 1));
  const size_t Expansions = llvm::count_if(Patterns, [&](StringRef P) {
    return P.consume_back("...") && substitute(P, Pack, 0) != P;
  });
  const size_t Fixed = Patterns.size() - Expansions;
  if (App->Arguments.size() < Fixed ||
      (!Expansions && App->Arguments.size() != Fixed))
    return;
  size_t Count = 0;
  if (Expansions) {
    size_t Remaining = App->Arguments.size() - Fixed;
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
      const auto &Arg = App->Arguments[I++];
      if (!Arg.IR)
        inferNestedPack(F, Fam, P, Arg.Type, Pack, DeduceCount, At);
    }
  }
}
// Compare the admitted structural type patterns symbolically. A repeated
// parameter has to match the same pattern at every occurrence.
bool acceptsPattern(const Node &General, const Node &Specific) {
  if (General.Params.size() != Specific.Params.size())
    return false;
  std::set<std::string> Variables;
  for (auto &P : General.Generics)
    Variables.insert(P.Text);
  std::map<std::string, std::string> Bound;
  auto Match = [&](auto &&Self, llvm::StringRef A, llvm::StringRef B) -> bool {
    if (Variables.count(A.str())) {
      auto [It, New] = Bound.emplace(A.str(), B.str());
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
    auto I = A.find('<'), J = B.find('<');
    if (I != llvm::StringRef::npos && J != llvm::StringRef::npos &&
        A.take_front(I) == B.take_front(J)) {
      auto L = splitArguments(A.slice(I + 1, A.size() - 1));
      auto R = splitArguments(B.slice(J + 1, B.size() - 1));
      if (L.size() != R.size())
        return false;
      for (size_t K = 0; K < L.size(); ++K)
        if (!Self(Self, L[K], R[K]))
          return false;
      return true;
    }
    return A == B;
  };
  for (size_t I = 0; I < General.Params.size(); ++I)
    if (!Match(Match, General.Params[I].Type, Specific.Params[I].Type))
      return false;
  return true;
}
std::string substituteBinders(llvm::StringRef Text, const Node &Decl,
                              const Node *New) {
  std::string Key;
  while (!Text.empty()) {
    auto Word = Text.take_while([](char C) {
      return llvm::isAlnum(C) || C == '_' ||
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
  std::string Key = std::to_string(N.K) + "(" + normalized(N.Text, Decl) + "|" +
                    normalized(N.Type, Decl);
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
  auto collect = [&](auto &&Visit, const Node &N) -> void {
    for (auto &Param : N.Params)
      if (Param.Pack)
        Names.insert(Param.Text);
    for (auto &Child : N.Children)
      Visit(Visit, Child);
  };
  collect(collect, D);
  std::function<void(Node &, std::optional<size_t>)> transform;
  std::function<void(std::vector<Node> &, std::optional<size_t>)> sequence =
      [&](std::vector<Node> &Nodes, std::optional<size_t> I) {
        std::vector<Node> Out;
        for (auto N : Nodes) {
          if (N.Pack) {
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
    if (!I && N.K == Node::Name && Names.count(N.Text))
      fail(N.At, "unexpanded pack in expression");
    N.Text = expandPackLists(N.Text, Names, Count, I, N.At);
    N.At.Text = expandPackLists(N.At.Text, Names, Count, I, N.At);
    N.Type = expandPackLists(N.Type, Names, Count, I, N.At);
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
                      return Param.Pack && Param.Text == Region;
                    });
        if (!Pack)
          Add(Item);
        else
          for (size_t J = 0; J < Count; ++J)
            Add(Item.str() + "$" + std::to_string(J));
      }
      E->second = Bound.empty() ? "none" : std::move(Bound);
    }
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
  auto Better = [](const Candidate &A, const Candidate &B) {
    if (A.VariableArity != B.VariableArity && acceptsPattern(A.Head, B.Head) &&
        acceptsPattern(B.Head, A.Head))
      return !A.VariableArity;
    return betterTypePattern(A.Head, B.Head);
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
        }
        Slot.Type = Pattern.Type;
      } else {
        auto V = Actual.Values.at(Param.Text);
        bool Direct =
            Pattern.K == Node::Name && binder(Pattern.Text, Node::ValueParam);
        Slot.Type = Direct ? Pattern.Text : atom(Pattern, Spec.Decl);
        if (Direct) {
          auto [It, New] = Probe.Env.Values.emplace(Pattern.Text, V);
          Fits = New || It->second.IR == V.IR;
        } else {
          Fits = Pattern.K != Node::TypeArg;
          ValueChecks.emplace_back(&Pattern, V);
        }
      }
      Head.Params.push_back(std::move(Slot));
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
