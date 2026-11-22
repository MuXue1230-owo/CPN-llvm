#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
using namespace cpn;
namespace {
std::string substitute(llvm::StringRef S, const std::set<std::string> &Names,
                       size_t Index) {
  std::string R;
  while (!S.empty()) {
    if (llvm::isAlnum(S[0]) || S[0] == '_') {
      auto W =
          S.take_while([](char C) { return llvm::isAlnum(C) || C == '_'; });
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
std::string normalized(llvm::StringRef Text, const Node &Decl) {
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
    Key += I == Decl.Generics.end()
               ? Word.str()
               : "$" + std::to_string(I - Decl.Generics.begin());
    Text = Text.drop_front(Word.size());
  }
  return Key;
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
    if (I) {
      N.Text = substitute(N.Text, Names, *I);
      N.At.Text = substitute(N.At.Text, Names, *I);
      N.Type = substitute(N.Type, Names, *I);
    } else if (N.K == Node::Name && Names.count(N.Text))
      fail(N.At, "unexpanded pack in expression");
    sequence(N.Params, I);
    sequence(N.Children, I);
    sequence(N.TemplateArgs, I);
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
    const Family *Source;
    Node Head;
    Substitution Env;
  };
  std::vector<Candidate> Best;
  for (auto &Spec : Group->second) {
    if (Spec.Site.Through > LookupLimit)
      continue;
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
    auto matchType = [&](auto &&Match, llvm::StringRef P,
                         llvm::StringRef T) -> bool {
      if (binder(P, Node::TypeParam)) {
        auto [I, New] = Probe.Env.Types.emplace(P.str(), T.str());
        return New || I->second == T;
      }
      for (auto S : {"&&", "&", "*"})
        if (P.consume_back(S))
          return T.consume_back(S) && Match(Match, P, T);
      if (P.consume_front("const<") && P.consume_back(">"))
        return T.consume_front("const<") && T.consume_back(">") &&
               Match(Match, P, T);
      auto A = P.find('<'), B = T.find('<');
      if (A != llvm::StringRef::npos && B != llvm::StringRef::npos &&
          P.take_front(A) == T.take_front(B)) {
        auto L = splitArguments(P.slice(A + 1, P.size() - 1)),
             R = splitArguments(T.slice(B + 1, T.size() - 1));
        if (L.size() != R.size())
          return false;
        for (size_t I = 0; I < L.size(); ++I)
          if (!Match(Match, L[I], R[I]))
            return false;
        return true;
      }
      return Probe.resolve(P.str(), At) == T;
    };
    bool Fits = Spec.Decl.Pattern.size() == Primary.Decl.Generics.size();
    for (size_t I = 0; Fits && I < Spec.Decl.Pattern.size(); ++I) {
      const auto &Pattern = Spec.Decl.Pattern[I],
                 &Param = Primary.Decl.Generics[I];
      Node Slot(Node::Parameter, Pattern.At);
      if (Param.K == Node::TypeParam) {
        Fits = Pattern.K == Node::TypeArg &&
               matchType(matchType, Pattern.Type, Actual.Types.at(Param.Text));
        Slot.Type = Pattern.Type;
      } else {
        auto V = Actual.Values.at(Param.Text);
        Slot.Type = Pattern.Text;
        if (Pattern.K == Node::Name && binder(Pattern.Text, Node::ValueParam)) {
          auto [It, New] = Probe.Env.Values.emplace(Pattern.Text, V);
          Fits = New || It->second.IR == V.IR;
        } else {
          Fits =
              Pattern.K != Node::TypeArg &&
              Probe.convert(Probe.constantEval(Pattern), V.Type, At).IR == V.IR;
        }
      }
      Head.Params.push_back(std::move(Slot));
    }
    if (!Fits || Probe.Env.Types.size() + Probe.Env.Values.size() !=
                     Head.Generics.size())
      continue;
    if (!Spec.Decl.Params.empty() &&
        !llvm::cast<llvm::ConstantInt>(
             Probe.constantEval(Spec.Decl.Params.front()).IR)
             ->isOne())
      continue;
    if (llvm::any_of(Best, [&](const Candidate &Entry) {
          return betterTypePattern(Entry.Head, Head);
        }))
      continue;
    llvm::erase_if(Best, [&](const Candidate &Entry) {
      return betterTypePattern(Head, Entry.Head);
    });
    Best.push_back({&Spec, std::move(Head), std::move(Probe.Env)});
  }
  if (Best.size() > 1)
    fail(At, "ambiguous type specialization");
  if (!Best.empty()) {
    Primary = *Best.front().Source;
    Actual = std::move(Best.front().Env);
  }
}
