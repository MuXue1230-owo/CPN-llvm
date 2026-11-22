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
    if (P.K == Node::TypeParam)
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
  if (!acceptsPattern(B, A))
    return false;
  if (!acceptsPattern(A, B))
    return true;
  auto Left = requirements(A), Right = requirements(B);
  return Left.size() > Right.size() &&
         std::includes(Left.begin(), Left.end(), Right.begin(), Right.end());
}
bool cpn::sameGenericSignature(const Node &A, const Node &B) {
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
  for (auto &Param : D.Params)
    if (Param.Pack)
      Names.insert(Param.Text);
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
  for (std::string P = Prefix;;) {
    auto It = U.Constraints.find(P + Name);
    if (It != U.Constraints.end() && It->second.Site.Through <= LookupLimit)
      return &It->second;
    if (P.empty())
      return nullptr;
    P.resize(P.size() - 2);
    auto Sep = P.rfind("::");
    P = Sep == std::string::npos ? "" : P.substr(0, Sep + 2);
  }
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
  auto &C = *constraint(N.Text);
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
