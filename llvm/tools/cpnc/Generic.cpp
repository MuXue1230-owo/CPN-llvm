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
} // namespace
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
bool Frame::predicate(const Node &N) {
  if (N.Text == "ObjectType" || N.Text == "CompleteType") {
    if (N.TemplateArgs.size() != 1)
      fail(N.At, "predicate requires one type");
    auto T = resolve(N.TemplateArgs[0].Type, N.At);
    if (T == "void" || llvm::StringRef(T).ends_with("&"))
      return false;
    return N.Text == "ObjectType" || U.ir(T, N.At)->isSized();
  }
  auto &C = U.Constraints.at(N.Text);
  auto S = bind(C, N.TemplateArgs, {}, N.At);
  auto *Fn = llvm::Function::Create(
      llvm::FunctionType::get(B.getVoidTy(), false),
      llvm::GlobalValue::InternalLinkage, "cpn.requirement", U.M);
  Frame Probe(U, nullptr, Fn, C.Prefix);
  Probe.Env = std::move(S);
  Probe.B.SetInsertPoint(Probe.block("entry"));
  bool OK = true;
  try {
    for (auto &R : C.Decl.Children) {
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
          if (llvm::StringRef(T).starts_with("const<") && T.back() == '>')
            T = T.substr(6, T.size() - 7);
          Probe.Scopes.back().Names[P.Text] = {T, nullptr,
                                               Probe.allocate(T, P.At)};
        }
        for (auto &E : R.Children)
          OK &= Probe.eval(E).Type == Probe.resolve(E.Type, E.At);
      }
      Probe.Scopes.pop_back();
    }
  } catch (const Diagnostic &) {
    OK = false;
  }
  Fn->eraseFromParent();
  return OK;
}
