#include "Sema.h"
using namespace cpn;
namespace {
using Scope = std::set<std::string>;
using Path = std::vector<const Node *>;
struct Check {
  Context &U;
  std::string Prefix, Owner;
  Scope Names;
  bool Dependent = false;
  std::map<std::string, Path> Labels;
  std::vector<std::pair<const Node *, Path>> Jumps;
  bool known(const std::string &S) const {
    static const Scope Intrinsics = {"std::move",
                                     "std::forward",
                                     "construct_at",
                                     "storage_of",
                                     "destroy",
                                     "destroy_base",
                                     "transfer_destruction",
                                     "abandon",
                                     "abandon_base",
                                     "this",
                                     "nullptr",
                                     "true",
                                     "false",
                                     "SameType",
                                     "ObjectType",
                                     "CompleteType"};
    if (Names.count(S) || Intrinsics.count(S) || builtin(S) ||
        builtinPredicate(S) || U.Aliases.count(S) || U.Cases.count(S))
      return true;
    if (!Owner.empty() && U.Records.count(Owner)) {
      const auto &R = U.Records.at(Owner);
      Token T{S};
      if (S == R.Decl.Text || R.Env.Types.count(S) || R.Env.Values.count(S) ||
          U.lookupPath(Owner, T, true) || U.lookupPath(Owner, T, false) ||
          llvm::any_of(R.Decl.Children,
                       [&](const Node &D) { return D.Text == S; }))
        return true;
    }
    if (Dependent && llvm::StringRef(S).contains("::") &&
        Names.count(llvm::StringRef(S).split("::").first.str()))
      return true;
    return !scopeKey(Prefix, S, [&](const std::string &Key) {
              return U.Globals.count(Key) || U.Overloads.count(Key) ||
                     U.Families.count(Key) || U.Constraints.count(Key) ||
                     U.Records.count(Key) || U.Enums.count(Key) ||
                     U.Aliases.count(Key) || U.Cases.count(Key);
            }).empty();
  }
  void visit(const Node &N, Path &Active) {
    auto &A = N.Children;
    if (N.K == Node::Requirement) {
      auto Saved = Names;
      for (auto &P : N.Params)
        Names.insert(P.Text);
      for (auto &C : N.Children)
        visit(C, Active);
      Names = std::move(Saved);
      return;
    }
    if (N.K == Node::Lambda) {
      auto Outer = Names;
      Scope Captured;
      for (auto &C : N.TemplateArgs) {
        if (C.Type == "initializer")
          visit(C.Children[0], Active);
        else if (!known(C.Text))
          fail(C.At, "unknown capture '" + C.Text + "'");
        Captured.insert(C.Text);
      }
      Names = std::move(Captured);
      for (auto &P : N.Params)
        Names.insert(P.Text);
      Path Nested;
      for (auto &C : N.Children)
        visit(C, Nested);
      Names = std::move(Outer);
      return;
    }
    if (N.K == Node::Name && !known(N.Text))
      fail(N.At, "unknown name '" + N.Text + "'");
    if (N.K == Node::Record || N.K == Node::Enumeration || N.K == Node::Union) {
      Names.insert(N.Text);
      return;
    }
    if (N.K == Node::Alias)
      Names.insert(N.Text);
    if (N.K == Node::Object) {
      Names.insert(N.Text);
      Active.push_back(&N);
    }
    if (N.K == Node::Goto)
      Jumps.emplace_back(&N, Active);
    if (N.K == Node::Label && !Labels.emplace(N.Text, Active).second)
      fail(N.At, "duplicate statement label");
    if (N.K == Node::Block || N.K == Node::Tail || N.K == Node::For) {
      auto Saved = Names;
      auto Previous = Active;
      for (auto &C : A)
        visit(C, Active);
      Names = std::move(Saved);
      Active = std::move(Previous);
      return;
    }
    if (N.K == Node::Arm) {
      auto Saved = Names;
      for (auto &P : N.Params)
        Names.insert(P.Text);
      for (auto &C : A)
        visit(C, Active);
      Names = std::move(Saved);
      return;
    }
    for (auto &C : N.TemplateArgs)
      visit(C, Active);
    for (auto &C : A)
      visit(C, Active);
  }
};
} // namespace
JumpCleanups Context::validate(const Node &N, const std::string &P,
                               const std::string &Owner) {
  Check Ch{*this, P, Owner, {}, {}, {}, {}};
  Path Scope;
  Ch.Names.insert(N.Text);
  if (!N.Generics.empty() && N.Generics.back().Pack) {
    std::set<std::string> Packs{N.Generics.back().Text};
    for (auto &P : N.Params)
      if (P.Pack)
        Packs.insert(P.Text);
    std::function<void(const Node &, bool)> check = [&](const Node &V,
                                                        bool Expanded) {
      Expanded |= V.Pack;
      if (V.K == Node::Name && Packs.count(V.Text) && !Expanded)
        fail(V.At, "unexpanded pack in expression");
      for (auto &C : V.Children)
        check(C, Expanded);
      for (auto &C : V.TemplateArgs)
        check(C, Expanded);
    };
    for (auto &C : N.Children)
      check(C, false);
  }
  for (auto &G : N.Generics) {
    if (G.K == Node::ValueParam && !Ch.Names.count(G.Type)) {
      Frame Resolver(*this, nullptr, nullptr, P);
      auto T = Resolver.resolve(G.Type, G.At);
      if (!integer(T) && T != "bool" && T != "char" && !Enums.count(T))
        fail(G.At, "invalid generic constant parameter type");
    }
    for (auto &D : G.Children)
      Ch.visit(D, Scope);
    Ch.Names.insert(G.Text);
  }
  for (auto &Arg : N.Params) {
    bool HasPack = !N.Generics.empty() && N.Generics.back().Pack;
    if (Arg.Pack && !HasPack)
      fail(Arg.At, "parameter expansion requires a generic pack");
    if (llvm::StringRef(Arg.Type).starts_with("forward ") &&
        llvm::none_of(N.Generics, [&](auto &G) {
          return G.K == Node::TypeParam && G.Text == Arg.Type.substr(8);
        }))
      fail(Arg.At, "forward requires a type parameter");
    for (auto &D : Arg.Children)
      Ch.visit(D, Scope);
    if (!Arg.Text.empty())
      Ch.Names.insert(Arg.Text);
  }
  // Ordinary expressions bind as they are emitted. Check discarded arms and
  // dependent definitions here since neither necessarily has a runtime entry.
  std::function<void(const Node &)> collect = [&](const Node &S) {
    if (S.K == Node::Record || S.K == Node::Enumeration || S.K == Node::Union) {
      Ch.Names.insert(S.Text);
      return;
    }
    if (S.K == Node::Object || S.K == Node::Alias)
      Ch.Names.insert(S.Text);
    if (S.K == Node::If && S.Required) {
      Ch.visit(S, Scope);
      return;
    }
    if (S.K == Node::Block) {
      auto Saved = Ch.Names;
      for (auto &C : S.Children)
        collect(C);
      Ch.Names = std::move(Saved);
      return;
    }
    for (auto &C : S.Children)
      collect(C);
  };
  if ((N.K == Node::Function || N.K == Node::Constraint) &&
      !N.Generics.empty()) {
    for (auto &C : N.Children)
      Ch.visit(C, Scope);
  } else if (N.K == Node::Function) {
    for (auto &C : N.Children)
      collect(C);
  }
  Check Flow{*this, P, Owner, {}, {}, {}, {}};
  std::function<void(const Node &, Path &)> walk = [&](const Node &S,
                                                       Path &Live) {
    if (S.K == Node::Lambda)
      return;
    if (S.K == Node::Object)
      Live.push_back(&S);
    if (S.K == Node::Label && !Flow.Labels.emplace(S.Text, Live).second)
      fail(S.At, "duplicate statement label");
    if (S.K == Node::Goto)
      Flow.Jumps.emplace_back(&S, Live);
    if (S.K == Node::Block || S.K == Node::For || S.K == Node::Match ||
        S.K == Node::Arm) {
      auto Nested = Live;
      if (S.K == Node::Match || S.K == Node::Arm)
        Nested.push_back(&S);
      for (auto &C : S.Children)
        walk(C, Nested);
      return;
    }
    for (auto &C : S.Children)
      walk(C, Live);
  };
  for (auto &C : N.Children)
    walk(C, Scope);
  JumpCleanups Exited;
  for (auto &[Jump, From] : Flow.Jumps) {
    auto It = Flow.Labels.find(Jump->Text);
    if (It == Flow.Labels.end())
      fail(Jump->At, "unknown statement label");
    auto &To = It->second;
    if (To.size() > From.size() ||
        !std::equal(To.begin(), To.end(), From.begin()))
      fail(Jump->At, "goto enters an unexecuted initializer");
    auto &Ended = Exited[{Jump->At.Line, Jump->At.Column}];
    for (const auto *Object : llvm::ArrayRef(From).drop_front(To.size()))
      Ended.emplace(Object->At.Line, Object->At.Column);
  }
  return Exited;
}
