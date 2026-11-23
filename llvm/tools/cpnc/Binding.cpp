#include "Sema.h"
using namespace cpn;
namespace {
struct NominalType {
  const Node *Declaration = nullptr;
  std::string Key;
  unsigned Pointers = 0;
  bool Dependent = false;
};
struct Binding {
  enum Kind {
    Object,
    Alias,
    Nominal,
    TypeParameter,
    ValueParameter
  } K = Object;
  NominalType Type;
};
using Scope = std::map<std::string, Binding>;
using Path = std::vector<const Node *>;

bool callable(const Node &N) {
  return N.K == Node::Function || N.K == Node::Constructor ||
         N.K == Node::Destructor;
}

bool nominalRecord(const Node &N) {
  return N.K == Node::Record || N.K == Node::Union;
}

struct Check {
  Context &U;
  std::string Prefix, Owner;
  Scope Names;
  const Node *SyntaxOwner = nullptr;

  bool known(const std::string &S) const {
    static const std::set<std::string> Intrinsics = {"std::move",
                                                     "std::forward",
                                                     "std::ensure",
                                                     "std::debug_assert",
                                                     "std::discard",
                                                     "std::to_underlying",
                                                     "std::from_underlying",
                                                     "std::try_from_underlying",
                                                     "construct_at",
                                                     "storage_of",
                                                     "destroy",
                                                     "destroy_base",
                                                     "transfer_storage",
                                                     "transfer_destruction",
                                                     "abandon",
                                                     "abandon_base",
                                                     "this",
                                                     "nullptr",
                                                     "true",
                                                     "false"};
    auto Intrinsic = llvm::StringRef(S);
    if (Intrinsic.starts_with("::std::"))
      Intrinsic = Intrinsic.drop_front(2);
    if (Names.count(S) || Intrinsics.count(Intrinsic.str()) ||
        integerLibraryName(S) || floatingSpecialName(S) || builtin(S) ||
        builtinPredicate(S) || U.Aliases.count(S) || U.Cases.count(S))
      return true;
    if (auto Enclosing =
            U.Records.find(llvm::StringRef(Prefix).rtrim(':').str());
        Enclosing != U.Records.end() &&
        Enclosing->second.Env.PackLengths.count(S))
      return true;
    if (!Owner.empty() && U.Records.count(Owner)) {
      const auto &R = U.Records.at(Owner);
      Token T{S};
      if (S == R.Decl.Text || R.Env.Types.count(S) || R.Env.Values.count(S) ||
          R.Env.PackLengths.count(S) || U.lookupPath(Owner, T, true) ||
          U.lookupPath(Owner, T, false) ||
          llvm::any_of(R.Decl.Children,
                       [&](const Node &D) { return D.Text == S; }))
        return true;
    }
    if (SyntaxOwner) {
      if (S == SyntaxOwner->Text ||
          llvm::any_of(SyntaxOwner->Children,
                       [&](const Node &D) { return D.Text == S; }))
        return true;
      for (const auto &Base : SyntaxOwner->TemplateArgs) {
        auto T = nominalType(Base.Type);
        if (T.Dependent ||
            (!T.Declaration && llvm::StringRef(Base.Type).contains("<")))
          return true;
        if (!T.Key.empty() && (U.lookupPath(T.Key, Token{S}, false) ||
                               U.lookupPath(T.Key, Token{S}, true)))
          return true;
      }
    }
    auto [Head, Qualified] = llvm::StringRef(S).split("::");
    if (auto I = Names.find(Head.str());
        !Qualified.empty() && I != Names.end()) {
      const auto &Symbol = I->second;
      if (Symbol.K == Binding::TypeParameter ||
          (Symbol.K == Binding::Alias && Symbol.Type.Dependent))
        return true;
      if (Symbol.K == Binding::Alias || Symbol.K == Binding::Nominal) {
        auto *Decl = Symbol.Type.Declaration;
        auto Remaining = Qualified;
        while (Decl && !Remaining.empty()) {
          auto Member = Remaining.split("::");
          auto Found = llvm::find_if(Decl->Children, [&](const Node &D) {
            return D.Text == Member.first;
          });
          if (Found == Decl->Children.end())
            break;
          Decl = &*Found;
          Remaining = Member.second;
        }
        if (Remaining.empty())
          return true;
      }
    }
    auto [Family, Arguments] = llvm::StringRef(S).split('<');
    if (!Arguments.empty() &&
        !scopeKey(Prefix, Family, [&](const std::string &Key) {
           return U.Families.count(Key);
         }).empty())
      return true;
    return !scopeKey(Prefix, S, [&](const std::string &Key) {
              return U.Globals.count(Key) || U.Overloads.count(Key) ||
                     U.Families.count(Key) || U.Constraints.count(Key) ||
                     U.Records.count(Key) || U.Enums.count(Key) ||
                     U.Aliases.count(Key) || U.Cases.count(Key);
            }).empty();
  }

  NominalType nominalType(std::string T) const {
    unsigned Pointers = 0;
    for (unsigned Depth = 0; Depth < 64 && !T.empty(); ++Depth) {
      T = unconst(T);
      if (llvm::StringRef(T).ends_with("*")) {
        ++Pointers;
        T.pop_back();
        continue;
      }
      if (llvm::StringRef(T).ends_with("&")) {
        T.pop_back();
        continue;
      }
      if (auto Local = Names.find(T); Local != Names.end()) {
        if (Local->second.K == Binding::TypeParameter)
          return {nullptr, {}, Pointers, true};
        if (Local->second.K == Binding::Alias ||
            Local->second.K == Binding::Nominal) {
          auto Type = Local->second.Type;
          Type.Pointers += Pointers;
          return Type;
        }
        return {};
      }
      auto Key = scopeKey(Prefix, T, [&](const std::string &Name) {
        return U.Records.count(Name) || U.Aliases.count(Name);
      });
      if (auto Alias = U.Aliases.find(Key); Alias != U.Aliases.end()) {
        T = Alias->second;
        continue;
      }
      if (!Key.empty())
        return {&U.Records.at(Key).Decl, Key, Pointers};
      return {};
    }
    return {};
  }

  NominalType expressionType(const Node &N) const {
    if (N.K == Node::Unary && (N.Text == "*" || N.Text == "&")) {
      auto T = expressionType(N.Children.front());
      if (N.Text == "&")
        ++T.Pointers;
      else if (T.Pointers)
        --T.Pointers;
      else
        return {};
      return T;
    }
    if (N.K != Node::Name)
      return {};
    if (auto I = Names.find(N.Text); I != Names.end())
      return I->second.Type;
    if (N.Text == "this") {
      if (!Owner.empty())
        return nominalType(Owner + "*");
      if (SyntaxOwner)
        return {SyntaxOwner, {}, 1};
    }
    if (SyntaxOwner)
      for (const auto &Field : SyntaxOwner->Children)
        if (Field.K == Node::Field && Field.Text == N.Text)
          return nominalType(Field.Type);
    auto Key = scopeKey(Prefix, N.Text, [&](const std::string &K) {
      return U.Globals.count(K);
    });
    return Key.empty() ? NominalType{} : nominalType(U.Globals.at(Key).Type);
  }

  void bindMember(const Node &N) const {
    const auto T = expressionType(N.Children.front());
    if (!T.Declaration || !nominalRecord(*T.Declaration) ||
        T.Pointers != unsigned(N.Definition))
      return;
    if (llvm::any_of(T.Declaration->Children,
                     [&](const Node &D) { return D.Text == N.Text; }))
      return;
    // An unapplied record may acquire members through a dependent base.
    if (T.Key.empty() && !T.Declaration->TemplateArgs.empty())
      return;
    if (!T.Key.empty() &&
        (U.lookupPath(T.Key, N.At, false) || U.lookupPath(T.Key, N.At, true)))
      return;
    fail(N.At, "unknown member '" + N.Text + "'");
  }

  void generic(const Node &G) {
    for (const auto &Default : G.Children)
      visit(Default, true);
    Names[G.Text] = {G.K == Node::TypeParam ? Binding::TypeParameter
                                            : Binding::ValueParameter,
                     nominalType(G.Type)};
  }

  void parameters(const std::vector<Node> &Params) {
    for (const auto &P : Params) {
      for (const auto &Default : P.Children)
        visit(Default, true);
      if (!P.Text.empty())
        Names[P.Text] = {Binding::Object, nominalType(P.Type)};
    }
  }

  void members(const Node &N) {
    llvm::SaveAndRestore RecordScope(SyntaxOwner, &N);
    for (const auto &Member : N.Children) {
      llvm::SaveAndRestore MemberScope(Names);
      if (nominalRecord(Member)) {
        visit(Member, true);
        continue;
      }
      for (const auto &G : Member.Generics)
        generic(G);
      if (callable(Member))
        parameters(Member.Params);
      for (const auto &Condition : Member.TemplateArgs)
        visit(Condition, true);
      for (const auto &C : Member.Children)
        visit(C, true);
    }
  }

  void visit(const Node &N, bool Bind) {
    const auto &A = N.Children;
    Bind |= N.K == Node::If && N.Required;
    if (N.K == Node::Lambda) {
      llvm::SaveAndRestore Outer(Names);
      Scope Captured;
      for (const auto &[Name, Symbol] : Names)
        if (Symbol.K != Binding::Object)
          Captured.emplace(Name, Symbol);
      for (const auto &C : N.TemplateArgs) {
        NominalType Type;
        if (C.Type == "initializer") {
          visit(C.Children[0], Bind);
          Type = expressionType(C.Children[0]);
        } else if (auto I = Names.find(C.Text); I != Names.end()) {
          Type = I->second.Type;
        } else {
          if (Bind && !known(C.Text))
            fail(C.At, "unknown capture '" + C.Text + "'");
          Type = expressionType(Node(Node::Name, C.At));
        }
        Captured[C.Text] = {Binding::Object, std::move(Type)};
      }
      Names = std::move(Captured);
      llvm::SaveAndRestore OwnerScope(Owner, std::string{});
      llvm::SaveAndRestore SyntaxScope(SyntaxOwner,
                                       static_cast<const Node *>(nullptr));
      parameters(N.Params);
      for (const auto &C : A)
        visit(C, Bind);
      return;
    }
    if (Bind && N.K == Node::Name && !known(N.Text))
      fail(N.At, "unknown name '" + N.Text + "'");
    if (Bind && N.K == Node::Member)
      bindMember(N);
    if (nominalRecord(N) || N.K == Node::Enumeration) {
      Names[N.Text] = {Binding::Nominal, {&N}};
      if (Bind && nominalRecord(N)) {
        llvm::SaveAndRestore TypeScope(Names);
        for (const auto &G : N.Generics)
          generic(G);
        members(N);
      }
      return;
    }
    if (N.K == Node::Alias)
      Names[N.Text] = {Binding::Alias, nominalType(N.Type)};
    if (N.K == Node::Object)
      Names[N.Text] = {Binding::Object, nominalType(N.Type)};
    if (N.K == Node::Block || N.K == Node::Tail || N.K == Node::For ||
        N.K == Node::Arm || N.K == Node::Requirement) {
      llvm::SaveAndRestore BlockScope(Names);
      parameters(N.Params);
      for (const auto &C : A)
        visit(C, Bind);
      return;
    }
    for (const auto &C : N.TemplateArgs)
      visit(C, Bind);
    for (auto [I, C] : llvm::enumerate(A))
      if ((I != 2 || (!bitExtensionArgument(N) && !castRoundingArgument(N))) &&
          !floatingSpecialSignArgument(N, I))
        visit(C, Bind);
  }
};
} // namespace
JumpCleanups Context::validate(const Node &N, const std::string &P,
                               const std::string &Owner,
                               const Node *FamilyOwner,
                               const Substitution *Captured) {
  Check Ch{*this, P, Owner, {}, FamilyOwner};
  if (Captured) {
    for (const auto &[Name, Type] : Captured->Types)
      Ch.Names[Name] = {Binding::Alias, Ch.nominalType(Type)};
    for (const auto &[Name, Value] : Captured->Values)
      Ch.Names[Name] = {Binding::ValueParameter, Ch.nominalType(Value.Type)};
  }
  Ch.Names[N.Text] =
      nominalRecord(N) ? Binding{Binding::Nominal, {&N}} : Binding{};
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
    Ch.generic(G);
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
  }
  if (!nominalRecord(N))
    Ch.parameters(N.Params);
  if (!N.Generics.empty())
    for (const auto &Condition : nominalRecord(N) ? N.Params : N.TemplateArgs)
      Ch.visit(Condition, true);
  bool Specialization = N.Settings.count("specialize");
  if (Specialization)
    for (const auto &Pattern : N.Pattern)
      Ch.visit(Pattern, true);
  // Definition-time binding does not depend on whether a callable,
  // discarded branch, or record specialization emits a runtime body.
  if (nominalRecord(N) && (Specialization || !N.Generics.empty()))
    Ch.members(N);
  else if (callable(N) || N.K == Node::Constraint)
    for (const auto &C : N.Children)
      Ch.visit(C, !N.Generics.empty());
  std::map<std::string, Path> Labels;
  std::vector<std::pair<const Node *, Path>> Jumps;
  std::function<void(const Node &, Path &, bool)> walk =
      [&](const Node &S, Path &Live, bool MatchArm) {
        if (S.K == Node::Lambda || S.K == Node::Record || S.K == Node::Union ||
            S.K == Node::Enumeration)
          return;
        if (S.K == Node::Object)
          Live.push_back(&S);
        if (S.K == Node::Label && !Labels.emplace(S.Text, Live).second)
          fail(S.At, "duplicate statement label");
        if (S.K == Node::Goto)
          Jumps.emplace_back(&S, Live);
        if (S.K == Node::Block || S.K == Node::For || S.K == Node::Match ||
            S.K == Node::Arm || S.K == Node::Tail) {
          auto Nested = Live;
          if (MatchArm || S.K == Node::Tail)
            Nested.push_back(&S);
          for (auto &C : S.Children)
            walk(C, Nested, S.K == Node::Match && C.K == Node::Arm);
          return;
        }
        for (auto &C : S.Children)
          walk(C, Live, false);
      };
  const bool HasCleanup = N.K == Node::Destructor && N.Children.size() > 1;
  for (auto &C : N.Children) {
    Path Phase;
    // Body and Cleanup have distinct entries separated by the required
    // automatic subobject retirement.
    if (HasCleanup)
      Phase.push_back(&C);
    walk(C, Phase, false);
  }
  JumpCleanups Result;
  for (auto &[Jump, From] : Jumps) {
    auto It = Labels.find(Jump->Text);
    if (It == Labels.end())
      fail(Jump->At, "unknown statement label");
    auto &To = It->second;
    if (HasCleanup && From.front() != To.front())
      fail(Jump->At, "goto crosses a destructor phase boundary");
    if (To.size() > From.size() ||
        !std::equal(To.begin(), To.end(), From.begin()))
      fail(Jump->At, "goto enters an unexecuted initializer");
    Result.Targets.insert(Jump->Text);
    auto &Ended = Result.Exited[{Jump->At.Line, Jump->At.Column}];
    for (const auto *Object : llvm::ArrayRef(From).drop_front(To.size()))
      Ended.emplace(Object->At.Line, Object->At.Column);
  }
  return Result;
}
