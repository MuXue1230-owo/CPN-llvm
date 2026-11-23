#include "Sema.h"
using namespace cpn;
using llvm::StringRef;

namespace {
SourcePosition position(const Node &D) { return {D.At.Line, D.At.Column}; }
void rebindCondition(Node &N, const Node &From, const Node &To) {
  N.Text = rebindTypeNames(N.Text, From, To);
  N.Type = rebindTypeNames(N.Type, From, To);
  for (auto &A : N.TemplateArgs)
    rebindCondition(A, From, To);
  for (auto &A : N.Children)
    rebindCondition(A, From, To);
}
std::set<size_t> effectPositions(const Node &D, StringRef Key) {
  std::set<size_t> S;
  if (auto I = D.Settings.find(Key.str()); I != D.Settings.end())
    for (const auto &Name : splitArguments(I->second)) {
      auto P = llvm::find_if(D.Params,
                             [&](const Node &P) { return P.Text == Name; });
      if (P == D.Params.end())
        fail(D.At, "unknown parameter in callable contract");
      S.insert(P - D.Params.begin());
    }
  return S;
}
} // namespace

void Context::defineFamilyMember(const Node &D, const std::string &Prefix) {
  std::string Base;
  if (StringRef(D.Settings.at("qualifier")).starts_with("::"))
    Base = "::";
  auto Applied = D.Pattern.begin();
  for (; Applied != D.Pattern.end(); ++Applied) {
    Base += Applied->Text;
    if (Applied->ExplicitApplication)
      break;
    Base += "::";
  }
  if (Applied == D.Pattern.end())
    fail(D.At, "qualified member definition requires an applied owner");
  auto Key =
      scopeKey(Prefix, Base, [&](const auto &S) { return Families.count(S); });
  if (Key.empty())
    fail(D.At, "qualified member definition requires a declared owner family");
  Node Formals;
  std::vector<SourcePosition> GenericOwners;
  auto matches = [&](const Node &Decl, const std::vector<Node> &Args) {
    size_t Begin = Formals.Generics.size(), Count = Decl.Generics.size();
    if (Begin + Count > D.Generics.size())
      return false;
    Node Binders;
    Binders.Generics.assign(D.Generics.begin() + Begin,
                            D.Generics.begin() + Begin + Count);
    std::vector<Node> Pattern;
    if (Decl.Settings.count("specialize")) {
      Pattern = Decl.Pattern;
    } else {
      for (const auto &G : Decl.Generics) {
        Node A(G.K == Node::TypeParam ? Node::TypeArg : Node::Name, G.At);
        if (G.K == Node::TypeParam)
          A.Type = G.Text;
        A.Pack = G.Pack;
        Pattern.push_back(std::move(A));
      }
    }
    return Pattern.size() == Args.size() &&
           std::equal(Pattern.begin(), Pattern.end(), Args.begin(),
                      [&](const Node &L, const Node &R) {
                        return sameGenericArgument(L, R, Decl, Binders);
                      });
  };
  auto addOwner = [&](const Node &Owner) {
    GenericOwners.push_back(position(Owner));
    Formals.Generics.insert(Formals.Generics.end(), Owner.Generics.begin(),
                            Owner.Generics.end());
    Formals.Params.insert(Formals.Params.end(), Owner.Params.begin(),
                          Owner.Params.end());
  };
  const Node *Class = nullptr;
  auto matchRoot = [&](const Node &Decl) {
    if (!matches(Decl, Applied->TemplateArgs))
      return;
    if (Class)
      fail(D.At, "ambiguous qualified owner pattern");
    Class = &Decl;
  };
  matchRoot(Families.at(Key).Decl);
  if (auto It = Specializations.find(Key); It != Specializations.end())
    for (const auto &S : It->second)
      matchRoot(S.Decl);
  if (!Class)
    fail(D.At,
         "owner application must identify a declared family or specialization");
  addOwner(*Class);
  for (++Applied; Applied != D.Pattern.end(); ++Applied) {
    auto Inner = llvm::find_if(Class->Children, [&](const Node &N) {
      return (N.K == Node::Record || N.K == Node::Union) &&
             N.Text == Applied->Text && !N.Prototype;
    });
    if (Inner == Class->Children.end())
      fail(D.At, "unknown nested owning declaration");
    Class = &*Inner;
    if (Applied->ExplicitApplication) {
      if (Class->Generics.empty() || !matches(*Class, Applied->TemplateArgs))
        fail(D.At, "invalid nested owner application");
      addOwner(*Class);
    } else if (!Class->Generics.empty())
      fail(D.At, "nested owner family requires an application");
  }
  if (Class->K != Node::Record && Class->K != Node::Union)
    fail(D.At, "qualified definition requires a record or union owner");
  if (Formals.Generics.size() != D.Generics.size())
    fail(D.At,
         "owner application must match its declaration's generic parameters");
  for (const auto &G : D.Generics)
    if (!G.Children.empty())
      fail(G.At, "a definition cannot redeclare a generic default");
  const auto &Owner = *Class;
  const Node *Selected = nullptr;
  for (const auto &Member : Owner.Children) {
    if (Member.K != D.K || Member.Text != D.Text || !Member.Generics.empty())
      continue;
    Node Public = Member;
    Public.Generics = Formals.Generics;
    // Omitting the owner's already established constraint retains that bound.
    if (!D.TemplateArgs.empty())
      Public.TemplateArgs = Formals.Params;
    if (!sameGenericSignature(Public, D))
      continue;
    if (!sameGenericResult(Public, D) || D.Noexcept != Member.Noexcept ||
        D.Required != Member.Required ||
        D.Settings.count("mode") != Member.Settings.count("mode") ||
        D.Settings.count("lifecycle_effect") !=
            Member.Settings.count("lifecycle_effect"))
      fail(D.At, "incompatible qualified member definition");
    auto HasReceiver = !Member.Settings.count("static");
    if (auto Bound = genericEffectBound(D, HasReceiver);
        Bound && Bound != genericEffectBound(Member, HasReceiver))
      fail(D.At, "incompatible qualified member effect contract");
    if (!D.Contracts.empty() && !sameGenericValueContracts(Public, D))
      fail(D.At, "incompatible qualified member value contract");
    for (StringRef Effect : {"consumes", "noescape", "returns_borrowed_from"})
      if (effectPositions(Member, Effect) != effectPositions(D, Effect))
        fail(D.At, "incompatible qualified member effect contract");
    if (Selected || !Member.Prototype || D.Prototype)
      fail(D.At, "member is ambiguous or already defined");
    Selected = &Member;
  }
  if (!Selected)
    fail(D.At,
         "qualified definition must match a previously declared family member");
  for (auto &P : D.Params)
    if (!P.Children.empty())
      fail(P.At, "defaults belong to the canonical declaration");
  validate(D, Families.at(Key).Prefix, {}, &Owner);
  Node Domain = Owner;
  Domain.K = Node::Record;
  Domain.Generics = D.Generics;
  Domain.Params = Formals.Params;
  for (auto &Q : Domain.Params)
    rebindCondition(Q, Formals, D);
  Domain.Children.clear();
  for (auto Field : Owner.Children)
    if (Field.K == Node::Field) {
      Field.Type = rebindTypeNames(Field.Type, Formals, D);
      Domain.Children.push_back(std::move(Field));
    }
  Domain.Children.push_back(D);
  checkDomain(Domain, Families.at(Key).Prefix, &Owner);
  auto &Definitions = OwnerBodies[position(Owner)];
  auto [Bound, New] = Definitions.emplace(position(*Selected),
                                          MemberBody{GenericOwners, D, site()});
  if (!New)
    fail(D.At, "family member is already defined");
  std::vector<std::string> Existing;
  for (const auto &[Name, Rec] : Records)
    if (position(Rec.Decl) == position(Owner))
      Existing.push_back(Name);
  for (const auto &Name : Existing)
    bindFamilyMember(Name, Bound->second);
}

void Context::bindFamilyMember(const std::string &Name,
                               const MemberBody &Saved) {
  const auto &Owner = Records.at(Name);
  Node D = Saved.Definition;
  auto Env = Owner.Env;
  std::vector<const Record *> Instances;
  const Record *Current = &Owner;
  for (auto Site : llvm::reverse(Saved.GenericOwners)) {
    while (Current && position(Current->Decl) != Site) {
      auto P = Records.find(Current->EnclosingScope);
      Current = P == Records.end() ? nullptr : &P->second;
    }
    if (!Current)
      fail(D.At, "missing enclosing owner instance");
    Instances.push_back(Current);
  }
  size_t Count = 0;
  for (auto *R : Instances)
    Count += R->Decl.Generics.size();
  if (!D.Generics.empty() && D.Generics.back().Pack) {
    Family Source{D, "", Saved.Site, Env};
    auto Expanded = expand(Source, Count - (D.Generics.size() - 1), D.At);
    D = std::move(Expanded.Decl);
    Env.PackLengths = std::move(Expanded.Enclosing.PackLengths);
  }
  if (D.Generics.size() != Count)
    fail(D.At, "owner binder arity mismatch");
  size_t I = 0;
  for (auto *R : llvm::reverse(Instances))
    for (const auto &Old : R->Decl.Generics) {
      const auto &New = D.Generics[I++].Text;
      if (Old.K == Node::TypeParam)
        Env.Types[New] = R->Env.Types.at(Old.Text);
      else
        Env.Values[New] = R->Env.Values.at(Old.Text);
    }
  D.Generics.clear();
  D.TemplateArgs.clear();
  // The selected member declaration owns its value predicates. Any repeated
  // clauses have already been compared in the correct binder environments.
  D.Contracts.clear();
  D.Settings["qualifier"] = "::" + Name + "::";
  EnterDefinition Site(*this, Saved.Site);
  defineQualified(D, "", &Env);
}
