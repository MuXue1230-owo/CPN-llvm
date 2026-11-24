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
  Node Formals, BoundOwners;
  std::vector<size_t> Renaming;
  std::vector<Node> OwnerConditions;
  std::vector<MemberBody::OwnerBinding> GenericOwners;
  auto matches = [&](const Node &Decl, const std::vector<Node> &Args) {
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
    auto All = Formals.Generics;
    All.insert(All.end(), Decl.Generics.begin(), Decl.Generics.end());
    return matchOwnerBinders(Pattern, Args, All, D.Generics, Renaming);
  };
  auto addOwner = [&](const Node &Owner, std::vector<size_t> Parameters) {
    MemberBody::OwnerBinding Binding{position(Owner), {}};
    for (size_t I = Renaming.size(); I < Parameters.size(); ++I)
      Binding.Parameters.push_back(D.Generics[Parameters[I]]);
    Renaming = std::move(Parameters);
    Formals.Generics.insert(Formals.Generics.end(), Owner.Generics.begin(),
                            Owner.Generics.end());
    BoundOwners.Generics.insert(BoundOwners.Generics.end(),
                                Binding.Parameters.begin(),
                                Binding.Parameters.end());
    Formals.Params.insert(Formals.Params.end(), Owner.Params.begin(),
                          Owner.Params.end());
    for (auto Requirement : Owner.Params) {
      rebindCondition(Requirement, Formals, BoundOwners);
      OwnerConditions.push_back(std::move(Requirement));
    }
    GenericOwners.push_back(std::move(Binding));
  };
  const Node *Class = nullptr;
  std::vector<size_t> RootParameters;
  auto matchRoot = [&](const Node &Decl) {
    auto Parameters = matches(Decl, Applied->TemplateArgs);
    if (!Parameters)
      return;
    if (Class)
      fail(D.At, "ambiguous qualified owner pattern");
    Class = &Decl;
    RootParameters = std::move(*Parameters);
  };
  matchRoot(Families.at(Key).Decl);
  if (auto It = Specializations.find(Key); It != Specializations.end())
    for (const auto &S : It->second)
      matchRoot(S.Decl);
  if (!Class)
    fail(D.At,
         "owner application must identify a declared family or specialization");
  addOwner(*Class, std::move(RootParameters));
  for (++Applied; Applied != D.Pattern.end(); ++Applied) {
    auto Inner = llvm::find_if(Class->Children, [&](const Node &N) {
      return (N.K == Node::Record || N.K == Node::Union) &&
             N.Text == Applied->Text && !N.Prototype;
    });
    if (Inner == Class->Children.end())
      fail(D.At, "unknown nested owning declaration");
    Class = &*Inner;
    if (Applied->ExplicitApplication) {
      auto Parameters = matches(*Class, Applied->TemplateArgs);
      if (Class->Generics.empty() || !Parameters)
        fail(D.At, "invalid nested owner application");
      addOwner(*Class, std::move(*Parameters));
    } else if (!Class->Generics.empty())
      fail(D.At, "nested owner family requires an application");
  }
  if (Class->K != Node::Record && Class->K != Node::Union)
    fail(D.At, "qualified definition requires a record or union owner");
  for (const auto &G : D.Generics)
    if (!G.Children.empty())
      fail(G.At, "a definition cannot redeclare a generic default");
  auto Body = D;
  Body.Generics.clear();
  for (size_t I = 0; I < D.Generics.size(); ++I)
    if (!llvm::is_contained(Renaming, I))
      Body.Generics.push_back(D.Generics[I]);
  auto Signature = D;
  Signature.Generics = BoundOwners.Generics;
  Signature.Generics.insert(Signature.Generics.end(), Body.Generics.begin(),
                            Body.Generics.end());
  const auto &Owner = *Class;
  const Node *Selected = nullptr;
  Node Public;
  for (const auto &Member : Owner.Children) {
    if (Member.K != D.K || Member.Text != D.Text)
      continue;
    Node Candidate = Member;
    Candidate.Generics.insert(Candidate.Generics.begin(),
                              Formals.Generics.begin(), Formals.Generics.end());
    if (D.TemplateArgs.empty())
      Candidate.TemplateArgs.clear();
    if (!sameGenericSignature(Candidate, Signature)) {
      Candidate.TemplateArgs.insert(Candidate.TemplateArgs.begin(),
                                    Formals.Params.begin(),
                                    Formals.Params.end());
      if (!sameGenericSignature(Candidate, Signature))
        continue;
    }
    if (!sameGenericResult(Candidate, Signature) ||
        D.Noexcept != Member.Noexcept || D.Required != Member.Required ||
        D.Settings.count("mode") != Member.Settings.count("mode") ||
        D.Settings.count("lifecycle_effect") !=
            Member.Settings.count("lifecycle_effect"))
      fail(D.At, "incompatible qualified member definition");
    auto HasReceiver = !Member.Settings.count("static");
    if (auto Bound = genericEffectBound(D, HasReceiver);
        Bound && Bound != genericEffectBound(Member, HasReceiver))
      fail(D.At, "incompatible qualified member effect contract");
    if (!D.Contracts.empty() &&
        !sameGenericValueContracts(Candidate, Signature))
      fail(D.At, "incompatible qualified member value contract");
    for (StringRef Effect : {"consumes", "noescape", "returns_borrowed_from"})
      if ((Member.Generics.empty() || D.Settings.count(Effect.str())) &&
          effectPositions(Member, Effect) != effectPositions(D, Effect))
        fail(D.At, "incompatible qualified member effect contract");
    for (auto Effect : {"requires_initialized", "initializes"})
      if (auto Contract = D.Settings.find(Effect);
          Contract != D.Settings.end() &&
          (Member.Settings.count(Effect) == 0 ||
           Member.Settings.at(Effect) != Contract->second))
        fail(D.At, "incompatible qualified member construction contract");
    if (Selected || !Member.Prototype || D.Prototype)
      fail(D.At, "member is ambiguous or already defined");
    Selected = &Member;
    Public = std::move(Candidate);
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
  Domain.Params = std::move(OwnerConditions);
  for (auto Requirement : Selected->TemplateArgs) {
    rebindCondition(Requirement, Public, Signature);
    Domain.Params.push_back(std::move(Requirement));
  }
  Domain.Children.clear();
  for (auto Field : Owner.Children)
    if (Field.K == Node::Field) {
      Field.Type = rebindTypeNames(Field.Type, Formals, BoundOwners);
      Domain.Children.push_back(std::move(Field));
    }
  Domain.Children.push_back(D);
  if (Selected->Settings.count("static"))
    Domain.Children.back().Settings["static"] = "1";
  checkDomain(Domain, Families.at(Key).Prefix, &Owner);
  Body.Pattern.clear();
  Body.TemplateArgs.clear();
  // The selected declaration owns the public value predicates.
  Body.Contracts.clear();
  auto &Definitions = OwnerBodies[position(Owner)];
  auto [Bound, New] = Definitions.emplace(position(*Selected),
                                          MemberBody{std::move(GenericOwners),
                                                     position(*Selected),
                                                     std::move(Body), site()});
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
  std::vector<const Record *> Instances;
  const Record *Current = &Owner;
  for (const auto &Binding : llvm::reverse(Saved.GenericOwners)) {
    while (Current && position(Current->Decl) != Binding.Position) {
      auto P = Records.find(Current->EnclosingScope);
      Current = P == Records.end() ? nullptr : &P->second;
    }
    if (!Current)
      fail(D.At, "missing enclosing owner instance");
    Instances.push_back(Current);
  }
  Substitution Bindings;
  for (auto [R, Binding] :
       llvm::zip_equal(llvm::reverse(Instances), Saved.GenericOwners)) {
    const bool Packed =
        !Binding.Parameters.empty() && Binding.Parameters.back().Pack;
    const size_t Fixed = Binding.Parameters.size() - Packed;
    if (R->Decl.Generics.size() < Fixed ||
        (!Packed && R->Decl.Generics.size() != Fixed))
      fail(D.At, "owner binder arity mismatch");
    for (auto [I, Old] : llvm::enumerate(R->Decl.Generics)) {
      const auto New = I < Fixed ? Binding.Parameters[I].Text
                                 : Binding.Parameters.back().Text + "$" +
                                       std::to_string(I - Fixed);
      if (Old.K == Node::TypeParam)
        Bindings.Types[New] = R->Env.Types.at(Old.Text);
      else
        Bindings.Values[New] = R->Env.Values.at(Old.Text);
    }
    if (Packed) {
      // The sole source pack belongs to this owner. Expand its occurrences
      // now that the owner is concrete, then retain the member's own binders.
      auto MemberArity = D.Generics.size();
      D.Generics.push_back(Binding.Parameters.back());
      Family Source{std::move(D), "", Saved.Site, std::move(Bindings)};
      auto Expanded = expand(*this, Source, R->Decl.Generics.size() - Fixed,
                             Saved.Definition.At);
      D = std::move(Expanded.Decl);
      D.Generics.resize(MemberArity);
      Bindings = std::move(Expanded.Enclosing);
    }
  }
  if (!D.Generics.empty()) {
    auto &Group = FunctionFamilies.at(Name + "::" + D.Text);
    auto Selected = llvm::find_if(Group, [&](const Family &F) {
      return position(F.Decl) == Saved.Member;
    });
    if (Selected == Group.end() || Selected->Body)
      fail(D.At, "member is ambiguous or already defined");
    setGenericBody(*Selected, std::move(D), Saved.Site, std::move(Bindings));
    return;
  }
  auto Env = Owner.Env;
  for (const auto &[Parameter, T] : Bindings.Types)
    Env.Types[Parameter] = T;
  for (const auto &[Parameter, V] : Bindings.Values)
    Env.Values[Parameter] = V;
  for (const auto &[Parameter, Count] : Bindings.PackLengths)
    Env.PackLengths[Parameter] = Count;
  D.Settings["qualifier"] = "::" + Name + "::";
  EnterDefinition Site(*this, Saved.Site);
  defineQualified(D, "", &Env);
}
