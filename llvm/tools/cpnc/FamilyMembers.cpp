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
  auto Qualifier = StringRef(D.Settings.at("qualifier")).drop_back(2);
  auto [Base, Arguments] = Qualifier.split('<');
  auto Key =
      scopeKey(Prefix, Base, [&](const auto &S) { return Families.count(S); });
  if (Key.empty())
    fail(D.At, "qualified member definition requires a declared owner family");
  unsigned Depth = 1;
  size_t End = 0;
  for (; End < Arguments.size(); ++End) {
    if (Arguments[End] == '<')
      ++Depth;
    if (Arguments[End] == '>' && !--Depth)
      break;
  }
  if (End == Arguments.size())
    fail(D.At, "unterminated owner application");
  auto Args = splitArguments(Arguments.take_front(End));
  auto Suffix = Arguments.drop_front(End + 1);
  const Node *Generic = nullptr;
  auto matchOwner = [&](const Node &Decl) {
    if (Decl.Generics.size() != D.Generics.size())
      return;
    std::vector<std::string> Pattern;
    if (Decl.Settings.count("specialize")) {
      for (const auto &P : Decl.Pattern) {
        if (P.K != Node::TypeArg && P.K != Node::Name && P.K != Node::Number)
          return;
        Pattern.push_back(
            rebindTypeNames(P.K == Node::TypeArg ? P.Type : P.Text, Decl, D));
      }
    } else {
      for (const auto &G : D.Generics)
        Pattern.push_back(G.Text + (G.Pack ? "..." : ""));
    }
    if (Pattern != Args)
      return;
    if (Generic)
      fail(D.At, "ambiguous qualified owner pattern");
    Generic = &Decl;
  };
  matchOwner(Families.at(Key).Decl);
  if (auto It = Specializations.find(Key); It != Specializations.end())
    for (const auto &S : It->second)
      matchOwner(S.Decl);
  if (!Generic)
    fail(D.At,
         "owner application must identify a declared family or specialization");
  for (const auto &G : D.Generics)
    if (!G.Children.empty())
      fail(G.At, "a definition cannot redeclare a generic default");
  const Node *Class = Generic;
  while (Suffix.consume_front("::")) {
    auto Part = Suffix.split("::").first;
    auto Inner = llvm::find_if(Class->Children, [&](const Node &N) {
      return (N.K == Node::Record || N.K == Node::Union) && N.Text == Part &&
             !N.Prototype;
    });
    if (Inner == Class->Children.end() || !Inner->Generics.empty())
      fail(D.At, "unknown nested owning declaration");
    Class = &*Inner;
    Suffix = Suffix.drop_front(Part.size());
  }
  if (!Suffix.empty() || (Class->K != Node::Record && Class->K != Node::Union))
    fail(D.At, "qualified definition requires a record or union owner");
  const auto &Owner = *Class;
  const Node *Selected = nullptr;
  for (const auto &Member : Owner.Children) {
    if (Member.K != D.K || Member.Text != D.Text || !Member.Generics.empty())
      continue;
    Node Public = Member;
    Public.Generics = Generic->Generics;
    // Omitting the owner's already established constraint retains that bound.
    if (!D.TemplateArgs.empty())
      Public.TemplateArgs = Generic->Params;
    if (!sameGenericSignature(Public, D))
      continue;
    if (!sameGenericResult(Public, D) || D.Noexcept != Member.Noexcept ||
        D.Required != Member.Required ||
        D.Settings.count("mode") != Member.Settings.count("mode") ||
        D.Settings.count("lifecycle_effect") !=
            Member.Settings.count("lifecycle_effect"))
      fail(D.At, "incompatible qualified member definition");
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
  Domain.Params = Generic->Params;
  for (auto &Q : Domain.Params)
    rebindCondition(Q, *Generic, D);
  Domain.Children.clear();
  for (auto Field : Owner.Children)
    if (Field.K == Node::Field) {
      Field.Type = rebindTypeNames(Field.Type, *Generic, D);
      Domain.Children.push_back(std::move(Field));
    }
  Domain.Children.push_back(D);
  checkDomain(Domain, Families.at(Key).Prefix);
  auto &Definitions = OwnerBodies[position(Owner)];
  auto [Bound, New] = Definitions.emplace(
      position(*Selected), MemberBody{position(*Generic), D, site()});
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
  auto *Generic = &Owner.Decl;
  auto Parent = Name;
  while (position(*Generic) != Saved.GenericOwner) {
    auto P = MemberTypes.find(Parent);
    if (P == MemberTypes.end())
      fail(D.At, "missing enclosing owner instance");
    Parent = P->second.first;
    Generic = &Records.at(Parent).Decl;
  }
  if (!D.Generics.empty() && D.Generics.back().Pack) {
    Family Source{D, "", Saved.Site};
    D = expand(Source, Generic->Generics.size() - (D.Generics.size() - 1), D.At)
            .Decl;
  }
  for (size_t I = 0; I < D.Generics.size(); ++I) {
    auto &Old = Generic->Generics[I];
    auto &New = D.Generics[I].Text;
    if (Old.K == Node::TypeParam)
      Env.Types[New] = Owner.Env.Types.at(Old.Text);
    else
      Env.Values[New] = Owner.Env.Values.at(Old.Text);
  }
  D.Generics.clear();
  D.TemplateArgs.clear();
  D.Settings["qualifier"] = "::" + Name + "::";
  EnterDefinition Site(*this, Saved.Site);
  defineQualified(D, "", &Env);
}
