#include "ConstraintLogic.h"
#include "Frontend.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SaveAndRestore.h"
#include <algorithm>
#include <iterator>
#include <memory>
#include <tuple>

using namespace cpn;
using llvm::StringRef;
namespace {
// Chapter 15 reserves alphabetic terminals except its contextual words.
const std::set<std::string> Reserved = {"alias",
                                        "alignof",
                                        "associated",
                                        "async",
                                        "auto",
                                        "await",
                                        "break",
                                        "case",
                                        "catch",
                                        "class",
                                        "cleanup",
                                        "configuration",
                                        "configured",
                                        "const",
                                        "consteval",
                                        "constexpr",
                                        "constraint",
                                        "continue",
                                        "declaration",
                                        "declare",
                                        "decltype",
                                        "default",
                                        "define",
                                        "delegate",
                                        "delete",
                                        "derive",
                                        "derive_access",
                                        "destruction_owner",
                                        "do",
                                        "else",
                                        "emit",
                                        "enum",
                                        "export",
                                        "extern",
                                        "fallthrough",
                                        "false",
                                        "for",
                                        "forward",
                                        "function",
                                        "generate",
                                        "generic",
                                        "goto",
                                        "if",
                                        "import",
                                        "init",
                                        "match",
                                        "meta_grant",
                                        "module",
                                        "mutable",
                                        "namespace",
                                        "noexcept",
                                        "nullptr",
                                        "operator",
                                        "partial_typefn",
                                        "private",
                                        "protected",
                                        "public",
                                        "quote",
                                        "reflect_decl",
                                        "reflect_expr",
                                        "reflect_type",
                                        "requires",
                                        "return",
                                        "satisfy",
                                        "sizeof",
                                        "specialize",
                                        "splice_expr",
                                        "splice_name",
                                        "splice_type",
                                        "static",
                                        "struct",
                                        "switch",
                                        "this",
                                        "thread_local",
                                        "throw",
                                        "true",
                                        "try",
                                        "typefn",
                                        "union",
                                        "virtual",
                                        "while"};
int precedence(const std::string &S) {
  static const std::vector<std::set<std::string>> Levels = {
      {"=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "|=", "^="},
      {"?"},
      {"||"},
      {"&&"},
      {"|"},
      {"^"},
      {"&"},
      {"==", "!="},
      {"<", "<=", ">", ">="},
      {"<<", ">>"},
      {"+", "-"},
      {"*", "/", "%"}};
  for (size_t I = 0; I < Levels.size(); ++I)
    if (Levels[I].count(S))
      return I + 1;
  return 0;
}
class Parser {
  std::shared_ptr<std::vector<Token>> Tokens;
  size_t Pos = 0;
  const RelationalMembers *BoundRelationalMembers = nullptr;
  unsigned GenericDepth = 0;
  std::string Namespace;
  std::set<std::string> Types, HiddenTypes, TypeParameters;
  // The owner is the declaration identity, which survives lexical shadowing
  // of its name. Only pointer (*) and array ([) layers affect member syntax.
  struct ReceiverType {
    std::string Owner, Layers;
    bool Dependent = false;
    std::shared_ptr<const ReceiverType> CallableResult;
    std::string Scalar;
    std::string TypeParameter;
    ReferenceKind Reference = ReferenceKind::None;
    bool Readonly = false;
    bool QualificationUnknown = false;
    bool ExactNominal = false;
    std::optional<bool> PointeeReadonly;
    std::string PointeeScalar;
    std::shared_ptr<const std::vector<ReceiverType>> Alternatives;
    bool known() const {
      return !Owner.empty() || Dependent || CallableResult || !Scalar.empty() ||
             Alternatives;
    }
    bool operator==(const ReceiverType &Other) const {
      return Owner == Other.Owner && Layers == Other.Layers &&
             Dependent == Other.Dependent && Scalar == Other.Scalar &&
             TypeParameter == Other.TypeParameter &&
             Reference == Other.Reference && Readonly == Other.Readonly &&
             QualificationUnknown == Other.QualificationUnknown &&
             ExactNominal == Other.ExactNominal &&
             PointeeReadonly == Other.PointeeReadonly &&
             PointeeScalar == Other.PointeeScalar &&
             (Alternatives == Other.Alternatives ||
              (Alternatives && Other.Alternatives &&
               *Alternatives == *Other.Alternatives)) &&
             (CallableResult == Other.CallableResult ||
              (CallableResult && Other.CallableResult &&
               *CallableResult == *Other.CallableResult));
    }
  };
  using Receivers = std::map<std::string, ReceiverType>;
  using Site = std::pair<unsigned, unsigned>;
  static Site sourceSite(const Token &At) { return {At.Line, At.Column}; }
  std::vector<Site> PolicyContext;
  Receivers NominalReceivers, ValueReceivers, FieldReceivers;
  std::map<Site, ReceiverType> ReceiverDeclarations, ParameterTypes,
      TypeArguments;
  std::map<Site, ReceiverType> NominalExpressions;
  std::map<std::pair<unsigned, unsigned>, std::string>
      QualifiedMemberExpressions;
  struct RequirementSite {
    std::string Scope;
    llvm::SmallVector<Node, 4> Parameters;
    llvm::SmallVector<Node, 2> Conditions;
    Token DefinedAt;
    bool Pure = true;
    bool RecordScope = false;
    std::set<std::string> ShadowedValues;
    std::vector<Site> Policy;
  };
  struct DefinitionDomain {
    RequirementSite Site;
    const DefinitionDomain *Outer;
  };
  const DefinitionDomain *CurrentDomain = nullptr;
  std::map<std::string, std::shared_ptr<const RequirementSite>>
      NamedRequirements;
  struct CallShape {
    size_t Required;
    std::optional<size_t> Maximum;
    ReceiverType Result;
    std::vector<ReceiverType> Parameters;
    std::optional<size_t> ResultDeduction;
    std::shared_ptr<const RequirementSite> Requirements;
    std::map<std::string, llvm::SmallVector<size_t, 2>> Deductions;
    std::optional<std::vector<std::tuple<size_t, ReferenceKind, bool>>>
        DirectPattern;
    size_t TypeBinders = 0;
    bool Generic = false;
    bool Instance = false, Const = false;
    bool ConstantPredicate = false;
    Site Declaration;
    ReferenceKind Receiver = ReferenceKind::None;
    bool accepts(size_t Count) const {
      return Count >= Required && (!Maximum || Count <= *Maximum);
    }
  };
  std::map<std::string, std::vector<CallShape>> CallResults;
  std::map<std::string, std::vector<ReceiverType>> BaseReceivers;
  std::set<std::string> SpecializedReceivers;
  ReceiverType CurrentReceiver;
  bool ReceiverReadonly = false;
  bool ReceiverAvailable = false;
  std::set<std::string> OwnMembers;
  static ReceiverType recordReceiver(const Node &R, bool Exact = false) {
    ReceiverType Type;
    Type.Owner = "$record." + std::to_string(R.At.Line) + "." +
                 std::to_string(R.At.Column);
    Type.ExactNominal = Exact;
    return Type;
  }
  std::map<std::string, std::string> AliasSchemas;
  void publishReceiver(const Node &Decl, const std::string &Name) {
    if (Decl.K == Node::Function)
      return;
    auto I = ReceiverDeclarations.find({Decl.At.Line, Decl.At.Column});
    if (I == ReceiverDeclarations.end())
      return;
    auto &Bindings = Decl.K == Node::Object || Decl.K == Node::Field
                         ? ValueReceivers
                         : NominalReceivers;
    Bindings[Name] = I->second;
    Bindings["::" + Name] = I->second;
  }
  std::map<std::pair<unsigned, unsigned>, std::string> AliasDeclarations;
  void publishAlias(const Node &Alias, const std::string &Name) {
    auto I = AliasDeclarations.find({Alias.At.Line, Alias.At.Column});
    if (I == AliasDeclarations.end())
      return;
    StringRef Target(I->second);
    auto Canonical = Target.str();
    if (Target.consume_front("::")) {
      Canonical = Target.str();
    } else if (!Target.empty()) {
      StringRef Scope(Name);
      while (Scope.contains("::")) {
        Scope = Scope.rsplit("::").first;
        auto Qualified = (Scope + "::" + Target).str();
        if (Types.count(Qualified)) {
          Canonical = std::move(Qualified);
          break;
        }
      }
    }
    AliasSchemas[Name] = Canonical;
    AliasSchemas["::" + Name] = std::move(Canonical);
  }
  void publishRootAliases(const Node &Decl) {
    publishReceiver(Decl, Decl.Text);
    if (Decl.K == Node::Alias)
      publishAlias(Decl, Decl.Text);
    else if (Decl.K == Node::Linkage)
      for (const auto &Child : Decl.Children)
        publishRootAliases(Child);
  }
  void publishMemberNames(const Node &Owner, const std::string &Prefix) {
    for (const auto &C : Owner.Children) {
      auto Key = Prefix + C.Text;
      publishReceiver(C, Key);
      if (C.K == Node::Record || C.K == Node::Alias ||
          C.K == Node::Enumeration || C.K == Node::Union)
        Types.insert(Key);
      if (C.K == Node::Function && !C.Generics.empty())
        publishCallableFamily(Key, C.Generics);
      else if (!C.Generics.empty() || C.K == Node::Constraint)
        Families[Key] = C.Generics;
      if (C.K == Node::Alias)
        publishAlias(C, Key);
      if (C.K == Node::Record || C.K == Node::Union || C.K == Node::Namespace)
        publishMemberNames(C, Key + "::");
    }
  }
  std::map<std::string, Node> TypeQueries;
  std::map<std::string, std::vector<Node>> Families;
  std::set<std::string> ConflictingCallableSchemas;
  void publishCallableFamily(const std::string &Key,
                             const std::vector<Node> &Parameters) {
    auto &Previous = Families[Key];
    if (!Previous.empty() &&
        (Previous.size() != Parameters.size() ||
         !std::equal(Previous.begin(), Previous.end(), Parameters.begin(),
                     [](const Node &L, const Node &R) {
                       return L.K == R.K && L.Pack == R.Pack;
                     })))
      ConflictingCallableSchemas.insert(Key);
    Previous = Parameters;
  }
  void publishCallResult(const std::string &Key, const ReceiverType &Result,
                         const Node &Function, const Parser &Scope,
                         bool Member) {
    CallShape Shape{0, std::nullopt, Result};
    Shape.Generic = !Function.Generics.empty();
    Shape.Instance = Member && !Function.Settings.count("static");
    Shape.Const = Function.Const;
    Shape.Declaration = sourceSite(Function.At);
    Shape.ConstantPredicate = !Member && !Function.Foreign && !Shape.Generic &&
                              Function.Settings.count("mode") &&
                              Function.Settings.at("mode") == "consteval" &&
                              Result.Scalar == "bool" &&
                              Result.Layers.empty() &&
                              Result.Reference == ReferenceKind::None;
    if (auto Category = Function.Settings.find("category");
        Category != Function.Settings.end())
      Shape.Receiver = referenceKind(Category->second);
    const auto Params = llvm::ArrayRef(Function.Params);
    if (Shape.Generic && llvm::all_of(Function.Generics, [](const Node &G) {
          return G.K == Node::TypeParam && !G.Pack && G.Children.empty();
        })) {
      Shape.TypeBinders = Function.Generics.size();
      Shape.DirectPattern.emplace();
      for (const auto &P : Params) {
        const auto &Type = Scope.ParameterTypes.at(sourceSite(P.At));
        auto Binder = llvm::find_if(Function.Generics, [&](const Node &G) {
          return G.Text == Type.TypeParameter;
        });
        if (P.Pack || !P.Children.empty() || !Type.Layers.empty() ||
            Binder == Function.Generics.end() ||
            StringRef(P.Type).starts_with("forward ")) {
          Shape.DirectPattern.reset();
          break;
        }
        Shape.DirectPattern->emplace_back(Binder - Function.Generics.begin(),
                                          Type.Reference, Type.Readonly);
      }
    }
    if (Shape.Generic && !Function.TemplateArgs.empty()) {
      auto R = std::make_shared<RequirementSite>();
      R->Scope = Scope.Namespace;
      R->Parameters.append(Function.Generics.begin(), Function.Generics.end());
      R->Conditions.push_back(Function.TemplateArgs.front());
      R->DefinedAt = Function.At;
      R->RecordScope = Member || Function.Settings.count("qualifier");
      R->Policy = Scope.PolicyContext;
      Shape.Requirements = std::move(R);
      for (auto [I, P] : llvm::enumerate(Params)) {
        const auto &Type = Scope.ParameterTypes.at(sourceSite(P.At));
        StringRef Pattern(P.Type);
        while (Pattern.consume_back("&")) {
        }
        if (Pattern.consume_front("const<"))
          Pattern.consume_back(">");
        if (!P.Pack && !Type.TypeParameter.empty() &&
            Pattern == Type.TypeParameter)
          Shape.Deductions[Pattern.str()].push_back(I);
      }
    }
    if (llvm::none_of(Params, [](const Node &P) { return P.Pack; })) {
      Shape.Maximum = Params.size();
      auto Defaulted = llvm::find_if(
          Params, [](const Node &P) { return !P.Children.empty(); });
      Shape.Required = std::distance(Params.begin(), Defaulted);
      if (!Shape.Generic)
        for (const auto &P : Params)
          Shape.Parameters.push_back(
              Scope.ParameterTypes.at({P.At.Line, P.At.Column}));
      if (Result.Dependent && Result.Layers.empty() &&
          llvm::any_of(Function.Generics, [&](const Node &G) {
            return G.K == Node::TypeParam && !G.Pack &&
                   G.Text == Result.TypeParameter;
          })) {
        auto Source = llvm::find_if(Params, [&](const Node &P) {
          return P.Type == Result.TypeParameter ||
                 P.Type == Result.TypeParameter + "&" ||
                 P.Type == Result.TypeParameter + "&&";
        });
        if (Source != Params.end())
          Shape.ResultDeduction = std::distance(Params.begin(), Source);
      }
    }
    auto &Overloads = CallResults[Key];
    if (llvm::none_of(Overloads, [&](const CallShape &Existing) {
          return Existing.Required == Shape.Required &&
                 Existing.Maximum == Shape.Maximum &&
                 Existing.Result == Result &&
                 Existing.Parameters == Shape.Parameters &&
                 Existing.ResultDeduction == Shape.ResultDeduction &&
                 Existing.DirectPattern == Shape.DirectPattern &&
                 Existing.TypeBinders == Shape.TypeBinders &&
                 ((!Existing.Requirements && !Shape.Requirements) ||
                  (Existing.Requirements && Shape.Requirements &&
                   sourceSite(Existing.Requirements->DefinedAt) ==
                       sourceSite(Shape.Requirements->DefinedAt))) &&
                 Existing.Generic == Shape.Generic &&
                 Existing.ConstantPredicate == Shape.ConstantPredicate &&
                 Existing.Instance == Shape.Instance &&
                 Existing.Const == Shape.Const &&
                 Existing.Receiver == Shape.Receiver;
        }))
      Overloads.push_back(std::move(Shape));
  }
  std::string indexedMember(const std::string &Owner, StringRef Name) const {
    std::set<std::string> Visited, Matches;
    auto Search = [&](auto &&Self, const std::string &Type) -> void {
      if (Type.empty() || !Visited.insert(Type).second)
        return;
      auto Key = (Type + "::" + Name).str();
      if (OwnMembers.count(Key)) {
        Matches.insert(std::move(Key));
        return;
      }
      if (auto I = BaseReceivers.find(Type); I != BaseReceivers.end())
        for (const auto &Base : I->second)
          Self(Self, Base.Owner);
    };
    Search(Search, Owner);
    return Matches.size() == 1 ? *Matches.begin() : std::string();
  }
  static ReceiverType scalarReceiver(StringRef Name) {
    ReceiverType Result;
    Result.Scalar = Name == "byte" ? "u8" : Name.str();
    return Result;
  }
  static ReceiverType lvalue(ReceiverType Type) {
    Type.Reference = ReferenceKind::Lvalue;
    return Type;
  }
  static ReceiverType alternatives(llvm::ArrayRef<ReceiverType> Types) {
    if (Types.empty() ||
        llvm::any_of(Types, [](const ReceiverType &T) { return !T.known(); }))
      return {};
    if (llvm::all_of(Types,
                     [&](const ReceiverType &T) { return T == Types.front(); }))
      return Types.front();
    ReceiverType View;
    View.Alternatives = std::make_shared<const std::vector<ReceiverType>>(
        Types.begin(), Types.end());
    return View;
  }
  static ReceiverType pointee(ReceiverType Type) {
    Type.Layers.pop_back();
    Type.QualificationUnknown |= !Type.PointeeReadonly;
    Type.Readonly = Type.PointeeReadonly.value_or(false);
    Type.PointeeReadonly.reset();
    Type.Scalar = std::move(Type.PointeeScalar);
    Type.PointeeScalar.clear();
    return lvalue(std::move(Type));
  }
  using BooleanBindings = std::map<std::string, bool>;
  static std::string typeIdentity(const ReceiverType &T) {
    if (T.Dependent || T.QualificationUnknown || T.CallableResult)
      return {};
    auto Identity = T.ExactNominal ? T.Owner : T.Scalar;
    if (T.Layers == "*" && T.PointeeReadonly) {
      Identity = T.ExactNominal ? T.Owner : T.PointeeScalar;
      if (Identity.empty())
        return {};
      if (*T.PointeeReadonly)
        Identity = "const<" + Identity + ">";
      Identity += '*';
    } else if (!T.Layers.empty()) {
      return {};
    }
    if (Identity.empty() || Identity == "integer" || Identity == "real")
      return {};
    if (T.Readonly)
      Identity = "const<" + Identity + ">";
    if (T.Reference != ReferenceKind::None)
      Identity += T.Reference == ReferenceKind::Lvalue ? "&" : "&&";
    return Identity;
  }
  static const Node &argumentFor(const Node &N, bool Type) {
    return N.K == Node::GenericArgument ? N.Children[Type ? 0 : 1] : N;
  }
  const RequirementSite *namedRequirement(const RequirementSite &At,
                                          StringRef Name) const {
    auto Key = scopeKey(At.Scope, Name, [&](const std::string &K) {
      auto I = NamedRequirements.find(K);
      return I != NamedRequirements.end() &&
             sourceSite(I->second->DefinedAt) < sourceSite(At.DefinedAt);
    });
    return Key.empty() ? nullptr : NamedRequirements.at(Key).get();
  }
  static ReceiverType substituteRequirementType(const ReceiverType &Type,
                                                const Receivers &Bindings) {
    if (!Type.Dependent)
      return Type;
    auto Bound = Bindings.find(Type.TypeParameter);
    if (Bound == Bindings.end() || !Type.Layers.empty())
      return {};
    auto Result = Bound->second;
    if (Type.Reference != ReferenceKind::None) {
      if (Result.Reference != ReferenceKind::None)
        return {};
      Result.Reference = Type.Reference;
    }
    Result.Readonly |= Type.Readonly;
    return Result;
  }
  ReceiverType requirementType(const Node &Argument,
                               const Receivers &Bindings) const {
    const auto &N = argumentFor(Argument, true);
    auto Found = TypeArguments.find(sourceSite(N.At));
    if (N.K != Node::TypeArg || Found == TypeArguments.end())
      return {};
    return substituteRequirementType(Found->second, Bindings);
  }
  std::optional<bool> requirementValue(const Node &N,
                                       const RequirementSite &Site,
                                       const Receivers &Types,
                                       const BooleanBindings &Values,
                                       unsigned &Budget) const {
    if (!Budget)
      return std::nullopt;
    --Budget;
    auto Evaluate = [&](const Node &Child) {
      return requirementValue(Child, Site, Types, Values, Budget);
    };
    if (N.K == Node::Unary && N.Text == "!") {
      if (auto Inner = Evaluate(N.Children.front()))
        return !*Inner;
    } else if (N.K == Node::Conditional) {
      if (auto Condition = Evaluate(N.Children.front()))
        return Evaluate(N.Children[*Condition ? 1 : 2]);
    } else if (N.K == Node::Binary) {
      if (N.Text == "&&" || N.Text == "||" || N.Text == "==" ||
          N.Text == "!=") {
        auto Left = Evaluate(N.Children.front());
        if (!Left)
          return std::nullopt;
        if ((N.Text == "&&" && !*Left) || (N.Text == "||" && *Left))
          return Left;
        auto Right = Evaluate(N.Children.back());
        if (!Right || N.Text == "&&" || N.Text == "||")
          return Right;
        return (*Left == *Right) == (N.Text == "==");
      }
    } else if (N.K == Node::Name) {
      if (N.TemplateArgs.empty()) {
        if (N.Text == "true" || N.Text == "false")
          return N.Text == "true";
        if (auto I = Values.find(N.Text); I != Values.end())
          return I->second;
      }
      if (N.Text == "SameType" && N.TemplateArgs.size() == 2) {
        auto L = typeIdentity(requirementType(N.TemplateArgs[0], Types));
        auto R = typeIdentity(requirementType(N.TemplateArgs[1], Types));
        if (!L.empty() && !R.empty())
          return L == R;
        return std::nullopt;
      }
      if (N.Text == "ObjectType" && N.TemplateArgs.size() == 1) {
        auto T = requirementType(N.TemplateArgs.front(), Types);
        if (!typeIdentity(T).empty())
          return T.Scalar != "void" && T.Scalar != "never" &&
                 T.Reference == ReferenceKind::None;
        return std::nullopt;
      }
      if (const auto *Found = namedRequirement(Site, N.Text)) {
        const auto &Named = *Found;
        if (!Named.Pure || Named.Parameters.size() != N.TemplateArgs.size() ||
            llvm::any_of(Named.Parameters,
                         [](const Node &P) { return P.Pack; }))
          return std::nullopt;
        Receivers BoundTypes;
        BooleanBindings BoundValues;
        for (auto [I, P] : llvm::enumerate(Named.Parameters)) {
          const auto &Argument = N.TemplateArgs[I];
          if (Argument.Pack)
            return std::nullopt;
          if (P.K == Node::TypeParam)
            BoundTypes[P.Text] = requirementType(Argument, Types);
          else if (P.Type == "bool")
            if (auto Value = Evaluate(argumentFor(Argument, false)))
              BoundValues[P.Text] = *Value;
        }
        for (const auto &Condition : Named.Conditions) {
          auto Value = requirementValue(Condition, Named, BoundTypes,
                                        BoundValues, Budget);
          if (!Value || !*Value)
            return Value;
        }
        return true;
      }
    }
    return std::nullopt;
  }
  std::optional<bool>
  callRequirement(const CallShape &Shape, const Node &Callee,
                  llvm::ArrayRef<ReceiverType> Actual) const {
    if (!Shape.Requirements)
      return true;
    const auto &Site = *Shape.Requirements;
    if (llvm::any_of(Callee.TemplateArgs,
                     [](const Node &A) { return A.Pack; }) ||
        llvm::any_of(Site.Parameters, [](const Node &P) { return P.Pack; }))
      return std::nullopt;
    Receivers Types;
    BooleanBindings Values;
    unsigned Budget = 128;
    RequirementSite Caller;
    Caller.Scope = Namespace;
    Caller.DefinedAt = Callee.At;
    for (auto [Index, Param] : llvm::enumerate(Site.Parameters)) {
      if (Index < Callee.TemplateArgs.size()) {
        const auto &Argument = Callee.TemplateArgs[Index];
        if (Param.K == Node::TypeParam)
          Types[Param.Text] = requirementType(Argument, {});
        else if (Param.Type == "bool")
          if (auto Value = requirementValue(argumentFor(Argument, false),
                                            Caller, {}, {}, Budget))
            Values[Param.Text] = *Value;
        continue;
      }
      if (Param.K != Node::TypeParam)
        continue;
      auto Source = Shape.Deductions.find(Param.Text);
      if (Source == Shape.Deductions.end())
        continue;
      ReceiverType Binding;
      std::string Identity;
      for (auto I : Source->second) {
        if (I >= Actual.size())
          continue;
        auto Deduced = Actual[I];
        Deduced.Readonly = false;
        Deduced.Reference = ReferenceKind::None;
        auto Key = typeIdentity(Deduced);
        if (Key.empty() || (!Identity.empty() && Identity != Key)) {
          Identity.clear();
          break;
        }
        Identity = std::move(Key);
        Binding = std::move(Deduced);
      }
      if (!Identity.empty())
        Types.emplace(Param.Text, std::move(Binding));
    }
    if (auto Concrete = requirementValue(Site.Conditions.front(), Site, Types,
                                         Values, Budget))
      return Concrete;
    return requirementInDomain(Shape, Callee, Actual, std::move(Types));
  }
  using Formula = ConstraintLogic::Formula;
  struct ValueTerm {
    std::string Identity, Type;
    std::optional<bool> Boolean;
  };
  using ValueTerms = std::map<std::string, ValueTerm>;
  std::optional<ValueTerm> requirementTerm(const Node &Argument,
                                           const ValueTerms &Bindings) const {
    const auto &N = argumentFor(Argument, false);
    if (N.K != Node::Name || !N.TemplateArgs.empty() || Argument.Pack)
      return std::nullopt;
    if (N.Text == "true" || N.Text == "false")
      return ValueTerm{N.Text, "bool", N.Text == "true"};
    if (auto I = Bindings.find(N.Text); I != Bindings.end())
      return I->second;
    return std::nullopt;
  }
  std::optional<ValueTerm> symbolicTerm(const Node &Argument,
                                        const RequirementSite &At,
                                        const ValueTerms &Bindings,
                                        ConstraintLogic &Logic,
                                        unsigned Depth) const {
    Logic.chargeVisit(Depth);
    if (auto Value = requirementTerm(Argument, Bindings))
      return Value;
    const auto &N = argumentFor(Argument, false);
    if (Argument.Pack)
      return std::nullopt;
    if (N.K == Node::Number)
      return ValueTerm{"literal(" + N.Text + ")", "integer", {}};
    if (N.K != Node::Unary && N.K != Node::Binary)
      return std::nullopt;
    std::string Policy;
    for (const auto &[Line, Column] : At.Policy)
      Policy += ":" + std::to_string(Line) + "." + std::to_string(Column);
    auto L = symbolicTerm(N.Children.front(), At, Bindings, Logic, Depth + 1);
    if (!L)
      return std::nullopt;
    StringRef Op(N.Text);
    if (N.K == Node::Unary) {
      if (integer(L->Type) && (Op == "+" || Op == "-"))
        return ValueTerm{
            "unary" + N.Text + Policy + "(" + L->Identity + ")", L->Type, {}};
      return std::nullopt;
    }
    auto R = symbolicTerm(N.Children.back(), At, Bindings, Logic, Depth + 1);
    if (!R || !integer(L->Type) || !integer(R->Type))
      return std::nullopt;
    const std::string Key = "binary" + N.Text + Policy + "(" + L->Identity +
                            ")(" + R->Identity + ")";
    if (Op == "==" || Op == "!=" || Op == "<" || Op == ">" || Op == "<=" ||
        Op == ">=")
      return ValueTerm{Key, "bool", {}};
    if (Op == "+" || Op == "-" || Op == "*" || Op == "/" || Op == "%") {
      auto Type = integerCommonType(L->Type, R->Type);
      if (!Type.empty())
        return ValueTerm{Key, std::move(Type), {}};
    }
    return std::nullopt;
  }
  std::optional<Formula> computedAtom(const Node &N, const RequirementSite &At,
                                      const ValueTerms &Values,
                                      ConstraintLogic &Logic,
                                      unsigned Depth) const {
    const auto &Callee = N.Children.front();
    if (Callee.K != Node::Name || Callee.ExplicitApplication ||
        Values.count(Callee.Text) || At.ShadowedValues.count(Callee.Text) ||
        (At.RecordScope && !StringRef(Callee.Text).starts_with("::")))
      return std::nullopt;
    const CallShape *Selected = nullptr;
    auto Visible = [&](const CallShape &S) {
      return S.Declaration < sourceSite(At.DefinedAt) &&
             S.accepts(N.Children.size() - 1);
    };
    auto Key = scopeKey(At.Scope, Callee.Text, [&](const std::string &K) {
      auto Found = CallResults.find(K);
      return Found != CallResults.end() && llvm::any_of(Found->second, Visible);
    });
    if (Key.empty())
      return std::nullopt;
    llvm::SmallVector<ValueTerm, 4> Arguments;
    for (const auto &Argument : llvm::ArrayRef(N.Children).drop_front()) {
      auto Value = symbolicTerm(Argument, At, Values, Logic, Depth + 1);
      if (!Value)
        return std::nullopt;
      Arguments.push_back(std::move(*Value));
    }
    for (const auto &S : CallResults.at(Key)) {
      if (!Visible(S))
        continue;
      if (S.Generic || S.Parameters.size() != Arguments.size() ||
          llvm::any_of(S.Parameters, [](const ReceiverType &P) {
            return P.Reference != ReferenceKind::None || P.Scalar.empty() ||
                   !P.Layers.empty() || P.Dependent;
          }))
        return std::nullopt;
      // Among plain scalar value parameters, an exact signature outranks all
      // implicit numeric conversions. Unestablished reference or generic
      // ranks above are left to semantic binding.
      if (std::equal(S.Parameters.begin(), S.Parameters.end(),
                     Arguments.begin(),
                     [](const ReceiverType &P, const ValueTerm &A) {
                       return P.Scalar == A.Type;
                     })) {
        if (Selected || !S.ConstantPredicate)
          return std::nullopt;
        Selected = &S;
      }
    }
    if (!Selected)
      return std::nullopt;
    std::string Atom = "consteval:" + Key + ":" +
                       std::to_string(Selected->Declaration.first) + "." +
                       std::to_string(Selected->Declaration.second);
    for (const auto &Value : Arguments)
      Atom += "(" + Value.Identity + ")";
    return Logic.variable(Atom);
  }
  std::optional<Formula>
  constraintFormula(const Node &N, const RequirementSite &At,
                    const Receivers &Bindings, ConstraintLogic &Logic,
                    unsigned Depth, const ValueTerms &Values = {}) const {
    Logic.chargeVisit(Depth);
    auto Build = [&](const Node &Child) {
      return constraintFormula(Child, At, Bindings, Logic, Depth + 1, Values);
    };
    if (N.K == Node::Unary && N.Text == "!") {
      if (auto Value = Build(N.Children.front()))
        return Logic.negate(*Value);
    } else if (N.K == Node::Binary && (N.Text == "&&" || N.Text == "||")) {
      auto L = Build(N.Children.front());
      if (!L || *L == (N.Text == "&&" ? 0u : 1u))
        return L;
      if (auto R = Build(N.Children.back()))
        return N.Text == "&&" ? Logic.conjunction(*L, *R)
                              : Logic.disjunction(*L, *R);
    } else if (N.K == Node::Call) {
      return computedAtom(N, At, Values, Logic, Depth);
    } else if (N.K == Node::Binary) {
      if (auto Term = symbolicTerm(N, At, Values, Logic, Depth + 1);
          Term && Term->Type == "bool")
        return Logic.variable(Term->Identity);
    } else if (N.K == Node::Name) {
      if (N.Text == "true" || N.Text == "false")
        return N.Text == "true";
      if (auto V = requirementTerm(N, Values); V && V->Type == "bool") {
        if (V->Boolean)
          return unsigned(*V->Boolean);
        return Logic.variable(V->Identity);
      }
      if (builtinPredicate(N.Text)) {
        std::string Key = N.Text;
        bool Symbolic = false;
        for (const auto &A : N.TemplateArgs) {
          auto Type = typeIdentity(requirementType(A, Bindings));
          if (Type.empty() || A.Pack)
            return std::nullopt;
          Symbolic |= StringRef(Type).contains("$constraint.");
          Key += "(" + Type + ")";
        }
        if (Symbolic)
          return Logic.variable(Key);
        unsigned Budget = 128;
        if (auto Value = requirementValue(N, At, Bindings, {}, Budget))
          return unsigned(*Value);
      } else if (const auto *Named = namedRequirement(At, N.Text)) {
        if (Named->Parameters.size() != N.TemplateArgs.size())
          return std::nullopt;
        Receivers Nested;
        ValueTerms NestedValues;
        std::string Application =
            "requirement:" + std::to_string(Named->DefinedAt.Line) + "." +
            std::to_string(Named->DefinedAt.Column);
        bool KnownArguments = true;
        for (auto [I, P] : llvm::enumerate(Named->Parameters)) {
          if (P.Pack || N.TemplateArgs[I].Pack)
            return std::nullopt;
          if (P.K == Node::TypeParam) {
            auto T = requirementType(N.TemplateArgs[I], Bindings);
            auto Key = typeIdentity(T);
            KnownArguments &= !Key.empty();
            Application += "(type:" + Key + ")";
            Nested[P.Text] = std::move(T);
          } else if (auto V = symbolicTerm(N.TemplateArgs[I], At, Values, Logic,
                                           Depth + 1);
                     V && V->Type == valueParameterType(P)) {
            Application += "(value:" + V->Type + ":" + V->Identity + ")";
            NestedValues[P.Text] = std::move(*V);
          } else {
            KnownArguments = false;
          }
        }
        Formula Result = 1;
        for (auto [Index, Clause] : llvm::enumerate(Named->Conditions)) {
          std::optional<Formula> F;
          if (Clause.K == Node::Empty) {
            if (KnownArguments)
              F = Logic.variable(Application + "/" + std::to_string(Index));
          } else {
            F = constraintFormula(Clause, *Named, Nested, Logic, Depth + 1,
                                  NestedValues);
          }
          if (!F)
            return std::nullopt;
          Result = Logic.conjunction(Result, *F);
          if (!Result)
            break;
        }
        return Result;
      }
    }
    return std::nullopt;
  }
  std::string valueParameterType(const Node &P) const {
    auto Found = ParameterTypes.find(sourceSite(P.At));
    if (Found == ParameterTypes.end())
      return {};
    return typeIdentity(Found->second);
  }
  struct DefinitionEvidence {
    Receivers Types;
    ValueTerms Values;
    Formula Assumed = 1;
  };
  DefinitionEvidence definitionEvidence(ConstraintLogic &Logic) const {
    llvm::SmallVector<const DefinitionDomain *, 4> Domains;
    for (auto *D = CurrentDomain; D; D = D->Outer)
      Domains.push_back(D);
    DefinitionEvidence Evidence;
    for (auto *D : llvm::reverse(Domains)) {
      for (auto [I, P] : llvm::enumerate(D->Site.Parameters)) {
        Evidence.Types.erase(P.Text);
        Evidence.Values.erase(P.Text);
        auto Identity = "$constraint." + std::to_string(P.At.Line) + "." +
                        std::to_string(P.At.Column) + "." + std::to_string(I);
        if (P.K == Node::TypeParam && !P.Pack)
          Evidence.Types[P.Text] = scalarReceiver(Identity);
        else if (!P.Pack)
          if (auto Type = valueParameterType(P); !Type.empty())
            Evidence.Values[P.Text] = {
                std::move(Identity), std::move(Type), {}};
      }
      if (!D->Site.Conditions.empty()) {
        auto VisibleValues = Evidence.Values;
        for (const auto &Hidden : D->Site.ShadowedValues)
          VisibleValues.erase(Hidden);
        for (const auto &Clause : D->Site.Conditions)
          if (auto Known = constraintFormula(Clause, D->Site, Evidence.Types,
                                             Logic, 0, VisibleValues))
            Evidence.Assumed = Logic.conjunction(Evidence.Assumed, *Known);
      }
    }

    return Evidence;
  }
  ReceiverType refineReceiver(ReceiverType Type, const Token &At) const {
    if (!CurrentDomain || !Type.Dependent || Type.TypeParameter.empty() ||
        NominalReceivers.count(Type.TypeParameter) ||
        HiddenTypes.count(Type.TypeParameter) ||
        (!Type.Layers.empty() && Type.Layers != "*"))
      return Type;
    unsigned Steps = 0;
    ConstraintLogic Logic([&](unsigned Depth) {
      if (Depth > 128 || ++Steps > 2048)
        throw ResourceExhausted{
            {At, "constraint syntax binding resource exhausted"}};
    });
    try {
      auto Evidence = definitionEvidence(Logic);
      if (Evidence.Assumed < 2)
        return Type;
      auto Param = Evidence.Types.find(Type.TypeParameter);
      if (Param == Evidence.Types.end())
        return Type;
      const std::string Symbol = typeIdentity(Param->second);
      const ReceiverType *Bound = nullptr;
      std::string Identity;
      auto ImpliesEquality = [&](const std::string &L, const std::string &R) {
        auto Atom = Logic.findVariable("SameType(" + L + ")(" + R + ")");
        return Atom &&
               Logic.conjunction(Evidence.Assumed, Logic.negate(*Atom)) == 0;
      };
      auto Equal = [&](const std::string &L, const std::string &R) {
        return ImpliesEquality(L, R) || ImpliesEquality(R, L);
      };
      llvm::SmallVector<std::string, 4> Connected{Symbol};
      std::set<std::string> Seen{Symbol};
      for (size_t I = 0; I < Connected.size(); ++I) {
        const auto Current = Connected[I];
        for (const auto &[Name, Variable] : Evidence.Types) {
          auto Other = typeIdentity(Variable);
          if (!Seen.count(Other) && Equal(Current, Other)) {
            Seen.insert(Other);
            Connected.push_back(std::move(Other));
          }
        }
      }
      for (const auto &[Site, Candidate] : TypeArguments) {
        if (!Candidate.ExactNominal)
          continue;
        auto Concrete = typeIdentity(Candidate);
        if (Concrete.empty() || Concrete == Identity ||
            llvm::none_of(Connected, [&](const auto &Prior) {
              return Equal(Prior, Concrete);
            }))
          continue;
        if (Bound)
          return Type;
        Identity = std::move(Concrete);
        Bound = &Candidate;
      }
      if (Bound) {
        if (Type.Layers.empty())
          return substituteRequirementType(Type,
                                           {{Type.TypeParameter, *Bound}});
        if (Bound->Layers.empty() && Bound->Reference == ReferenceKind::None) {
          auto Pointer = *Bound;
          Pointer.Layers = "*";
          Pointer.PointeeReadonly =
              Pointer.Readonly || Type.PointeeReadonly.value_or(false);
          Pointer.Readonly = Type.Readonly;
          Pointer.Reference = Type.Reference;
          return Pointer;
        }
      }
    } catch (const ResourceExhausted &) {
      // The caller can still have declaration-kind evidence independent of
      // an exact receiver identity.
    }
    return Type;
  }
  std::optional<bool> requirementInDomain(const CallShape &Shape,
                                          const Node &Callee,
                                          llvm::ArrayRef<ReceiverType> Actual,
                                          Receivers CandidateTypes) const {
    if (!CurrentDomain)
      return std::nullopt;
    unsigned Steps = 0;
    ConstraintLogic Logic([&](unsigned Depth) {
      if (Depth > 128 || ++Steps > 2048)
        throw ResourceExhausted{
            {Callee.At, "constraint syntax binding resource exhausted"}};
    });
    try {
      auto Evidence = definitionEvidence(Logic);
      auto &DomainTypes = Evidence.Types;
      auto &DomainValues = Evidence.Values;
      const auto Assumed = Evidence.Assumed;
      if (Assumed == 0)
        return std::nullopt;
      ValueTerms CandidateValues;
      for (const auto &[Name, Binding] : ValueReceivers)
        DomainValues.erase(Name);
      for (const auto &[Name, Binding] :
           llvm::make_early_inc_range(DomainTypes))
        if (NominalReceivers.count(Name) || HiddenTypes.count(Name))
          DomainTypes.erase(Name);
      const auto &Target = *Shape.Requirements;
      RequirementSite Caller;
      Caller.Policy = PolicyContext;
      for (auto [I, P] : llvm::enumerate(Target.Parameters)) {
        if (I < Callee.TemplateArgs.size()) {
          if (P.K == Node::TypeParam)
            CandidateTypes[P.Text] =
                requirementType(Callee.TemplateArgs[I], DomainTypes);
          else if (auto V = symbolicTerm(Callee.TemplateArgs[I], Caller,
                                         DomainValues, Logic, 0);
                   V && V->Type == valueParameterType(P))
            CandidateValues[P.Text] = std::move(*V);
          continue;
        }
        auto Source = Shape.Deductions.find(P.Text);
        if (P.K != Node::TypeParam || Source == Shape.Deductions.end())
          continue;
        std::string Identity;
        ReceiverType Agreed;
        for (auto Pos : Source->second) {
          if (Pos >= Actual.size())
            continue;
          auto Type = substituteRequirementType(Actual[Pos], DomainTypes);
          Type.Reference = ReferenceKind::None;
          Type.Readonly = false;
          auto Key = typeIdentity(Type);
          if (Key.empty() || (!Identity.empty() && Key != Identity)) {
            Identity.clear();
            break;
          }
          Identity = std::move(Key);
          Agreed = std::move(Type);
        }
        if (!Identity.empty())
          CandidateTypes[P.Text] = std::move(Agreed);
      }
      auto Needed =
          constraintFormula(Target.Conditions.front(), Target, CandidateTypes,
                            Logic, 0, CandidateValues);
      if (Needed && Logic.conjunction(Assumed, *Needed) == 0)
        return false;
      if (Needed && Logic.conjunction(Assumed, Logic.negate(*Needed)) == 0)
        return true;
    } catch (const ResourceExhausted &) {
      // The semantic checker owns the configured proof budget and diagnostics.
    }
    return std::nullopt;
  }
  std::optional<Formula> constraintFormula(const CallShape &Shape,
                                           ConstraintLogic &Logic) const {
    if (!Shape.Requirements)
      return 1;
    const auto &At = *Shape.Requirements;
    Receivers Bindings;
    for (auto [I, P] : llvm::enumerate(At.Parameters))
      Bindings[P.Text] = scalarReceiver("$constraint." + std::to_string(I));
    return constraintFormula(At.Conditions.front(), At, Bindings, Logic, 0);
  }
  bool strongerRequirements(const CallShape &L, const CallShape &R,
                            const Token &At) const {
    if (!L.Requirements || !L.DirectPattern ||
        L.DirectPattern != R.DirectPattern || L.TypeBinders != R.TypeBinders ||
        L.Instance != R.Instance || L.Const != R.Const ||
        L.Receiver != R.Receiver)
      return false;
    unsigned Steps = 0;
    ConstraintLogic Logic([&](unsigned Depth) {
      if (Depth > 128 || ++Steps > 2048)
        throw ResourceExhausted{
            {At, "constraint syntax binding resource exhausted"}};
    });
    try {
      auto A = constraintFormula(L, Logic), B = constraintFormula(R, Logic);
      return A && B && Logic.stronger(*A, *B);
    } catch (const ResourceExhausted &) {
      // Semantic binding owns the configured solver budget and its diagnostics.
      return false;
    }
  }
  struct ConversionEvidence {
    unsigned Minimum = 0;
    bool Exact = false;
  };
  static std::optional<ConversionEvidence>
  bindingEvidence(const ReceiverType &Argument, const ReceiverType &Parameter) {
    bool Scalar = !Argument.Scalar.empty() && !Parameter.Scalar.empty();
    bool Nominal = Argument.ExactNominal && Parameter.ExactNominal;
    bool Pointer = Argument.Layers == "*" && Parameter.Layers == "*" &&
                   Argument.PointeeReadonly && Parameter.PointeeReadonly &&
                   (Nominal || (!Argument.PointeeScalar.empty() &&
                                !Parameter.PointeeScalar.empty()));
    if (Argument.Scalar == "never" || Argument.Scalar == "integer" ||
        Argument.Scalar == "real" || Argument.QualificationUnknown ||
        Parameter.QualificationUnknown)
      return ConversionEvidence{};
    if ((StringRef(Argument.Layers).ends_with("*") &&
         !Parameter.Scalar.empty()) ||
        (StringRef(Parameter.Layers).ends_with("*") &&
         !Argument.Scalar.empty() && Argument.Scalar != "nullptr_t"))
      return std::nullopt;
    if (!Pointer && ((!Scalar && !Nominal) || !Argument.Layers.empty() ||
                     !Parameter.Layers.empty()))
      return ConversionEvidence{};
    const bool Lvalue = Argument.Reference == ReferenceKind::Lvalue;
    auto Rank = referenceBindingRank(Parameter.Reference, Parameter.Readonly,
                                     Argument.Readonly, Lvalue);
    if (!Rank)
      return std::nullopt;
    if (Pointer) {
      const bool Same = Nominal
                            ? Argument.Owner == Parameter.Owner
                            : Argument.PointeeScalar == Parameter.PointeeScalar;
      const bool SourceConst = *Argument.PointeeReadonly;
      const bool TargetConst = *Parameter.PointeeReadonly;
      if (Same && SourceConst == TargetConst)
        return ConversionEvidence{*Rank, true};
      if ((SourceConst && !TargetConst) || (!Nominal && !Same) ||
          (Parameter.Reference != ReferenceKind::None && Lvalue))
        return std::nullopt;
      return ConversionEvidence{1, false};
    }
    if (Scalar ? Argument.Scalar == Parameter.Scalar
               : Argument.Owner == Parameter.Owner)
      return ConversionEvidence{*Rank, true};
    if (Nominal) {
      if (Parameter.Reference == ReferenceKind::None)
        return std::nullopt;
      return ConversionEvidence{1 + *Rank, false};
    }
    if (Parameter.Reference != ReferenceKind::None && Lvalue)
      return std::nullopt;
    // Different scalar identities can only participate through conversion.
    // Value-dependent numeric viability is still checked by semantic binding.
    return ConversionEvidence{3, false};
  }
  ReceiverType callReceiver(const Node &Call) const {
    const auto &Callee = Call.Children.front();
    ReceiverType Callable;
    std::optional<ReceiverType> Object;
    std::string Key;
    if (Callee.K == Node::Member) {
      auto Base =
          refineReceiver(receiverType(Callee.Children.front()), Callee.At);
      if (Base.Dependent)
        return Base;
      if (Base.Layers == (Callee.Definition ? "*" : "")) {
        Key = indexedMember(Base.Owner, Callee.Text);
        Object = Callee.Definition ? pointee(Base) : Base;
      }
      if (auto I = FieldReceivers.find(Key); I != FieldReceivers.end())
        Callable = I->second;
    } else if (Callee.K == Node::Name && !ValueReceivers.count(Callee.Text)) {
      auto Name = StringRef(Callee.Text);
      bool Root = Name.consume_front("::");
      if ((Name == "std::move" || Name == "std::forward") &&
          Call.Children.size() == 2) {
        auto Type = receiverType(Call.Children.back());
        if (Name == "std::move")
          Type.Reference = ReferenceKind::Rvalue;
        else
          Type.Scalar.clear();
        return Type;
      }
      const auto Site = std::pair(Callee.At.Line, Callee.At.Column);
      if (auto I = NominalExpressions.find(Site); I != NominalExpressions.end())
        return I->second;
      if (auto I = QualifiedMemberExpressions.find(Site);
          I != QualifiedMemberExpressions.end())
        Key = I->second;
      else if (!Root && !Name.contains("::")) {
        Key = indexedMember(CurrentReceiver.Owner, Name);
        if (!Key.empty() && ReceiverAvailable) {
          Object = lvalue(CurrentReceiver);
          Object->Readonly = ReceiverReadonly;
        }
      }
      if (Key.empty())
        Key = scopeKey(Namespace, Callee.Text, [&](const std::string &Entry) {
          return CallResults.count(Entry);
        });
    } else
      Callable = receiverType(Callee);
    if (Callable.CallableResult &&
        (Callable.Layers == "*" || Callable.Layers.empty()))
      return *Callable.CallableResult;
    if (auto I = CallResults.find(Key); I != CallResults.end()) {
      const auto Args = llvm::ArrayRef(Call.Children).drop_front();
      const bool Expanded =
          llvm::any_of(Args, [](const Node &A) { return A.Pack; });
      struct Candidate {
        ReceiverType Result;
        llvm::SmallVector<ConversionEvidence, 4> Ranks;
        const CallShape *Shape;
        bool RequirementsHold;
      };
      llvm::SmallVector<ReceiverType, 4> Types;
      if (!Expanded)
        for (const auto &Arg : Args)
          Types.push_back(receiverType(Arg));
      llvm::SmallVector<Candidate, 4> Viable;
      for (const auto &Overload : I->second) {
        if ((Callee.ExplicitApplication && !Overload.Generic) ||
            (!Expanded && !Overload.accepts(Args.size())))
          continue;
        auto Requirement = Expanded ? std::optional<bool>{}
                                    : callRequirement(Overload, Callee, Types);
        if (Requirement && !*Requirement)
          continue;
        Candidate C{
            Overload.Result, {}, &Overload, Requirement.value_or(false)};
        if (!Expanded && !Callee.ExplicitApplication &&
            Overload.ResultDeduction &&
            *Overload.ResultDeduction < Types.size()) {
          const auto &Source = Types[*Overload.ResultDeduction];
          if (Source.known() && Source.Scalar != "integer" &&
              Source.Scalar != "real") {
            C.Result = Source;
            C.Result.Reference = Overload.Result.Reference;
            C.Result.Readonly = Overload.Result.Readonly;
            C.Result.QualificationUnknown |=
                Source.Readonly &&
                Overload.Result.Reference != ReferenceKind::None;
          }
        }
        if (!Expanded && Overload.Parameters.size() >= Types.size()) {
          for (size_t A = 0; A < Types.size(); ++A) {
            auto Rank = bindingEvidence(Types[A], Overload.Parameters[A]);
            if (!Rank)
              break;
            C.Ranks.push_back(*Rank);
          }
          if (C.Ranks.size() != Types.size())
            continue;
        } else {
          C.Ranks.resize(Types.size());
        }
        ConversionEvidence ReceiverRank{0, true};
        if (Overload.Instance) {
          if (!Object) {
            if (!ReceiverAvailable)
              continue;
            ReceiverRank.Exact = false;
          } else if (Object->QualificationUnknown) {
            ReceiverRank.Exact = false;
          } else {
            auto Rank = receiverBindingRank(
                Overload.Receiver, Overload.Const, Object->Readonly,
                Object->Reference != ReferenceKind::Lvalue);
            if (!Rank)
              continue;
            ReceiverRank.Minimum = *Rank;
          }
        }
        C.Ranks.push_back(ReceiverRank);
        Viable.push_back(std::move(C));
      }
      if (!Viable.empty() && llvm::all_of(Viable, [&](const Candidate &C) {
            return C.Result == Viable.front().Result;
          }))
        return Viable.front().Result;
      llvm::SmallVector<ReceiverType, 4> Results;
      auto Better = [&](const Candidate &A, const Candidate &B) {
        bool Strict = false;
        bool Dominates = true;
        for (size_t I = 0; I < A.Ranks.size(); ++I) {
          if (!A.Ranks[I].Exact || A.Ranks[I].Minimum > B.Ranks[I].Minimum)
            Dominates = false;
          Strict |= A.Ranks[I].Minimum < B.Ranks[I].Minimum;
        }
        return (Dominates && Strict) ||
               (A.RequirementsHold && A.Shape != B.Shape &&
                strongerRequirements(*A.Shape, *B.Shape, Callee.At));
      };
      for (const auto &C : Viable) {
        if (llvm::any_of(Viable,
                         [&](const Candidate &O) { return Better(O, C); }))
          continue;
        Results.push_back(C.Result);
      }
      return alternatives(Results);
    }
    return {};
  }
  ReceiverType receiverType(const Node &N) const {
    if (N.K == Node::Number || N.K == Node::Real)
      return scalarReceiver(N.K == Node::Number ? "integer" : "real");
    if (N.K == Node::Character)
      return scalarReceiver("char");
    if (N.K == Node::Name) {
      if (N.Text == "true" || N.Text == "false")
        return scalarReceiver("bool");
      if (N.Text == "nullptr")
        return scalarReceiver("nullptr_t");
      if (N.Text == "this" && !CurrentReceiver.Owner.empty()) {
        auto Self = CurrentReceiver;
        Self.Layers += '*';
        Self.PointeeReadonly = ReceiverReadonly;
        return Self;
      }
      auto Key = indexedMember(CurrentReceiver.Owner, N.Text);
      if (auto I = ValueReceivers.find(N.Text); I != ValueReceivers.end()) {
        auto Value = lvalue(I->second);
        // The field index is also visible in lexical bindings. A local that
        // shadows the field may have the same type but different qualification.
        if (ReceiverReadonly && FieldReceivers.count(Key))
          Value.QualificationUnknown = true;
        return Value;
      }
      if (auto I = FieldReceivers.find(Key); I != FieldReceivers.end()) {
        auto Field = lvalue(I->second);
        Field.Readonly |= ReceiverReadonly;
        return Field;
      }
      return {};
    }
    if (N.K == Node::Configured)
      return receiverType(N.Children.front());
    if (N.K == Node::Call)
      return callReceiver(N);
    if (N.K == Node::Conditional) {
      auto Left = receiverType(N.Children[1]);
      auto Right = receiverType(N.Children[2]);
      if (Left == Right)
        return Left;
      if (!Left.Owner.empty() && Left.Owner == Right.Owner &&
          Left.Layers == Right.Layers) {
        Left.QualificationUnknown = true;
        Left.ExactNominal &= Right.ExactNominal;
        return Left;
      }
      return {};
    }
    if (N.K == Node::Binary) {
      StringRef Op(N.Text);
      if (Op == "&&" || Op == "||")
        return scalarReceiver("bool");
      auto L = receiverType(N.Children[0]).Scalar;
      auto R = receiverType(N.Children[1]).Scalar;
      if (L.empty() || R.empty() || L == "never" || R == "never")
        return {};
      if (Op == "==" || Op == "!=" || Op == "<" || Op == ">" || Op == "<=" ||
          Op == ">=")
        return scalarReceiver("bool");
      if (integer(L) && integer(R)) {
        if (Op == "<<" || Op == ">>")
          return scalarReceiver(L);
        if (Op == "+" || Op == "-" || Op == "*" || Op == "/" || Op == "%" ||
            Op == "&" || Op == "|" || Op == "^")
          return scalarReceiver(integerCommonType(L, R));
      }
      if (Op == "+" || Op == "-" || Op == "*" || Op == "/") {
        if (L == "f64" || R == "f64")
          return scalarReceiver("f64");
        if (L == "f32" || R == "f32")
          return scalarReceiver("f32");
      }
      return {};
    }
    if (N.K == Node::Member)
      return fieldReceiver(receiverType(N.Children.front()), N);
    if (N.K != Node::Unary && N.K != Node::Index)
      return {};
    auto Base = receiverType(N.Children.front());
    if (Base.Dependent)
      return Base;
    if (!Base.known())
      return {};
    if (N.K == Node::Unary && N.Text == "&") {
      Base.PointeeScalar = Base.Layers.empty() ? Base.Scalar : std::string{};
      if (Base.Layers.empty() && !Base.QualificationUnknown)
        Base.PointeeReadonly = Base.Readonly;
      else
        Base.PointeeReadonly.reset();
      Base.Layers += '*';
      Base.Reference = ReferenceKind::None;
      Base.Readonly = false;
      Base.Scalar.clear();
      return Base;
    }
    if (N.K == Node::Index || N.Text == "*") {
      if (StringRef(Base.Layers).ends_with("*")) {
        return pointee(std::move(Base));
      }
      if (N.K == Node::Index && StringRef(Base.Layers).ends_with("[")) {
        Base.Layers.pop_back();
        return lvalue(Base);
      }
    }
    return {};
  }
  ReceiverType fieldReceiver(ReceiverType Base, const Node &N) const {
    if (Base.Alternatives) {
      llvm::SmallVector<ReceiverType, 4> Fields;
      for (const auto &Alternative : *Base.Alternatives)
        Fields.push_back(fieldReceiver(Alternative, N));
      return alternatives(Fields);
    }
    Base = refineReceiver(std::move(Base), N.At);
    if (Base.Dependent)
      return Base;
    if (Base.Owner.empty() || Base.Layers != (N.Definition ? "*" : ""))
      return {};
    auto I = FieldReceivers.find(indexedMember(Base.Owner, N.Text));
    if (I == FieldReceivers.end())
      return {};
    if (N.Definition)
      Base = pointee(std::move(Base));
    auto Field = lvalue(I->second);
    Field.Readonly |= Base.Readonly;
    Field.QualificationUnknown |=
        Base.QualificationUnknown || Base.Reference != ReferenceKind::Lvalue;
    return Field;
  }
  bool canConfirmMember(const Node &Receiver) const {
    if (!BoundRelationalMembers)
      return false;
    if (!GenericDepth)
      return true;
    // A plain free call with no runtime arguments and only fixed explicit
    // arguments has the same receiver type in every instantiation.
    if (!CurrentReceiver.Owner.empty() || Receiver.K != Node::Call ||
        Receiver.Children.size() != 1)
      return false;
    const auto &Callee = Receiver.Children.front();
    if (Callee.K != Node::Name || !Callee.ExplicitApplication ||
        Callee.TemplateArgs.empty() || ValueReceivers.count(Callee.Text) ||
        NominalExpressions.count(sourceSite(Callee.At)) ||
        StringRef(Callee.Text).contains('<') ||
        scopeKey(Namespace, Callee.Text, [&](const std::string &K) {
          return CallResults.count(K);
        }).empty())
      return false;
    return llvm::all_of(Callee.TemplateArgs, [&](const Node &Argument) {
      if (Argument.Pack)
        return false;
      if (Argument.K == Node::TypeArg) {
        auto Shape = TypeArguments.find(sourceSite(Argument.At));
        return Shape != TypeArguments.end() &&
               !typeIdentity(Shape->second).empty();
      }
      return Argument.K == Node::Number || Argument.K == Node::Real ||
             Argument.K == Node::Character ||
             (Argument.K == Node::Name &&
              (Argument.Text == "true" || Argument.Text == "false"));
    });
  }
  struct MemberSyntax {
    std::string Key;
    bool Generic = false;
    bool Deferred = false;
  };
  std::optional<MemberSyntax>
  memberFamily(ReceiverType Type, const Token &Member, bool Pointer) const {
    if (Type.Alternatives) {
      std::optional<MemberSyntax> Agreed;
      for (const auto &Alternative : *Type.Alternatives) {
        auto Found = memberFamily(Alternative, Member, Pointer);
        if (!Found || (Agreed && Found->Generic != Agreed->Generic))
          return std::nullopt;
        if (!Agreed)
          Agreed = std::move(Found);
        else if (Agreed->Generic)
          Agreed->Deferred |= Found->Deferred || Found->Key != Agreed->Key;
      }
      return Agreed;
    }
    Type = refineReceiver(std::move(Type), Member);
    if (!Type.Owner.empty() && Type.Layers == (Pointer ? "*" : "")) {
      auto Key = indexedMember(Type.Owner, Member.Text);
      if (Families.count(Key))
        return MemberSyntax{Key, true,
                            ConflictingCallableSchemas.count(Key) != 0};
      if (!Key.empty())
        return MemberSyntax{};
    }
    return std::nullopt;
  }
  bool IndexingMembers = false;
  unsigned Depth = 0;
  struct Nest {
    unsigned &D;
    Nest(unsigned &D, const Token &T) : D(D) {
      if (++D > 512)
        fail(T, "source nesting limit exceeded");
    }
    ~Nest() { --D; }
  };
  const Token &peek(size_t N = 0) const {
    return (*Tokens)[std::min(Pos + N, Tokens->size() - 1)];
  }
  bool is(StringRef S) const { return peek().Text == S; }
  bool eat(StringRef S) {
    if (!is(S))
      return false;
    ++Pos;
    return true;
  }
  Token take() {
    auto T = peek();
    if (T.Text.empty())
      fail(T, "unexpected end of input");
    ++Pos;
    return T;
  }
  Token expect(StringRef S) {
    auto T = peek();
    if (!eat(S))
      fail(T, "expected '" + S.str() + "'");
    return T;
  }
  Token name() {
    auto T = take();
    if (!identifier(T.Text) || Reserved.count(T.Text) || builtin(T.Text))
      fail(T, "expected identifier");
    return T;
  }
  Token operatorName() {
    Token T = expect("operator");
    if (eat("(")) {
      expect(")");
      T.Text = "operator()";
    } else if (eat("[")) {
      expect("]");
      T.Text = "operator[]";
    } else if (is("prefix") || is("postfix")) {
      auto Form = take();
      if (!is("++") && !is("--"))
        fail(peek(), "expected increment or decrement operator");
      T.Text += " " + Form.Text + " " + take().Text;
    } else {
      auto Op = take();
      if ((!precedence(Op.Text) && Op.Text != "!" && Op.Text != "~") ||
          Op.Text == "&&" || Op.Text == "||" || Op.Text == "?")
        fail(Op, "invalid overloadable operator");
      T.Text += Op.Text;
    }
    return T;
  }
  Node baseSelector() {
    Node Selector(Node::TypeArg, peek());
    if (is("base_path") && peek(1).Text == "<") {
      take();
      expect("<");
      do {
        Node Edge(Node::TypeArg, peek());
        Edge.Type = type();
        Selector.TemplateArgs.push_back(Edge);
      } while (eat(","));
      closeAngle();
      Selector.Type = Selector.TemplateArgs.back().Type;
    } else
      Selector.Type = type();
    return Selector;
  }
  bool opensBitArgumentTemplate(size_t Angle) const {
    size_t I = Angle - 1;
    std::string Name = peek(I).Text;
    if (!identifier(Name))
      return false;
    while (I >= 2 && peek(I - 1).Text == "::" && identifier(peek(I - 2).Text)) {
      I -= 2;
      Name = peek(I).Text + "::" + Name;
    }
    return known(Name) || Families.count(Name) ||
           integerLibraryName(Name, true) || floatingSpecialName(Name) ||
           builtinPredicate(Name);
  }
  std::optional<unsigned> bitExtractionArity() const {
    // The standard has a single type argument on the dynamic form and two
    // constant arguments on the static form.
    int Angles = 1, Group = 0;
    unsigned Count = 1;
    for (size_t I = 1; !peek(I).Text.empty(); ++I) {
      StringRef Word = peek(I).Text;
      if (Word == ";" || Word == "{" || Word == "}")
        break;
      if (Word == "(" || Word == "[")
        ++Group;
      else if (Word == ")" || Word == "]") {
        if (Group == 0)
          break;
        --Group;
      } else if (Group == 0) {
        if (Word == "," && Angles == 1)
          ++Count;
        else if (Word == "<" && opensBitArgumentTemplate(I))
          ++Angles;
        else if (Word == ">" || Word == ">>") {
          Angles -= Word == ">" ? 1 : 2;
          if (Angles <= 0)
            return Angles == 0 && peek(I + 1).Text == "("
                       ? std::optional<unsigned>(Count)
                       : std::nullopt;
        }
      }
    }
    return std::nullopt;
  }
  Token qualified(bool AllowBuiltin = false, Node *Application = nullptr,
                  std::string *NominalSchema = nullptr,
                  ReceiverType *Receiver = nullptr,
                  std::string *QualifiedMember = nullptr) {
    bool Root = eat("::");
    auto T = Application && is("operator")          ? operatorName()
             : AllowBuiltin && builtin(peek().Text) ? take()
                                                    : name();
    auto AliasSchema = [&](const std::string &S) {
      auto Head = StringRef(S).split("::").first.str();
      if (!Root && (HiddenTypes.count(Head) || TypeParameters.count(Head)))
        return S;
      if (auto I = AliasSchemas.find(Root ? "::" + S : S);
          I != AliasSchemas.end() && !I->second.empty())
        return StringRef(I->second).ltrim(':').str();
      return S;
    };
    std::string Schema = T.Text;
    while (true) {
      const bool Unqualified =
          Application && !Root && !StringRef(Schema).contains("::");
      const bool Shadowed = Unqualified && (HiddenTypes.count(Schema) ||
                                            ValueReceivers.count(Schema));
      auto MemberSchema = Unqualified
                              ? indexedMember(CurrentReceiver.Owner, Schema)
                              : std::string();
      bool MemberBinding = !MemberSchema.empty() && !Types.count(Schema);
      if (Application && StringRef(Schema).contains("::")) {
        auto [Owner, Member] = StringRef(Schema).rsplit("::");
        if (auto I = NominalReceivers.find((Root ? "::" : "") + Owner.str());
            I != NominalReceivers.end() && !I->second.Owner.empty() &&
            !SpecializedReceivers.count(I->second.Owner)) {
          MemberSchema = indexedMember(I->second.Owner, Member);
          MemberBinding = Families.count(MemberSchema);
        }
      }
      const auto &ArgumentSchema = MemberBinding ? MemberSchema : Schema;
      const bool HasFamilySchema = !Shadowed && Families.count(ArgumentSchema);
      const bool UnresolvedIndexType =
          IndexingMembers && AllowBuiltin && !Application && !HasFamilySchema;
      std::optional<bool> BitArgumentsAreTypes;
      if (Application && is("<") && (Root || !HiddenTypes.count(T.Text)) &&
          bitExtractionName(T.Text))
        if (auto Arity = bitExtractionArity())
          BitArgumentsAreTypes = *Arity == 1;
      const bool NumericApplication =
          BitArgumentsAreTypes.has_value() ||
          (Application && is("<") &&
           (integerLibraryName(T.Text, true) || floatingSpecialName(T.Text)) &&
           !bitExtractionName(T.Text) &&
           (StringRef(T.Text).contains("::") ||
            ((Root || !HiddenTypes.count(T.Text)) &&
             (known(peek(1).Text) || peek(1).Text == "::" ||
              peek(2).Text == "::"))));
      if (is("<") &&
          (HasFamilySchema || UnresolvedIndexType || NumericApplication ||
           (Application &&
            (builtinPredicate(T.Text) || T.Text == "construct_at" ||
             T.Text == "destroy_base" || T.Text == "abandon_base" ||
             T.Text == "transfer_destruction" || T.Text == "std::forward")))) {
        auto Start = Pos;
        std::string Canonical;
        std::vector<Node> Args;
        if (T.Text == "destroy_base" || T.Text == "abandon_base") {
          expect("<");
          Args.push_back(baseSelector());
          closeAngle();
        } else if (UnresolvedIndexType ||
                   (Application &&
                    ConflictingCallableSchemas.count(ArgumentSchema)))
          Args = deferredTemplateArgs();
        else
          Args = templateArgs(ArgumentSchema, &Canonical, BitArgumentsAreTypes);
        if (!Application || is("::") || Types.count(ArgumentSchema))
          T.Text += Canonical.empty() ? spelling(Start) : Canonical;
        else {
          Application->ExplicitApplication = true;
          Application->TemplateArgs = std::move(Args);
        }
      }
      if (!eat("::")) {
        if (QualifiedMember && !Unqualified)
          *QualifiedMember = std::move(MemberSchema);
        break;
      }
      Schema = AliasSchema(Schema);
      auto Next = Application && is("operator")      ? operatorName()
                  : is("forward") && T.Text == "std" ? take()
                                                     : name();
      T.Text += "::" + Next.Text;
      Schema += "::" + Next.Text;
    }
    if (NominalSchema)
      *NominalSchema = (Root ? "::" : "") + AliasSchema(Schema);
    if (Receiver) {
      if (!Root &&
          TypeParameters.count(StringRef(Schema).split("::").first.str())) {
        Receiver->Dependent = true;
        if (TypeParameters.count(Schema))
          Receiver->TypeParameter = Schema;
      } else if (auto I = NominalReceivers.find((Root ? "::" : "") + Schema);
                 I != NominalReceivers.end()) {
        if (SpecializedReceivers.count(I->second.Owner))
          Receiver->Dependent = true;
        else
          *Receiver = I->second;
      } else if (builtin(Schema) &&
                 (!Application || !HiddenTypes.count(Schema)))
        *Receiver = scalarReceiver(Schema);
      if (Application && !Root && ValueReceivers.count(Schema))
        *Receiver = {};
      if (StringRef(T.Text).contains('<'))
        Receiver->ExactNominal = false;
    }
    if (Root)
      T.Text = "::" + T.Text;
    return T;
  }
  bool known(StringRef S) const {
    bool Root = S.consume_front("::");
    if (!Root && HiddenTypes.count(S.str()))
      return false;
    return builtin(S) || Types.count(S.split('<').first.str()) ||
           (!Root && S.contains("::") &&
            TypeParameters.count(S.split("::").first.str())) ||
           S == "const" || S == "function" || S == "decltype";
  }
  std::string spelling(size_t Start) const {
    std::string S;
    for (size_t I = Start; I < Pos; ++I)
      S += (*Tokens)[I].Text;
    return S;
  }
  std::vector<Token> &editableTokens() {
    if (!Tokens.unique())
      Tokens = std::make_shared<std::vector<Token>>(*Tokens);
    return *Tokens;
  }
  void closeAngle() {
    if (is(">>")) {
      auto &Editable = editableTokens();
      Editable[Pos].Text = ">";
      auto Second = Editable[Pos++];
      ++Second.Column;
      Editable.insert(Editable.begin() + Pos, std::move(Second));
    } else
      expect(">");
  }
  Node typeArgument() {
    Node A(Node::TypeArg, peek());
    if (!A.At.Text.empty() && llvm::isDigit(A.At.Text.front()))
      fail(A.At, "expected a type argument");
    ReceiverType Shape;
    A.Type = type(nullptr, &Shape);
    TypeArguments[sourceSite(A.At)] = std::move(Shape);
    return A;
  }
  std::vector<Node> templateArgs(const std::string &Name,
                                 std::string *Canonical = nullptr,
                                 std::optional<bool> ArgumentIsType = {}) {
    expect("<");
    if (Canonical)
      *Canonical = "<";
    std::vector<Node> Out;
    if (is(">") || is(">>")) {
      closeAngle();
      if (Canonical)
        *Canonical += ">";
      return Out;
    }
    do {
      size_t I = Out.size(), Begin = Pos;
      auto It = Families.find(Name);
      bool T = It != Families.end() && !It->second.empty()
                   ? It->second[std::min(I, It->second.size() - 1)].K ==
                         Node::TypeParam
                   : ArgumentIsType.value_or(integerLibraryName(Name, true) ||
                                             floatingSpecialName(Name) ||
                                             known(peek().Text));
      if (T)
        Out.push_back(typeArgument());
      else {
        if (is("const") && peek(1).Text == "<")
          fail(peek(), "expected a constant argument");
        Out.push_back(expr(1, true));
      }
      if (Canonical) {
        if (I)
          *Canonical += ",";
        if (T)
          *Canonical += Out.back().Type;
        else {
          const auto &Argument = Out.back();
          auto Text = spelling(Begin);
          if (!Argument.Grouped &&
              (Argument.K == Node::Binary || Argument.K == Node::Conditional))
            Text = "(" + Text + ")";
          *Canonical += Text;
        }
      }
      Out.back().Pack = eat("...");
      if (Canonical && Out.back().Pack)
        *Canonical += "...";
    } while (eat(","));
    closeAngle();
    if (Canonical)
      *Canonical += ">";
    return Out;
  }
  bool possibleMemberApplication() const {
    unsigned Group = 0;
    for (size_t I = 1;; ++I) {
      const auto &Word = peek(I).Text;
      if (Word.empty())
        return false;
      if (Word == "(" || Word == "[" || Word == "{")
        ++Group;
      else if (Word == ")" || Word == "]" || Word == "}") {
        if (!Group)
          return false;
        --Group;
      } else if (!Group) {
        if (Word == ";")
          return false;
        if ((Word == ">" || Word == ">>") && peek(I + 1).Text == "(")
          return true;
      }
    }
  }
  bool argumentDelimiter() const {
    return is(",") || is("...") || is(">") || is(">>");
  }
  Node deferredTemplateArgument() {
    auto At = peek();
    Parser TypeParse(*this);
    std::optional<Node> Type, Value;
    try {
      auto Candidate = TypeParse.typeArgument();
      if (TypeParse.argumentDelimiter())
        Type = std::move(Candidate);
    } catch (const Diagnostic &) {
      // The selected parameter can still admit a constant expression.
    }
    try {
      auto Candidate = expr(1, true);
      if (argumentDelimiter())
        Value = std::move(Candidate);
    } catch (const Diagnostic &) {
      // Type-only tokens may be valid for the selected parameter.
    }
    if (!Value) {
      if (!Type)
        fail(At, "expected a generic type or constant argument");
      *this = std::move(TypeParse);
      return std::move(*Type);
    }
    if (!Type)
      return std::move(*Value);
    const auto &TypeEnd = TypeParse.peek();
    if (std::tie(TypeEnd.Line, TypeEnd.Column) !=
        std::tie(peek().Line, peek().Column))
      fail(At, "ambiguous generic argument boundary");
    TypeQueries.merge(TypeParse.TypeQueries);
    TypeArguments.merge(TypeParse.TypeArguments);
    Node Both(Node::GenericArgument, At);
    Both.Children.push_back(std::move(*Type));
    Both.Children.push_back(std::move(*Value));
    return Both;
  }
  std::vector<Node> deferredTemplateArgs() {
    std::vector<Node> Arguments;
    expect("<");
    if (!is(">") && !is(">>")) {
      do {
        auto Argument = deferredTemplateArgument();
        Argument.Pack = eat("...");
        Arguments.push_back(std::move(Argument));
      } while (eat(","));
    }
    closeAngle();
    return Arguments;
  }
  std::optional<std::vector<Node>> deferredMemberApplication() {
    if (!possibleMemberApplication())
      return std::nullopt;
    Parser Probe(*this);
    std::vector<Node> Arguments;
    try {
      Arguments = Probe.deferredTemplateArgs();
    } catch (const Diagnostic &) {
      // A relational expression can have the same leading tokens.
      return std::nullopt;
    }
    if (!Probe.is("("))
      return std::nullopt;
    *this = std::move(Probe);
    return Arguments;
  }
  std::string type(std::string *NominalSchema = nullptr,
                   ReceiverType *Receiver = nullptr) {
    Nest Guard(Depth, peek());
    auto T = peek();
    std::string S;
    if (eat("(")) {
      S = type(NominalSchema, Receiver);
      expect(")");
    } else if (eat("decltype")) {
      expect("(");
      Node Query(Node::TypeQuery, T);
      Query.Children.push_back(expr());
      if (Receiver)
        *Receiver = receiverType(Query.Children.front());
      expect(")");
      S = "$decltype." + std::to_string(T.Line) + "." +
          std::to_string(T.Column);
      Query.Text = S;
      TypeQueries[S] = std::move(Query);
    } else if (eat("const")) {
      expect("<");
      S = "const<" + type(nullptr, Receiver) + ">";
      if (Receiver)
        Receiver->Readonly = true;
      closeAngle();
    } else if (eat("function")) {
      expect("<");
      ReceiverType Result;
      auto Return = type(nullptr, Receiver ? &Result : nullptr);
      if (Receiver && Result.known())
        Receiver->CallableResult =
            std::make_shared<const ReceiverType>(std::move(Result));
      S = "function<" + Return + "(";
      auto Parameters = params();
      std::map<std::string, unsigned> Named;
      for (size_t I = 0; I < Parameters.size(); ++I) {
        const auto &P = Parameters[I];
        if (!P.Children.empty())
          fail(P.At, "callable type cannot contain a parameter default");
        if (StringRef(P.Type).starts_with("forward "))
          fail(P.At, "forward requires a generic function declaration");
        if (!P.Text.empty() && !Named.emplace(P.Text, I).second)
          fail(P.At, "duplicate parameter in callable type");
        if (I)
          S += ",";
        S += P.Type;
        if (P.Pack)
          S += "...";
      }
      S += ")";
      bool Noexcept = eat("noexcept");
      if (Noexcept)
        S += " noexcept";
      std::set<unsigned> NoEscape, Borrowed, Consumes;
      auto Attrs = attributes();
      if (!Attrs.Contracts.empty())
        fail(T, "value predicates require an owning declaration");
      EffectBound Effects;
      for (const auto &[Key, Value] : Attrs) {
        if (Key == "effects") {
          Effects = bindEffectNames(Value, Parameters, false, T);
          if (Effects->count("throw") && Noexcept)
            fail(T, "noexcept contradicts a throw effect");
          continue;
        }
        if (Key == "lifecycle_effect") {
          S += " whole";
          continue;
        }
        if (Key != "noescape" && Key != "returns_borrowed_from" &&
            Key != "consumes")
          fail(T, "invalid callable type attribute");
        llvm::SmallVector<StringRef> List;
        StringRef(Value).split(List, ',');
        auto &Positions = Key == "consumes"   ? Consumes
                          : Key == "noescape" ? NoEscape
                                              : Borrowed;
        for (auto Name : List) {
          auto It = Named.find(Name.str());
          if (It == Named.end())
            fail(T, "unknown borrow-contract parameter");
          Positions.insert(It->second);
        }
      }
      S +=
          parameterEffects(NoEscape, Borrowed, Consumes) + effectFlags(Effects);
      closeAngle();
      S += ">";
    } else {
      if (!is("::") && !identifier(peek().Text))
        fail(T, "unsupported or unknown type '" + T.Text + "'");
      S = qualified(true, nullptr, NominalSchema, Receiver).Text;
      if (!IndexingMembers && !known(S) &&
          !(StringRef(S).contains("::") &&
            known(StringRef(S).split("::").first)))
        fail(T, "unsupported or unknown type '" + S + "'");
    }
    for (;;) {
      if (is("*") || is("&") || is("&&")) {
        auto Suffix = take().Text;
        S += Suffix;
        if (Receiver) {
          if (Suffix == "*" && Receiver->known()) {
            Receiver->PointeeScalar =
                Receiver->Layers.empty() ? Receiver->Scalar : std::string{};
            if (Receiver->Layers.empty() && !Receiver->QualificationUnknown)
              Receiver->PointeeReadonly = Receiver->Readonly;
            else
              Receiver->PointeeReadonly.reset();
            Receiver->Layers += '*';
            Receiver->Scalar.clear();
            Receiver->Readonly = false;
            Receiver->Reference = ReferenceKind::None;
          } else if (Suffix != "*") {
            Receiver->Reference = referenceKind(Suffix);
          }
        }
        if (NominalSchema)
          NominalSchema->clear();
      } else if (eat("[")) {
        size_t Begin = Pos;
        expr();
        S += "[" + spelling(Begin) + "]";
        expect("]");
        if (Receiver && Receiver->known()) {
          Receiver->Layers += '[';
          Receiver->Scalar.clear();
        }
        if (NominalSchema)
          NominalSchema->clear();
      } else
        break;
    }
    return S;
  }
  std::vector<Node> args() {
    expect("(");
    std::vector<Node> V;
    if (!eat(")")) {
      do {
        V.push_back(expr());
        V.back().Pack = eat("...");
      } while (eat(","));
      expect(")");
    }
    return V;
  }
  Node expr(int Min = 1, bool InAngle = false) {
    Nest Guard(Depth, peek());
    auto T = peek();
    Node N;
    if (eat("(")) {
      N = expr();
      expect(")");
      N.Grouped = true;
    } else if (is("+") || is("-") || is("!") || is("~") || is("&") || is("*") ||
               is("++") || is("--")) {
      N = Node(Node::Unary, take());
      N.Children.push_back(expr(13, InAngle));
    } else if (eat("[")) {
      N = Node(Node::Lambda, T);
      std::set<std::string> Captures;
      Receivers CaptureTypes;
      if (!eat("]")) {
        do {
          bool Borrow = eat("&");
          Token Id = is("this") ? take() : name();
          Node Capture(Node::Capture, Id);
          Capture.Type = Borrow              ? "borrow"
                         : Id.Text == "this" ? "this"
                                             : "copy";
          if (Id.Text == "this" && Borrow)
            fail(Id, "this captures its pointer");
          if (is("(")) {
            if (Borrow || Id.Text == "this")
              fail(Id, "invalid initializer capture");
            Capture.Type = "initializer";
            Capture.Children = {condition()};
          }
          if (!Captures.insert(Id.Text).second)
            fail(Id, "duplicate closure capture");
          if (Capture.Type != "this")
            CaptureTypes[Id.Text] = Capture.Type == "initializer"
                                        ? receiverType(Capture.Children.front())
                                        : receiverType(Node(Node::Name, Id));
          N.TemplateArgs.push_back(std::move(Capture));
        } while (eat(","));
        expect("]");
      }
      if (eat("async"))
        fail(T, "async closures require asynchronous execution");
      N.Type = type();
      llvm::SaveAndRestore ReceiverBindings(ValueReceivers);
      N.Params = params(true);
      N.Const = !eat("mutable");
      for (const auto &Capture : N.TemplateArgs) {
        if (Capture.Type == "this" ||
            llvm::any_of(N.Params,
                         [&](const Node &P) { return P.Text == Capture.Text; }))
          continue;
        auto Type = CaptureTypes.at(Capture.Text);
        if (Capture.Type != "borrow") {
          Type.Readonly = N.Const;
          Type.QualificationUnknown = false;
        }
        ValueReceivers[Capture.Text] = std::move(Type);
      }
      llvm::SaveAndRestore InstanceScope(ReceiverAvailable, false);
      N.Noexcept = eat("noexcept");
      applyAttributes(N, attributes());
      N.Children = {block()};
    } else if (eat("configured")) {
      N = Node(Node::Configured, T);
      N.Settings = settings(false);
      llvm::SaveAndRestore ScopedPolicy(PolicyContext);
      PolicyContext.push_back(sourceSite(T));
      expect("(");
      N.Children.push_back(expr());
      expect(")");
    } else if (is("sizeof") || is("alignof")) {
      N = Node(Node::Unary, take());
      expect("(");
      if (typeBefore(false)) {
        Node Ty(Node::TypeArg, peek());
        Ty.Type = type();
        N.Children.push_back(Ty);
      } else {
        if (N.Text == "alignof")
          fail(T, "alignof requires a type");
        N.Children.push_back(expr());
      }
      expect(")");
    } else if (!T.Text.empty() && llvm::isDigit(T.Text[0]))
      N = Node(realToken(T.Text) ? Node::Real : Node::Number, take());
    else if (!T.Text.empty() && (T.Text[0] == '\'' || T.Text[0] == '"'))
      N = Node(T.Text[0] == '\'' ? Node::Character : Node::String, take());
    else if (is("true") || is("false") || is("nullptr") || is("this"))
      N = Node(Node::Name, take());
    else if (identifier(T.Text) || is("::")) {
      if (Reserved.count(T.Text) && T.Text != "operator")
        fail(T, "expected expression");
      N.K = Node::Name;
      ReceiverType Nominal;
      std::string QualifiedMember;
      N.At = qualified(true, &N, nullptr, &Nominal, &QualifiedMember);
      N.Text = N.At.Text;
      if (Nominal.known())
        NominalExpressions[{N.At.Line, N.At.Column}] = std::move(Nominal);
      if (!QualifiedMember.empty())
        QualifiedMemberExpressions[{N.At.Line, N.At.Column}] =
            std::move(QualifiedMember);
    } else
      fail(T, "expected expression");
    for (;;) {
      if (is("(")) {
        Node C(Node::Call, N.At);
        C.Children.push_back(std::move(N));
        auto A = args();
        C.Children.insert(C.Children.end(), A.begin(), A.end());
        N = std::move(C);
      } else if (eat("[")) {
        Node M(Node::Index, T);
        M.Children = {std::move(N), expr()};
        expect("]");
        N = std::move(M);
      } else if (is(".") || is("->")) {
        bool Ptr = take().Text == "->";
        auto Id = is("operator") ? operatorName() : name();
        if (eat("::")) {
          expect("~");
          expect(Id.Text);
          expect("(");
          expect(")");
          Node F(Node::Name, Id);
          F.At.Text = F.Text = "destroy_base";
          Node Ty(Node::TypeArg, Id);
          Ty.Type = Id.Text;
          F.TemplateArgs = {Ty};
          Node C(Node::Call, Id);
          C.Children = {F, std::move(N)};
          N = std::move(C);
        } else {
          Node M(Node::Member, Id);
          if (is("<") && (!BoundRelationalMembers ||
                          !BoundRelationalMembers->count(sourceSite(Id)))) {
            auto Base = receiverType(N);
            auto Schema = memberFamily(Base, Id, Ptr);
            if (Schema && Schema->Generic) {
              M.TemplateArgs = Schema->Deferred ? deferredTemplateArgs()
                                                : templateArgs(Schema->Key);
              M.ExplicitApplication = true;
            } else if (!Schema && (Families.count(Id.Text) || Base.Dependent)) {
              if (auto Arguments = deferredMemberApplication()) {
                M.TemplateArgs = std::move(*Arguments);
                M.ExplicitApplication = true;
                if (canConfirmMember(N))
                  M.Settings["$confirm_member_family"] = "";
              }
            }
          }
          M.Children.push_back(std::move(N));
          M.Definition = Ptr;
          N = std::move(M);
        }
      } else if (is("++") || is("--")) {
        Node Op(Node::Unary, take());
        Op.Definition = true;
        Op.Children.push_back(std::move(N));
        N = std::move(Op);
      } else
        break;
    }
    for (;;) {
      if (InAngle && (is(">") || is(">>")))
        break;
      int P = precedence(peek().Text);
      if (P < Min)
        break;
      auto Operator = take();
      Node Op(Operator.Text == "?" ? Node::Conditional : Node::Binary,
              Operator);
      Op.Children.push_back(std::move(N));
      if (Op.K == Node::Conditional) {
        Op.Children.push_back(expr());
        expect(":");
        Op.Children.push_back(expr(1, InAngle));
      } else
        Op.Children.push_back(expr(P == 1 ? P : P + 1, InAngle));
      N = std::move(Op);
    }
    return N;
  }
  std::string metadataValue() {
    Nest Guard(Depth, peek());
    auto T = take();
    if (T.Text == "[") {
      std::string List = "[";
      if (!eat("]")) {
        do {
          if (List.size() > 1)
            List += ",";
          List += metadataValue();
        } while (eat(","));
        expect("]");
      }
      return List + "]";
    }
    if (identifier(T.Text) || T.Text.front() == '"')
      return T.Text;
    if (llvm::isDigit(T.Text.front()) && !realToken(T.Text))
      return llvm::toString(integerLiteral(T), 10, false);
    fail(T, "CFG001: expected configuration value");
  }
  std::map<std::string, std::string> settings(bool File) {
    expect(File ? "{" : "(");
    std::map<std::string, std::string> M;
    if (File && eat("}"))
      return M;
    do {
      auto K = take();
      if (!identifier(K.Text))
        fail(K, "CFG001: expected configuration key");
      while (eat(".")) {
        auto Part = take();
        if (!identifier(Part.Text))
          fail(Part, "CFG001: expected a configuration key component");
        K.Text += "." + Part.Text;
      }
      expect("=");
      if (!M.emplace(K.Text, metadataValue()).second)
        fail(K, "CFG001: duplicate configuration key");
      if (File)
        expect(";");
    } while (File ? !is("}") : eat(","));
    expect(File ? "}" : ")");
    return M;
  }
  void skipBalanced(StringRef Open, StringRef Close) {
    expect(Open);
    unsigned Groups = 1;
    do {
      const auto Word = take().Text;
      Groups += (Word == Open) - (Word == Close);
    } while (Groups);
  }
  Node declarationBody(bool Construction = false) {
    if (!IndexingMembers)
      return block(Construction);
    Node Body(Node::Block, peek());
    skipBalanced("{", "}");
    return Body;
  }
  Node block(bool Construction = false) {
    Nest Guard(Depth, peek());
    auto OuterTypes = Types;
    auto OuterHidden = HiddenTypes;
    llvm::SaveAndRestore LocalSchemas(AliasSchemas);
    llvm::SaveAndRestore LocalTypes(NominalReceivers);
    llvm::SaveAndRestore LocalValues(ValueReceivers);
    Node B(Node::Block, expect("{"));
    while (!eat("}")) {
      if (Construction && eat("init")) {
        Node I(Node::Init, name());
        if ((I.Text == "base" || I.Text == "virtual_base") && eat("<")) {
          I.Text += "/" + type();
          closeAngle();
        }
        I.Children = args();
        expect(";");
        B.Children.push_back(std::move(I));
      } else
        B.Children.push_back(statement());
    }
    Types = std::move(OuterTypes);
    HiddenTypes = std::move(OuterHidden);
    return B;
  }
  Node object(Token T, std::string Ty, bool RO, bool CX) {
    Node O(Node::Object, T);
    O.Type = std::move(Ty);
    O.Const = RO || CX;
    O.Required = CX;
    O.HasInitializer = is("(");
    if (O.HasInitializer) {
      if (IndexingMembers)
        skipBalanced("(", ")");
      else
        O.Children = args();
    }
    if (!IndexingMembers && O.Type == "auto" && O.Children.size() != 1)
      fail(T, "auto requires a single initializer");
    if (eat("->")) {
      O.HasInitializer = true;
      if (O.Type == "auto")
        fail(T, "a construction tail requires a typed declaration");
      auto B = declarationBody(true);
      B.K = Node::Tail;
      O.Children.push_back(std::move(B));
    }
    expect(";");
    return O;
  }
  // A parenthesized type and a grouped expression share a prefix. Commit to
  // the type production only when its complete declarator or delimiter follows.
  bool typeBefore(bool Declarator) {
    size_t Start = 0;
    while (peek(Start).Text == "(")
      ++Start;
    bool Root = peek(Start).Text == "::";
    if (Root)
      ++Start;
    std::string S = Root ? "::" + peek(Start).Text : peek(Start).Text;
    for (size_t I = Start + 1; peek(I).Text == "::"; I += 2)
      S += "::" + peek(I + 1).Text;
    if (!known(S) && !(Declarator && StringRef(S).contains("::") &&
                       known(StringRef(S).split("::").first)))
      return false;
    auto Saved = Pos;
    bool Match = false;
    try {
      type();
      Match = Declarator
                  ? identifier(peek().Text) && !Reserved.count(peek().Text)
                  : is(")");
    } catch (const Diagnostic &) {
      // The expression production supplies the diagnostic if neither fits.
    }
    Pos = Saved;
    return Match;
  }
  Node simple() {
    if (is("[") && peek(1).Text == "[") {
      auto Attrs = attributes();
      if (!is("static") && !is("thread_local"))
        fail(peek(), "block static attributes require a storage modifier");
      auto N = simple();
      applyAttributes(N, Attrs);
      return N;
    }
    if (is("static") || is("thread_local")) {
      auto Storage = take();
      if (is("static") || is("thread_local"))
        fail(peek(), "duplicate storage modifier");
      if (is("[") && peek(1).Text == "[")
        fail(peek(), "static attributes must precede the storage modifier");
      auto N = simple();
      if (N.K != Node::Object)
        fail(Storage, "storage modifier requires an object declaration");
      N.Settings["storage"] = Storage.Text;
      return N;
    }
    if (is(";"))
      return Node(Node::Empty, take());
    bool RO = is("const") && peek(1).Text != "<";
    if (RO)
      take();
    bool CX = !RO && eat("constexpr");
    if (RO || CX || is("auto") || typeBefore(true)) {
      ReceiverType Receiver;
      auto Ty = eat("auto") ? std::string("auto") : type(nullptr, &Receiver);
      auto Id = name();
      Receiver.Readonly |= RO || CX;
      ValueReceivers[Id.Text] = std::move(Receiver);
      if (Types.count(Id.Text) || integerLibraryName(Id.Text, true))
        HiddenTypes.insert(Id.Text);
      auto O = object(Id, Ty, RO, CX);
      if (Ty == "auto" && O.Children.size() == 1) {
        auto Deduced = receiverType(O.Children.front());
        Deduced.Readonly = RO || CX;
        Deduced.QualificationUnknown = false;
        ValueReceivers[Id.Text] = std::move(Deduced);
      }
      return O;
    }
    Node S(Node::Expression, peek());
    S.Children.push_back(expr());
    expect(";");
    return S;
  }
  Node condition() {
    expect("(");
    auto E = expr();
    expect(")");
    return E;
  }
  Node statement() {
    Nest Guard(Depth, peek());
    auto T = peek();
    if (is("{"))
      return block();
    if (is("alias") || is("struct") || is("class") || is("union") ||
        is("enum") ||
        (is("declare") &&
         (peek(1).Text == "struct" || peek(1).Text == "class" ||
          peek(1).Text == "union" || peek(1).Text == "enum")))
      return declaration();
    if (eat("if")) {
      Node N(Node::If, T);
      N.Required = eat("constexpr");
      N.Children = {condition()};
      auto Branch = [&](bool Else) {
        DefinitionDomain Facts{{Namespace, {}, {}, T}, CurrentDomain};
        llvm::SaveAndRestore DomainScope(CurrentDomain);
        if (N.Required && CurrentDomain) {
          auto Test = N.Children.front();
          if (Else) {
            Node Negated(Node::Unary, T);
            Negated.Text = "!";
            Negated.Children.push_back(std::move(Test));
            Test = std::move(Negated);
          }
          Facts.Site.Conditions.push_back(std::move(Test));
          Facts.Site.RecordScope = !CurrentReceiver.Owner.empty();
          Facts.Site.Policy = PolicyContext;
          for (const auto &[Name, Binding] : ValueReceivers)
            Facts.Site.ShadowedValues.insert(Name);
          CurrentDomain = &Facts;
        }
        return Else && is("if") ? statement() : block();
      };
      N.Children.push_back(Branch(false));
      if (eat("else"))
        N.Children.push_back(Branch(true));
      return N;
    }
    if (eat("while")) {
      Node N(Node::While, T);
      N.Children = {condition(), block()};
      return N;
    }
    if (eat("do")) {
      Node N(Node::Do, T);
      N.Children.push_back(block());
      expect("while");
      N.Children.push_back(condition());
      expect(";");
      return N;
    }
    if (eat("for")) {
      llvm::SaveAndRestore LoopValues(ValueReceivers);
      auto OuterTypes = Types;
      auto OuterHidden = HiddenTypes;
      Node N(Node::For, T);
      expect("(");
      N.Children = {simple(), is(";") ? Node() : expr()};
      expect(";");
      N.Children.push_back(is(")") ? Node() : expr());
      expect(")");
      N.Children.push_back(block());
      Types = std::move(OuterTypes);
      HiddenTypes = std::move(OuterHidden);
      return N;
    }
    if (eat("match")) {
      Node N(Node::Match, T);
      N.Children = {condition()};
      expect("{");
      while (!eat("}")) {
        expect("case");
        Node Arm(Node::Arm, qualified());
        if (Arm.Text != "_" && eat("(")) {
          if (!eat(")")) {
            do {
              Node P(Node::Parameter, take());
              P.Type = P.Text;
              if (P.Type != "_") {
                if (P.Type != "ref" && P.Type != "move" && P.Type != "value")
                  fail(P.At, "invalid payload pattern");
                P.Text = name().Text;
              }
              Arm.Params.push_back(P);
            } while (eat(","));
            expect(")");
          }
        }
        llvm::SaveAndRestore ArmValues(ValueReceivers);
        for (const auto &P : Arm.Params)
          ValueReceivers[P.Text] = {};
        Arm.Children = {block()};
        N.Children.push_back(Arm);
      }
      return N;
    }
    if (eat("switch")) {
      Node N(Node::Switch, T);
      N.Children.push_back(condition());
      expect("{");
      while (!eat("}")) {
        Node A(Node::Arm, peek());
        if (eat("case"))
          A.Children.push_back(expr());
        else
          expect("default");
        expect(":");
        A.Children.push_back(block());
        N.Children.push_back(std::move(A));
      }
      return N;
    }
    if (eat("return")) {
      Node N(Node::Return, T);
      if (!is(";"))
        N.Children.push_back(expr());
      expect(";");
      return N;
    }
    if (eat("break") || eat("continue") || eat("goto") || eat("fallthrough")) {
      Node N(T.Text == "break"      ? Node::Break
             : T.Text == "continue" ? Node::Continue
             : T.Text == "goto"     ? Node::Goto
                                    : Node::Fallthrough,
             T);
      N.Text.clear();
      if (N.K == Node::Goto || (N.K != Node::Fallthrough && !is(";")))
        N.Text = name().Text;
      expect(";");
      return N;
    }
    if (is("configured")) {
      auto Start = Pos;
      take();
      Node N(Node::Configured, T);
      N.Settings = settings(false);
      if (is("(")) {
        Pos = Start;
        return simple();
      }
      llvm::SaveAndRestore ScopedPolicy(PolicyContext);
      PolicyContext.push_back(sourceSite(T));
      if (is("{"))
        N.Children = {block()};
      else {
        auto D = is("alias") ? declaration() : simple();
        if (D.K != Node::Object && D.K != Node::Alias)
          fail(D.At, "expected configured declaration, block or parenthesized "
                     "expression");
        N.Children = {std::move(D)};
      }
      return N;
    }
    if (eat("delegate")) {
      Node N(Node::Delegate, T);
      N.Children = args();
      expect(";");
      return N;
    }
    if (identifier(T.Text) && peek(1).Text == ":") {
      auto L = name();
      expect(":");
      Node N(Node::Label, L);
      N.Children = {statement()};
      if (N.Children[0].K == Node::Object || N.Children[0].K == Node::Alias)
        fail(L, "a label requires a statement");
      return N;
    }
    return simple();
  }
  std::vector<Node> params(bool BindReceivers = false) {
    expect("(");
    std::vector<Node> V;
    if (eat(")"))
      return V;
    do {
      Node P(Node::Parameter, peek());
      P.Const = is("const") && peek(1).Text != "<";
      if (P.Const)
        take();
      bool Forward = eat("forward");
      ReceiverType Receiver;
      P.Type = type(nullptr, BindReceivers ? &Receiver : nullptr);
      if (Forward)
        P.Type = "forward " + P.Type;
      if (P.Const && P.Type.back() == '&') {
        auto I = P.Type.find_last_not_of('&') + 1;
        P.Type = "const<" + P.Type.substr(0, I) + ">" + P.Type.substr(I);
      }
      if (P.Type == "void")
        fail(P.At, "void parameter is invalid; use ()");
      P.Pack = eat("...");
      P.Text = "";
      if (identifier(peek().Text)) {
        P.At = name();
        P.Text = P.At.Text;
      }
      if (is("(")) {
        if (IndexingMembers) {
          if (peek(1).Text != ")")
            P.Children.emplace_back(Node::Empty, peek(1));
          skipBalanced("(", ")");
        } else
          P.Children = args();
      }
      if (BindReceivers) {
        Receiver.Readonly |= P.Const;
        ParameterTypes[{P.At.Line, P.At.Column}] = Receiver;
        if (!P.Text.empty())
          ValueReceivers[P.Text] = std::move(Receiver);
      }
      V.push_back(std::move(P));
    } while (eat(","));
    expect(")");
    return V;
  }
  bool functionBody() const {
    if (!is("("))
      return false;
    size_t I = 0;
    int Depth = 0;
    do {
      auto S = peek(I++).Text;
      if (S.empty())
        return false;
      Depth += (S == "(") - (S == ")");
    } while (Depth);
    while (peek(I).Text == "const" || peek(I).Text == "noexcept" ||
           peek(I).Text == "override" || peek(I).Text == "final" ||
           peek(I).Text == "&" || peek(I).Text == "&&")
      ++I;
    while (peek(I).Text == "[" && peek(I + 1).Text == "[") {
      I += 2;
      unsigned Brackets = 2;
      do {
        const auto &Text = peek(I++).Text;
        if (Text.empty())
          return false;
        Brackets += (Text == "[") - (Text == "]");
      } while (Brackets);
    }
    if (peek(I).Text == "override")
      ++I;
    if (peek(I).Text == "final")
      ++I;
    return peek(I).Text == "{" || peek(I).Text == "=";
  }
  std::vector<Node> generic() {
    std::vector<Node> G;
    std::set<std::string> Names;
    expect("<");
    do {
      auto T = peek();
      Node P(Node::TypeParam, T);
      ReceiverType ValueType;
      if (!eat("type")) {
        expect("const");
        P.K = Node::ValueParam;
        P.Type = type(nullptr, &ValueType);
      }
      P.Pack = eat("...");
      P.At = name();
      P.Text = P.At.Text;
      if (!Names.insert(P.Text).second)
        fail(P.At, "duplicate generic parameter");
      if (P.K == Node::TypeParam) {
        Types.insert(P.Text);
        TypeParameters.insert(P.Text);
      } else
        ParameterTypes[sourceSite(P.At)] = std::move(ValueType);
      if (eat("=")) {
        if (P.K == Node::TypeParam) {
          Node A(Node::TypeArg, peek());
          A.Type = type();
          P.Children = {A};
        } else
          P.Children = {expr(1, true)};
      }
      if (P.Pack && !P.Children.empty())
        fail(P.At, "a generic pack cannot have a default");
      if (P.Pack && is(","))
        fail(P.At, "generic pack must be the last parameter");
      G.push_back(P);
    } while (eat(","));
    closeAngle();
    return G;
  }
  std::string definitionControl() {
    if (!is("default") && !is("delete"))
      fail(peek(), "expected default or delete");
    auto Control = take().Text;
    expect(";");
    return Control;
  }
  // A special member has no return type. Its qualified name is followed
  // immediately by the parameter list, unlike a function's result type.
  bool separateSpecial() {
    auto Start = Pos;
    if (!is("::") && (!identifier(peek().Text) ||
                      (peek(1).Text != "::" && peek(1).Text != "<")))
      return false;
    llvm::SaveAndRestore Position(Pos, Start);
    try {
      std::string Q;
      bool Drop = false;
      declarationName(Q, Drop);
      return !Q.empty() && is("(");
    } catch (const Diagnostic &) {
      return false;
    }
  }
  Token declarationName(std::string &Qualifier, bool &Dtor,
                        std::vector<Node> *Owners = nullptr) {
    bool Root = eat("::");
    auto Id = is("operator") ? operatorName() : name();
    std::string Schema = Id.Text;
    for (;;) {
      auto Component = Id.Text;
      Node Owner(Node::Name, Id);
      if (is("<") && Families.count(Schema)) {
        std::string Args;
        Owner.TemplateArgs = templateArgs(Schema, &Args);
        Owner.ExplicitApplication = true;
        Component += Args;
        if (!is("::"))
          fail(peek(),
               "an applied declaration qualifier must name an owning scope");
      }
      if (!eat("::"))
        break;
      if (Owners)
        Owners->push_back(std::move(Owner));
      Qualifier += Component + "::";
      Dtor = eat("~");
      Id = !Dtor && is("operator") ? operatorName() : name();
      Schema += "::" + Id.Text;
      if (Dtor)
        break;
    }
    if (Root)
      Qualifier = "::" + Qualifier;
    return Id;
  }
  void specialBody(Node &D, bool Proto, bool Separate = false) {
    bool Drop = D.K == Node::Destructor;
    llvm::SaveAndRestore ReceiverBindings(ValueReceivers);
    D.Params = params(true);
    if (Drop && !D.Params.empty())
      fail(D.At, "a destructor takes no parameters");
    D.Noexcept = eat("noexcept");
    applyAttributes(D, attributes());
    if (Drop && !Separate && eat("override"))
      D.Settings["override"] = "1";
    if (Drop && !Separate && eat("final"))
      D.Settings["final"] = "1";
    if (Proto) {
      expect(";");
      D.Prototype = true;
    } else if (eat("="))
      D.Settings["control"] = definitionControl();
    else {
      D.Children.push_back(declarationBody(!Drop));
      if (Drop && eat("cleanup"))
        D.Children.push_back(declarationBody());
    }
  }
  struct Attributes : std::map<std::string, std::string> {
    struct Predicate {
      Token Name;
      size_t Begin, End;
    };
    std::vector<Predicate> Contracts;
  };
  std::string effectBound() {
    if (eat("none"))
      return "none";
    std::string Bound;
    do {
      auto Item = take();
      auto K = Item.Text;
      std::string Effect = K;
      if (K == "read" || K == "write" || K == "allocate" || K == "deallocate" ||
          K == "trap") {
        expect("(");
        auto Region = is("this") ? take() : name();
        if (K == "trap" && Region.Text != "any" && Region.Text != "contract" &&
            Region.Text != "numeric")
          fail(Region, "unknown trap kind");
        Effect += ":" + Region.Text;
        expect(")");
      } else if (!std::set<std::string>{"volatile", "atomic", "synchronize",
                                        "io", "block", "spawn", "suspend",
                                        "cancel_point", "throw", "fp_status",
                                        "fp_control", "whole", "foreign"}
                      .count(K))
        fail(Item, "unknown effect '" + K + "'");
      if (!Bound.empty())
        Bound += ",";
      Bound += Effect;
    } while (eat(","));
    return Bound;
  }
  Attributes attributes() {
    Attributes Result;
    while (is("[") && peek(1).Text == "[") {
      take();
      take();
      do {
        auto Key = is("requires") ? take() : name();
        expect("(");
        if (Key.Text == "requires" || Key.Text == "ensures" ||
            Key.Text == "invariant") {
          size_t Begin = Pos;
          unsigned Parentheses = 1;
          do {
            auto Text = take().Text;
            Parentheses += (Text == "(") - (Text == ")");
          } while (Parentheses);
          Result.Contracts.push_back({std::move(Key), Begin, Pos - 1});
          continue;
        }
        std::string Value;
        if (Key.Text == "effects")
          Value = effectBound();
        else if (Key.Text == "admission_effects")
          fail(Key, "admission_effects requires an asynchronous callable");
        else if (Key.Text == "static_id" || Key.Text == "abi_symbol" ||
                 Key.Text == "abi_cc" || Key.Text == "abi_layout") {
          auto ID = take();
          if (!StringRef(ID.Text).starts_with("\""))
            fail(ID, Key.Text + " requires a string literal");
          Value = unquote(ID);
        } else if (Key.Text == "abi_pack" || Key.Text == "abi_align") {
          auto Amount = take();
          if (Amount.Text.empty() || !llvm::isDigit(Amount.Text.front()) ||
              realToken(Amount.Text))
            fail(Amount, Key.Text + " requires an integer literal");
          Value = llvm::toString(integerLiteral(Amount), 10, false);
        } else if (Key.Text == "init_after") {
          do {
            if (!Value.empty())
              Value += ",";
            Value += qualified().Text;
          } while (eat(","));
        } else if (Key.Text == "init_cancel" || Key.Text == "init_effect") {
          auto Contract = take();
          if (Contract.Text != "finish" &&
              !(Key.Text == "init_cancel" && Contract.Text == "cooperative") &&
              !(Key.Text == "init_effect" &&
                (Contract.Text == "none" || Contract.Text == "compensate")))
            fail(Contract, "invalid static initialization contract");
          Value = Contract.Text;
        } else if (Key.Text == "noescape" ||
                   Key.Text == "returns_borrowed_from" ||
                   Key.Text == "consumes" || Key.Text == "initializes" ||
                   Key.Text == "requires_initialized") {
          std::set<std::string> Seen;
          do {
            auto Arg = name();
            if (!Seen.insert(Arg.Text).second)
              fail(Arg, "duplicate name in attribute");
            if (!Value.empty())
              Value += ",";
            Value += Arg.Text;
          } while (eat(","));
        } else if (Key.Text == "lifecycle_effect")
          Value = expect("whole").Text;
        else
          fail(Key, "unsupported attribute");
        expect(")");
        if (!Result.emplace(Key.Text, Value).second)
          fail(Key, "duplicate attribute");
      } while (eat(","));
      expect("]");
      expect("]");
    }
    return Result;
  }
  void applyAttributes(Node &D, const Attributes &Attrs) {
    if (!IndexingMembers && !Attrs.Contracts.empty()) {
      // Leading attributes precede generic and parameter declarations.
      // Parse their expressions with the type names of the owning declaration.
      llvm::SaveAndRestore Cursor(Pos);
      llvm::SaveAndRestore SavedTypes(Types);
      llvm::SaveAndRestore SavedParameters(TypeParameters);
      llvm::SaveAndRestore SavedHidden(HiddenTypes);
      for (const auto &G : D.Generics) {
        if (G.K == Node::TypeParam) {
          Types.insert(G.Text);
          TypeParameters.insert(G.Text);
          HiddenTypes.erase(G.Text);
        } else {
          HiddenTypes.insert(G.Text);
        }
      }
      for (const auto &Param : D.Params)
        if (!Param.Text.empty())
          HiddenTypes.insert(Param.Text);
      if (D.K == Node::Lambda)
        for (const auto &Capture : D.TemplateArgs)
          HiddenTypes.insert(Capture.Text);
      const bool Record =
          !D.Prototype && (D.K == Node::Record || D.K == Node::Union);
      const bool Callable = D.K == Node::Function || D.K == Node::Constructor ||
                            D.K == Node::Destructor || D.K == Node::Lambda;
      std::vector<Node> Clauses;
      for (const auto &Predicate : Attrs.Contracts) {
        const auto &Name = Predicate.Name;
        if (Name.Text == "invariant" ? !Record : !Callable)
          fail(Name, "inapplicable value contract");
        bool HideResult =
            Name.Text == "ensures" && HiddenTypes.insert("return_value").second;
        Pos = Predicate.Begin;
        Node Clause(Node::Contract, Name);
        Clause.Children.push_back(expr());
        if (Pos != Predicate.End)
          fail(peek(), "unexpected token in contract predicate");
        if (HideResult)
          HiddenTypes.erase("return_value");
        Clauses.push_back(std::move(Clause));
      }
      D.Contracts.insert(D.Contracts.begin(),
                         std::make_move_iterator(Clauses.begin()),
                         std::make_move_iterator(Clauses.end()));
    }
    for (const auto &[Key, Value] : Attrs) {
      if (Key == "noescape" || Key == "returns_borrowed_from" ||
          Key == "consumes") {
        if (D.K != Node::Function && D.K != Node::Lambda)
          fail(D.At, "borrow contract requires a function");
      } else if (Key == "initializes" || Key == "requires_initialized") {
        if (D.K != Node::Function)
          fail(D.At, "construction-state contract requires an instance method");
      } else if (Key == "effects" || Key == "lifecycle_effect") {
        if (D.K != Node::Function && D.K != Node::Destructor &&
            D.K != Node::Constructor && D.K != Node::Lambda)
          fail(D.At, Key + " requires a callable");
      } else if (Key == "abi_symbol" || Key == "abi_cc") {
        if (!D.Foreign ||
            (D.K != Node::Function && (D.K != Node::Object || Key == "abi_cc")))
          fail(D.At, Key + " requires an applicable foreign declaration");
        if (Key == "abi_symbol" &&
            (Value.empty() || Value.find('\0') != std::string::npos ||
             StringRef(Value).starts_with('\1')))
          fail(D.At, "invalid raw object-file symbol");
        if (Key == "abi_cc" && Value != "sysv-amd64-2018.lp64")
          fail(D.At, "CFG002: unavailable calling convention '" + Value + "'");
      } else if (Key == "abi_layout" || Key == "abi_pack" ||
                 Key == "abi_align") {
        fail(D.At, "CFG002: " + Key + " is unavailable on the selected target");
      } else if (D.K != Node::Object)
        fail(D.At, "static attribute requires an object");
      if (!D.Settings.emplace(Key, Value).second)
        fail(D.At, "duplicate attribute");
    }
  }
  void recordMembers(Node &R, const ReceiverType &Receiver, bool Class,
                     bool Union) {
    std::string Access = Class ? "private" : "public";
    while (!eat("}")) {
      if (is("public") || is("private") || is("protected")) {
        Access = take().Text;
        expect(":");
        continue;
      }
      if (Union && (is("default") || is("case"))) {
        bool Default = eat("default");
        expect("case");
        Node C(Node::Variant, name());
        C.Definition = Default;
        if (eat("(")) {
          std::set<std::string> Fields;
          do {
            bool RO = is("const") && peek(1).Text != "<";
            if (RO)
              take();
            auto Ty = type();
            Node Field(Node::Parameter, name());
            Field.Type = Ty;
            Field.Const = RO;
            if (!Fields.insert(Field.Text).second)
              fail(Field.At, "duplicate union payload field");
            C.Params.push_back(std::move(Field));
          } while (eat(","));
          expect(")");
        }
        expect(";");
        R.Children.push_back(std::move(C));
        continue;
      }
      if (!Union && eat("destruction_owner")) {
        Node D(Node::DestructionOwner, peek());
        expect("<");
        D.Type = type();
        closeAngle();
        expect("=");
        D.TemplateArgs.push_back(baseSelector());
        expect(";");
        R.Children.push_back(std::move(D));
        continue;
      }
      // Leading attributes belong to special members as well as ordinary
      // member declarations. The latter keep the same decoration order.
      auto Leading = attributes();
      const bool HasLeading = !Leading.empty() || !Leading.Contracts.empty();
      if (HasLeading && is("configured"))
        fail(peek(), "configuration wrappers must precede attributes");
      bool SpecialProto =
          is("declare") && ((peek(1).Text == R.Text && peek(2).Text == "(") ||
                            peek(1).Text == "~" ||
                            (peek(1).Text == "virtual" && peek(2).Text == "~"));
      if (SpecialProto)
        take();
      bool Virt = is("virtual") && peek(1).Text == "~" && eat("virtual");
      Node D;
      if (is("Complete")) {
        if (HasLeading)
          fail(peek(), "attributes are unavailable on destruction markers");
        take();
        Node I(Node::Init, peek());
        I.Type = "Complete";
        if (!is(";")) {
          I.Text = name().Text;
          if ((I.Text == "base" || I.Text == "virtual_base") && eat("<")) {
            I.Text = (I.Text == "base" ? "$base:" : "$virtual:") + type();
            closeAngle();
          }
        } else
          I.Text = "*";
        expect(";");
        R.Children.push_back(I);
        continue;
      }
      if ((is(R.Text) && peek(1).Text == "(") || is("~")) {
        bool Drop = eat("~");
        D = Node(Drop ? Node::Destructor : Node::Constructor, expect(R.Text));
        if (!Drop && Virt)
          fail(D.At, "a constructor cannot be virtual");
        specialBody(D, SpecialProto);
      } else {
        D = declaration(false, true);
      }
      applyAttributes(D, Leading);
      if (D.K == Node::Object && !D.Settings.count("storage") &&
          (D.Settings.count("static_id") || D.Settings.count("init_after") ||
           D.Settings.count("init_cancel") || D.Settings.count("init_effect")))
        fail(D.At, "static initialization metadata requires static storage");
      if (D.K == Node::Object)
        D.K = Node::Field;
      if (Virt)
        D.Settings["virtual"] = "1";
      D.Settings["access"] = Access;
      auto Key = Receiver.Owner + "::" + D.Text;
      OwnMembers.insert(Key);
      if (!D.Generics.empty() && D.K == Node::Function)
        publishCallableFamily(Key, D.Generics);
      if (D.K == Node::Field)
        FieldReceivers[Key] = ValueReceivers.at(D.Text);
      R.Children.push_back(std::move(D));
    }
  }

  void importRecordMembers(const Parser &Index, const Node &R,
                           const ReceiverType &Receiver, bool Current) {
    for (const auto &Member : R.Children) {
      if (Member.K == Node::Variant || Member.K == Node::DestructionOwner ||
          Member.K == Node::Init)
        continue;
      auto Key = Receiver.Owner + "::" + Member.Text;
      OwnMembers.insert(Key);
      if (Member.K == Node::Function && !Member.Generics.empty())
        publishCallableFamily(Key, Member.Generics);
      if (Member.K == Node::Function)
        publishCallResult(
            Key,
            Index.ReceiverDeclarations.at({Member.At.Line, Member.At.Column}),
            Member, Index, true);
      if (Member.K == Node::Field) {
        const auto &Type = Index.FieldReceivers.at(Key);
        FieldReceivers[Key] = Type;
        if (Current)
          ValueReceivers[Member.Text] = Type;
      }
      if (Current &&
          (Member.K == Node::Record || Member.K == Node::Union ||
           Member.K == Node::Enumeration || Member.K == Node::Alias)) {
        Types.insert(Member.Text);
        if (!Member.Generics.empty() && !Member.Settings.count("specialize"))
          Families[Member.Text] = Member.Generics;
        const auto Site = std::pair(Member.At.Line, Member.At.Column);
        if (auto I = Index.ReceiverDeclarations.find(Site);
            I != Index.ReceiverDeclarations.end())
          NominalReceivers[Member.Text] = I->second;
        if (auto I = Index.AliasDeclarations.find(Site);
            I != Index.AliasDeclarations.end())
          AliasSchemas[Member.Text] = I->second;
        else
          AliasSchemas.erase(Member.Text);
      }
      if ((Member.K == Node::Record || Member.K == Node::Union) &&
          !Member.Prototype) {
        auto Nested = recordReceiver(Member);
        if (auto I = Index.BaseReceivers.find(Nested.Owner);
            I != Index.BaseReceivers.end())
          BaseReceivers[Nested.Owner] = I->second;
        importRecordMembers(Index, Member, Nested, false);
      }
    }
  }

  void indexRecordMembers(const Node &R, const ReceiverType &Receiver,
                          bool Class, bool Union) {
    if (IndexingMembers)
      return;
    // Collect the owning record's member names before parsing any of its
    // executable bodies. The indexing parser has its own lexical state.
    Parser Index(*this);
    Index.IndexingMembers = true;
    Node Header = R;
    try {
      Index.recordMembers(Header, Receiver, Class, Union);
    } catch (const Diagnostic &) {
      // The normal parse owns diagnostics for headers.
      return;
    }
    importRecordMembers(Index, Header, Receiver, true);
    TypeArguments.merge(Index.TypeArguments);
    ParameterTypes.merge(Index.ParameterTypes);
  }

  Node declaration(bool Foreign = false, bool Member = false) {
    llvm::SaveAndRestore Binders(TypeParameters);
    Nest Guard(Depth, peek());
    auto T = peek();
    if (eat("configured")) {
      Node Policy(Node::Configured, T);
      Policy.Settings = settings(false);
      llvm::SaveAndRestore ScopedPolicy(PolicyContext);
      PolicyContext.push_back(sourceSite(T));
      auto D = declaration(Foreign, Member);
      D.Policies.insert(D.Policies.begin(), std::move(Policy));
      return D;
    }
    if (is("[") && peek(1).Text == "[") {
      auto Attributes = attributes();
      if (is("configured"))
        fail(peek(), "configuration wrappers must precede attributes");
      auto D = declaration(Foreign, Member);
      applyAttributes(D, Attributes);
      return D;
    }
    if (eat("configuration")) {
      Node N(Node::Config, T);
      N.Settings = settings(true);
      expect(";");
      PolicyContext.push_back(sourceSite(T));
      return N;
    }
    if (eat("namespace") || eat("extern")) {
      bool NS = T.Text == "namespace";
      Node N(NS ? Node::Namespace : Node::Linkage, T);
      if (NS)
        N.Text = name().Text;
      else {
        auto Linkage = take();
        if (Linkage.Text == "\"C++\"")
          fail(Linkage, "CFG002: the target has no direct C++ ABI binding");
        if (Linkage.Text != "\"C\"")
          fail(Linkage, "expected \"C\" or \"C++\" linkage");
      }
      if (eat("{")) {
        if (NS) {
          llvm::SaveAndRestore NamespaceScope(Namespace,
                                              Namespace + N.Text + "::");
          llvm::SaveAndRestore NamespaceAliases(AliasSchemas);
          llvm::SaveAndRestore NamespaceTypes(NominalReceivers);
          llvm::SaveAndRestore NamespaceValues(ValueReceivers);
          llvm::SaveAndRestore NamespacePolicy(PolicyContext);
          while (!eat("}"))
            N.Children.push_back(declaration(Foreign));
        } else
          while (!eat("}"))
            N.Children.push_back(declaration(true));
      } else if (!NS)
        N.Children.push_back(declaration(true));
      else
        fail(T, "expected '{'");
      if (NS)
        publishMemberNames(N, N.Text + "::");
      return N;
    }
    if (eat("constraint")) {
      Node N(Node::Constraint, name());
      auto Saved = Types;
      N.Generics = generic();
      llvm::SaveAndRestore GenericScope(GenericDepth, GenericDepth + 1);
      Families[N.Text] = N.Generics;
      expect("{");
      while (!eat("}")) {
        Node Rule(Node::Requirement, peek());
        if (eat("requires")) {
          Rule.Text = "requires";
          Rule.Children = {condition()};
          expect(";");
        } else if (eat("type")) {
          Rule.Text = "type";
          Rule.Type = type();
          expect(";");
        } else {
          expect("expression");
          llvm::SaveAndRestore RequirementValues(ValueReceivers);
          Rule.Params = params(true);
          expect("{");
          while (!eat("}")) {
            size_t End = Pos, Arrow = Tokens->size();
            unsigned D = 0;
            while (End < Tokens->size() &&
                   !((*Tokens)[End].Text == ";" && !D)) {
              const auto &W = (*Tokens)[End].Text;
              if (W == "->" && !D)
                Arrow = End;
              D += (W == "(" || W == "[");
              D -= (W == ")" || W == "]");
              ++End;
            }
            if (Arrow == Tokens->size())
              fail(peek(), "expression requirement needs a result type");
            editableTokens()[Arrow].Text = "$result";
            auto E = expr();
            expect("$result");
            E.Type = type();
            E.Noexcept = eat("noexcept");
            expect(";");
            Rule.Children.push_back(E);
          }
        }
        N.Children.push_back(Rule);
      }
      expect(";");
      auto Required = std::make_shared<RequirementSite>();
      Required->Scope = Namespace;
      Required->DefinedAt = N.At;
      Required->RecordScope = !CurrentReceiver.Owner.empty();
      Required->Policy = PolicyContext;
      Required->Parameters.append(N.Generics.begin(), N.Generics.end());
      for (const auto &Rule : N.Children) {
        if (Rule.Text != "requires") {
          Required->Pure = false;
          Required->Conditions.emplace_back(Node::Empty, Rule.At);
        } else
          Required->Conditions.push_back(Rule.Children.front());
      }
      NamedRequirements[Namespace + N.Text] = std::move(Required);
      Types = std::move(Saved);
      return N;
    }
    if (eat("alias")) {
      Node N(Node::Alias, name());
      expect("=");
      std::string Schema;
      ReceiverType Receiver;
      N.Type = type(&Schema, &Receiver);
      expect(";");
      Types.insert(N.Text);
      HiddenTypes.erase(N.Text);
      AliasSchemas[N.Text] = Schema;
      AliasDeclarations[{N.At.Line, N.At.Column}] = std::move(Schema);
      NominalReceivers[N.Text] = Receiver;
      ReceiverDeclarations[{N.At.Line, N.At.Column}] = std::move(Receiver);
      return N;
    }
    auto Saved = Types;
    std::vector<Node> G;
    if (eat("generic"))
      G = generic();
    llvm::SaveAndRestore GenericScope(GenericDepth, GenericDepth + !G.empty());
    Node Requires;
    if (!G.empty() && eat("requires"))
      Requires = condition();
    DefinitionDomain Domain{{Namespace, {}, {}, T}, CurrentDomain};
    llvm::SaveAndRestore DomainScope(CurrentDomain);
    if (!G.empty()) {
      Domain.Site.Parameters.append(G.begin(), G.end());
      if (Requires.K != Node::Empty)
        Domain.Site.Conditions.push_back(Requires);
      Domain.Site.RecordScope = Member || !CurrentReceiver.Owner.empty();
      Domain.Site.Policy = PolicyContext;
      for (const auto &[Name, Binding] : ValueReceivers)
        Domain.Site.ShadowedValues.insert(Name);
      CurrentDomain = &Domain;
    }
    if (is("declare") && (peek(1).Text == "struct" || peek(1).Text == "class" ||
                          peek(1).Text == "union" || peek(1).Text == "enum")) {
      take();
      auto Kind = take();
      Node D(Kind.Text == "enum"    ? Node::Enumeration
             : Kind.Text == "union" ? Node::Union
                                    : Node::Record,
             name());
      D.Type = Kind.Text;
      if (D.K == Node::Enumeration) {
        expect(":");
        D.Type = type();
      }
      D.Prototype = true;
      expect(";");
      Types.insert(D.Text);
      AliasSchemas.erase(D.Text);
      return D;
    }
    bool Specialize = eat("specialize");
    if (Specialize && !is("struct") && !is("class") && !is("union"))
      fail(peek(), "specialize requires a type family");
    if (is("struct") || is("class") || is("union")) {
      auto Kind = take().Text;
      bool Union = Kind == "union", Class = Kind == "class";
      bool Manual = Class && eat("Manual");
      Node R(Union ? Node::Union : Node::Record, name());
      R.Type = Kind;
      auto Receiver = recordReceiver(R, G.empty() && !Specialize &&
                                            (CurrentReceiver.Owner.empty() ||
                                             CurrentReceiver.ExactNominal));
      if (!Specialize) {
        NominalReceivers[R.Text] = Receiver;
        ReceiverDeclarations[{R.At.Line, R.At.Column}] = Receiver;
      }
      auto RecordTypes = NominalReceivers;
      auto RecordValues = ValueReceivers;
      llvm::SaveAndRestore ReceiverScope(CurrentReceiver, Receiver);
      llvm::SaveAndRestore InstanceScope(ReceiverAvailable, true);
      R.Generics = G;
      if (Specialize) {
        while (eat("::"))
          R.Text += "::" + name().Text;
        if (!Families.count(R.Text))
          fail(R.At, "specialization must name an existing type family");
        if (auto I = NominalReceivers.find(R.Text); I != NominalReceivers.end())
          SpecializedReceivers.insert(I->second.Owner);
        R.Pattern = templateArgs(R.Text);
        R.Settings["specialize"] = "1";
      }
      Types.insert(R.Text);
      AliasSchemas.erase(R.Text);
      auto OuterAliases = AliasSchemas;
      if (!Specialize && !G.empty())
        Families[R.Text] = G;
      if (Requires.K != Node::Empty)
        R.Params.push_back(Requires);
      if (is(";"))
        fail(R.At, "incomplete declaration requires declare");
      if (Manual)
        R.Settings["manual"] = "1";
      if (!Union && eat("final"))
        R.Settings["final"] = "1";
      if (!Union && eat(":")) {
        do {
          Node B(Node::TypeArg, peek());
          B.Definition = eat("virtual");
          ReceiverType Base;
          B.Type = type(nullptr, &Base);
          BaseReceivers[Receiver.Owner].push_back(std::move(Base));
          R.TemplateArgs.push_back(B);
        } while (eat(","));
      }
      expect("{");
      indexRecordMembers(R, Receiver, Class, Union);
      recordMembers(R, Receiver, Class, Union);
      expect(";");
      Types = std::move(Saved);
      Types.insert(R.Text);
      AliasSchemas = std::move(OuterAliases);
      NominalReceivers = std::move(RecordTypes);
      ValueReceivers = std::move(RecordValues);
      publishMemberNames(R, R.Text + "::");
      return R;
    }
    if (eat("enum")) {
      Node E(Node::Enumeration, name());
      expect(":");
      E.Type = type();
      Types.insert(E.Text);
      AliasSchemas.erase(E.Text);
      expect("{");
      if (is("}"))
        fail(peek(), "enum requires a case");
      while (!eat("}")) {
        expect("case");
        Node V(Node::Enumerator, name());
        V.Children = {condition()};
        E.Children.push_back(V);
        if (!eat(",")) {
          expect("}");
          break;
        }
      }
      expect(";");
      return E;
    }
    if (!Member && !Foreign && separateSpecial()) {
      std::string Q;
      bool Dtor = false;
      std::vector<Node> Owners;
      auto Id = declarationName(Q, Dtor, &Owners);
      Node D(Dtor ? Node::Destructor : Node::Constructor, Id);
      D.Settings["qualifier"] = Q;
      D.Pattern = std::move(Owners);
      D.Generics = G;
      if (Requires.K != Node::Empty)
        D.TemplateArgs.push_back(std::move(Requires));
      specialBody(D, false, true);
      Types = std::move(Saved);
      return D;
    }
    if (Foreign && is("declare"))
      fail(peek(), "a foreign prototype uses its linkage declaration");
    if (!Foreign && is("define"))
      fail(peek(), "define requires an external object definition");
    bool Proto = eat("declare"), Def = eat("define");
    bool StorageStatic = eat("static"),
         ThreadLocal = !StorageStatic && eat("thread_local");
    bool RO = is("const") && peek(1).Text != "<";
    if (RO)
      take();
    bool CE = !RO && eat("constexpr"), Eval = !RO && !CE && eat("consteval");
    bool Static = StorageStatic || (!ThreadLocal && !RO && eat("static"));
    bool Virtual = !Static && !ThreadLocal && !RO && eat("virtual");
    ReceiverType Receiver;
    auto Ty = eat("auto") ? std::string("auto") : type(nullptr, &Receiver);
    std::string Q;
    bool Dtor = false;
    std::vector<Node> Owners;
    auto Id = declarationName(Q, Dtor, &Owners);
    if (Dtor || (!Q.empty() && (Member || Foreign || Proto || Def)))
      fail(Id, "invalid qualified declaration");
    bool Fn = !Def && (!Q.empty() || operatorSpelling(Id.Text) || Proto ||
                       (Foreign && is("(")) || !G.empty() || functionBody());
    if (Ty == "auto" && (Foreign || Fn))
      fail(Id, "this declaration requires an explicit type");
    if (!Fn) {
      if (Foreign && !Def && !is(";"))
        fail(Id, "an external object initializer requires define");
      if (Foreign && !Def && CE)
        fail(Id, "a constexpr external object requires a definition");
      if (Virtual || Eval || (Static && !StorageStatic) || (Foreign && Static))
        fail(Id, "invalid object declaration modifier");
      Receiver.Readonly |= RO || CE;
      ValueReceivers[Id.Text] = Receiver;
      auto O = object(Id, Ty, RO, CE);
      if (Ty == "auto" && O.Children.size() == 1) {
        auto Deduced = receiverType(O.Children.front());
        Deduced.Readonly = RO || CE;
        Deduced.QualificationUnknown = false;
        ValueReceivers[Id.Text] = std::move(Deduced);
      }
      ReceiverDeclarations[{Id.Line, Id.Column}] = ValueReceivers.at(Id.Text);
      if (Static || ThreadLocal)
        O.Settings["storage"] = Static ? "static" : "thread_local";
      O.Foreign = Foreign;
      O.Definition = Def;
      return O;
    }
    if (RO || ThreadLocal ||
        ((Static || Virtual) && (!Member || Foreign || !Q.empty())) ||
        (StorageStatic && (CE || Eval)))
      fail(Id, "invalid function declaration modifier");
    Node F(Node::Function, Id);
    ReceiverDeclarations[{Id.Line, Id.Column}] = Receiver;
    if (Static)
      F.Settings["static"] = "1";
    if (Virtual)
      F.Settings["virtual"] = "1";
    F.Type = Ty;
    F.Generics = G;
    F.Pattern = std::move(Owners);
    if (!Q.empty())
      F.Settings["qualifier"] = Q;
    F.Foreign = Foreign;
    F.Required = CE || Eval;
    if (Eval)
      F.Settings["mode"] = "consteval";
    if (!G.empty() && Q.empty())
      publishCallableFamily(Id.Text, G);
    if (Requires.K != Node::Empty)
      F.TemplateArgs.push_back(std::move(Requires));
    llvm::SaveAndRestore ReceiverBindings(ValueReceivers);
    F.Params = params(true);
    if ((Member && !Static) || !Q.empty()) {
      F.Const = eat("const");
      if (is("&") || is("&&"))
        F.Settings["category"] = take().Text;
    }
    if (Member)
      publishCallResult(CurrentReceiver.Owner + "::" + Id.Text, Receiver, F,
                        *this, true);
    else if (Q.empty())
      publishCallResult(Namespace + Id.Text, Receiver, F, *this, false);
    llvm::SaveAndRestore ConstReceiver(ReceiverReadonly, F.Const);
    llvm::SaveAndRestore InstanceScope(ReceiverAvailable,
                                       (Member && !Static) || !Q.empty());
    F.Noexcept = eat("noexcept");
    applyAttributes(F, attributes());
    if (Member && eat("override"))
      F.Settings["override"] = "1";
    if (Member && eat("final"))
      F.Settings["final"] = "1";
    if (Proto || (Foreign && is(";"))) {
      expect(";");
      F.Prototype = true;
    } else if (eat("=")) {
      F.Settings["control"] = definitionControl();
      if (F.Settings["control"] == "default" && F.Text != "operator=")
        fail(F.At, "this function has no generated default definition");
    } else {
      auto OuterHidden = HiddenTypes;
      for (const auto &P : F.Params)
        if (Types.count(P.Text) || integerLibraryName(P.Text, true))
          HiddenTypes.insert(P.Text);
      F.Children.push_back(declarationBody());
      HiddenTypes = std::move(OuterHidden);
    }
    Types = std::move(Saved);
    return F;
  }

public:
  explicit Parser(std::vector<Token> T,
                  const RelationalMembers *Bound = nullptr)
      : Tokens(std::make_shared<std::vector<Token>>(std::move(T))),
        BoundRelationalMembers(Bound) {
    Types.insert({"std::Unit", "std::AccessError", "std::Ref",
                  "std::ScalarError", "std::Result"});
    Types.insert({"std::mem::StorageView", "std::mem::StorageIdentity"});
    Types.insert({"std::numeric::NumericResult", "std::numeric::NumericStatus",
                  "std::numeric::NumericErrorCode", "std::numeric::FPFlag",
                  "std::numeric::FPFlagSet", "std::numeric::RoundingMode"});
    Types.insert({"std::numeric::FPControl", "std::numeric::FPStatus",
                  "std::numeric::FPControlError",
                  "std::numeric::SubnormalPolicy"});
    Node TypeParam(Node::TypeParam, {});
    Families["std::Ref"] = {TypeParam};
    Families["std::Result"] = {TypeParam, TypeParam};
    Families["std::numeric::NumericResult"] = {TypeParam};
    Families["std::from_underlying"] = {TypeParam};
    Families["std::try_from_underlying"] = {TypeParam};
  }
  std::vector<Node> unit() {
    std::vector<Node> V;
    while (!is("")) {
      auto D = declaration();
      publishRootAliases(D);
      V.push_back(std::move(D));
    }
    for (auto &[Key, Query] : TypeQueries)
      V.push_back(std::move(Query));
    return V;
  }
  Node expression() {
    auto V = expr();
    if (!is(""))
      fail(peek(), "unexpected token in expression");
    return V;
  }
};
} // namespace
std::vector<Node> cpn::parse(StringRef S, const Options &O,
                             const RelationalMembers *Bound) {
  return Parser(lex(S, O), Bound).unit();
}
Node cpn::parseExpression(StringRef S, const Options &O) {
  return Parser(lex(S, O, true)).expression();
}
void cpn::configure(Options &O, const Node &N, ConfigScope Scope) {
  auto requireFloatFormat = [&](StringRef Format) {
    if (floating(Format))
      return;
    if (Format == "f16" || Format == "bf16" || Format == "f128" ||
        Format == "dec32" || Format == "dec64" || Format == "dec128")
      fail(N.At, "CFG002: unavailable floating format '" + Format.str() + "'");
    fail(N.At, "CFG001: invalid floating format '" + Format.str() + "'");
  };
  auto P = N.Settings.find("preset");
  if (P != N.Settings.end()) {
    auto V = P->second;
    if (V != "Debug" && V != "Release" && V != "MinimalDebug" &&
        V != "MinimalRelease" && V != "Custom")
      fail(N.At, "CFG001: unknown preset");
    if (Scope > ConfigScope::File)
      fail(N.At, "CFG001: preset must be bound before declarations");
    O.CustomPreset = V == "Custom";
    const bool Minimal = StringRef(V).starts_with("Minimal");
    const bool Debug = O.CustomPreset || StringRef(V).ends_with("Debug");
    const bool CheckContracts = Debug && !Minimal;
    auto Default = [&](const char *Key, auto &Field, const auto &Value) {
      if (!O.ExplicitConfiguration.count(Key))
        Field = Value;
    };
    Default("contracts.enabled", O.ContractsEnabled, !Minimal);
    Default("contracts.validation", O.ContractValidation,
            CheckContracts ? "check" : "document");
    Default("contracts.invariants", O.InvariantValidation,
            Minimal          ? "disabled"
            : CheckContracts ? "check"
                             : "document");
    Default("contracts.trusted_assumptions", O.TrustedAssumptions, false);
    Default("construction.analysis", O.InterproceduralConstruction, Debug);
    Default("effects.inference", O.InterproceduralEffects, Debug);
    Default("effects.diagnostics", O.StrictEffectDiagnostics, false);
    Default("memory.raw_validation", O.RawValidation, Debug);
    Default("library.debug_assertions", O.DebugAssertions, Debug);
    Default("numeric.fp.profile", O.FPProfile, Debug ? "strict" : "native");
    Default("numeric.integer.overflow", O.Overflow,
            Debug ? "checked" : "native");
  }
  for (auto &KV : N.Settings) {
    auto &K = KV.first;
    auto &V = KV.second;
    if (K == "preset")
      continue;
    O.ExplicitConfiguration.insert(K);
    auto StringValue = [&] {
      if (!StringRef(V).starts_with('"'))
        fail(N.At, "CFG001: " + K + " requires a string");
      return unquote({V, N.At.Line, N.At.Column});
    };
    static const std::map<StringRef, ConfigScope> UnavailableCapabilities{
        {"compilation.modules", ConfigScope::Project},
        {"compilation.separate", ConfigScope::Project},
        {"tooling.contract_export", ConfigScope::Project},
        {"exceptions.language", ConfigScope::Project},
        {"exceptions.secondary.dynamic_storage", ConfigScope::Project},
        {"generic.higher_kinds", ConfigScope::Declaration},
        {"generic.associated_entities", ConfigScope::Declaration},
        {"meta.reflection", ConfigScope::Declaration},
        {"meta.generate", ConfigScope::Declaration},
        {"meta.generate_layout", ConfigScope::Declaration},
        {"numeric.software_fallback", ConfigScope::Declaration},
        {"atomic.software_fallback", ConfigScope::Declaration},
    };
    if (auto It = UnavailableCapabilities.find(K);
        It != UnavailableCapabilities.end()) {
      if (V == "true")
        fail(N.At, "CFG002: " + K + " is unavailable");
      if (V != "false")
        fail(N.At, "CFG001: expected Boolean value for " + K);
      if (Scope > It->second)
        fail(N.At, "CFG001: " + K + " is outside its configuration scope");
      continue;
    }
    if ((K == "target" || K == "source.identifiers" ||
         K == "source.unicode_version" || K == "static.schedule" ||
         K == "static.workers" || K == "static.identity_namespace") &&
        Scope != ConfigScope::Project)
      fail(N.At, "CFG001: " + K +
                     " must be bound before source tokenization or binding");
    if ((K == "numeric.float.formats" || K == "numeric.integer.widths") &&
        Scope > ConfigScope::Declaration)
      fail(N.At,
           "CFG001: " + K + " cannot be overridden below declaration scope");
    if (K == "static.schedule") {
      if (V == "custom_parallel")
        fail(N.At, "CFG002: parallel static initialization is unavailable");
      if (V != "serial")
        fail(N.At, "CFG001: invalid static scheduling policy");
      continue;
    }
    if (K == "static.workers") {
      if (V != "1")
        fail(N.At, "CFG001: serial static initialization requires one worker");
      continue;
    }
    if (K == "static.identity_namespace") {
      O.StaticIdentityNamespace = StringValue();
      if (O.StaticIdentityNamespace.empty())
        fail(N.At, "CFG001: static identity namespace must not be empty");
      continue;
    }
    if (K == "memory.raw_validation") {
      if (V != "available" && V != "contract")
        fail(N.At, "CFG001: invalid raw memory validation policy");
      O.RawValidation = V == "available";
      continue;
    }
    if (K == "library.debug_assertions") {
      if (V != "true" && V != "false")
        fail(N.At, "CFG001: expected Boolean library.debug_assertions");
      O.DebugAssertions = V == "true";
      continue;
    }
    if (StringRef(K).starts_with("contracts.")) {
      if (Scope > ConfigScope::Declaration)
        fail(N.At, "CFG001: contract policy binds at declaration scope");
      if (K == "contracts.enabled" || K == "contracts.trusted_assumptions") {
        if (V != "true" && V != "false")
          fail(N.At, "CFG001: expected Boolean contract setting");
        (K == "contracts.enabled" ? O.ContractsEnabled : O.TrustedAssumptions) =
            V == "true";
      } else if (K == "contracts.validation" &&
                 (V == "check" || V == "prove" || V == "document" ||
                  V == "trusted"))
        O.ContractValidation = V;
      else if (K == "contracts.invariants" &&
               (V == "check" || V == "document" || V == "disabled"))
        O.InvariantValidation = V;
      else
        fail(N.At, "CFG001: invalid contract policy");
      continue;
    }
    if (K == "construction.analysis" || K == "effects.inference") {
      if (Scope > ConfigScope::Declaration)
        fail(N.At,
             "CFG001: " + K + " cannot be overridden below declaration scope");
      if (V != "local" && V != "interprocedural")
        fail(N.At, "CFG001: invalid analysis mode for " + K);
      (K == "construction.analysis" ? O.InterproceduralConstruction
                                    : O.InterproceduralEffects) =
          V == "interprocedural";
      continue;
    }
    if (K == "effects.opaque_default" || K == "effects.diagnostics") {
      if (Scope > ConfigScope::Declaration)
        fail(N.At,
             "CFG001: " + K + " cannot be overridden below declaration scope");
      if (K == "effects.opaque_default" && V != "conservative")
        fail(N.At, "CFG001: invalid opaque effect policy");
      if (K == "effects.diagnostics") {
        if (V != "default" && V != "strict")
          fail(N.At, "CFG001: invalid effect diagnostic policy");
        O.StrictEffectDiagnostics = V == "strict";
      }
      continue;
    }
    if (K == "source.unicode_version") {
      if (StringValue() != "17.0.0")
        fail(N.At, "CFG002: unavailable Unicode data version");
      continue;
    }
    if (K == "generic.max_normalization_nodes" ||
        K == "generic.max_solver_steps" || K == "generic.max_instantiations") {
      uint64_t Limit;
      if (StringRef(V).getAsInteger(10, Limit) || !Limit)
        fail(N.At, "CFG001: generic resource limit must be a positive integer");
      if (K == "generic.max_normalization_nodes")
        O.MaxNormalNodes = Limit;
      else if (K == "generic.max_solver_steps")
        O.MaxSolverSteps = Limit;
      else
        O.MaxInstantiations = Limit;
      continue;
    }
    if (K == "numeric.literal.real_default") {
      requireFloatFormat(V);
      O.DefaultReal = V;
      continue;
    }
    if (K == "numeric.fp.require_finite") {
      if (V != "true" && V != "false")
        fail(N.At, "CFG001: expected Boolean floating result setting");
      O.FPRequireFinite = V == "true";
      continue;
    }
    if (StringRef(K).starts_with("numeric.fp.initial_") &&
        Scope > ConfigScope::File)
      fail(N.At, "CFG001: initial floating controls bind to the root context");
    if (K == "numeric.fp.trap_mask" || K == "numeric.fp.initial_trap_mask" ||
        K == "numeric.fp.result_mask") {
      if (K == "numeric.fp.trap_mask" && V == "current") {
        O.FPTrapMask.reset();
        continue;
      }
      StringRef Items(V);
      if (!Items.consume_front("[") || !Items.consume_back("]"))
        fail(N.At, "CFG001: floating event mask requires a set");
      static const std::map<StringRef, unsigned> Events{{"Invalid", 1},
                                                        {"DivideByZero", 4},
                                                        {"Overflow", 8},
                                                        {"Underflow", 16},
                                                        {"Inexact", 32}};
      llvm::SmallVector<StringRef> Members;
      Items.split(Members, ',', -1, false);
      unsigned Mask = 0;
      for (auto Member : Members) {
        auto It = Events.find(Member);
        if (It == Events.end() || (Mask & It->second))
          fail(N.At, "CFG001: invalid or duplicate floating event");
        Mask |= It->second;
      }
      if (K == "numeric.fp.result_mask")
        O.FPResultMask = Mask;
      else
        (K == "numeric.fp.trap_mask" ? O.FPTrapMask : O.FPInitialTraps) = Mask;
      continue;
    }
    if (K == "numeric.fp.subnormal" || K == "numeric.fp.initial_subnormal") {
      if (V != "preserve" && !(V == "current" && K == "numeric.fp.subnormal"))
        fail(N.At, "CFG002: unsupported subnormal control");
      (K == "numeric.fp.subnormal" ? O.FPSubnormal : O.InitialSubnormal) = V;
      continue;
    }
    if (K == "numeric.literal.real_rounding" || K == "numeric.fp.rounding" ||
        K == "numeric.fp.initial_rounding") {
      static const std::set<std::string> Modes = {
          "nearest_ties_even", "nearest_ties_away", "toward_zero",
          "toward_positive_infinity", "toward_negative_infinity"};
      bool Literal = K == "numeric.literal.real_rounding";
      if (!Modes.count(V) && !(K == "numeric.fp.rounding" && V == "current"))
        fail(N.At, "CFG001: invalid rounding mode");
      if (!Literal && V == "nearest_ties_away")
        fail(N.At, "CFG002: native x86-64 arithmetic does not supply "
                   "nearest_ties_away");
      if (Literal)
        O.LiteralRounding = V;
      else if (K == "numeric.fp.rounding")
        O.FPRounding = V;
      else
        O.InitialRounding = V;
      continue;
    }
    if (K == "numeric.fp.profile") {
      if (V == "reproducible" || V == "fast")
        fail(N.At, "CFG002: unavailable floating profile '" + V + "'");
      if (V != "strict" && V != "native")
        fail(N.At, "CFG001: unknown floating profile '" + V + "'");
      O.FPProfile = V;
      continue;
    }
    if (K == "numeric.float.formats") {
      StringRef List(V);
      if (!List.consume_front("[") || !List.consume_back("]"))
        fail(N.At, "CFG001: expected a list of floating formats");
      llvm::SmallVector<StringRef> Members;
      List.split(Members, ',', -1, false);
      O.FloatFormats.clear();
      for (auto Member : Members) {
        requireFloatFormat(Member);
        if (!O.FloatFormats.insert(Member.str()).second)
          fail(N.At, "CFG001: duplicate floating format");
      }
      continue;
    }
    if (K == "numeric.fp.relaxations") {
      if (V != "[]")
        fail(N.At,
             "CFG002: requested floating-point relaxations are unavailable");
      continue;
    }
    if (K == "numeric.integer.overflow") {
      if (V != "checked" && V != "native" && V != "wrapping" &&
          V != "saturating")
        fail(N.At, "CFG001: unknown overflow policy");
      O.Overflow = V;
    } else if (K == "source.identifiers") {
      if (V != "ascii" && V != "unicode")
        fail(N.At, "unknown identifier profile");
      O.ASCII = V == "ascii";
    } else if (K == "numeric.literal.integer_default") {
      if (!builtin(V) || V.empty() || V[0] != 'i' || V == "isize")
        fail(N.At, "CFG001: invalid default integer");
      O.DefaultInt = V;
    } else if (K == "target") {
      if (StringValue() != "x86_64-linux-gnu")
        fail(N.At, "CFG002: unsupported target");
    } else if (K == "numeric.integer.widths") {
      StringRef List(V);
      if (!List.consume_front("[") || !List.consume_back("]"))
        fail(N.At, "CFG001: expected a list of integer widths");
      llvm::SmallVector<StringRef> Members;
      List.split(Members, ',');
      O.IntegerWidths.clear();
      for (auto Member : Members) {
        uint64_t W;
        if (Member.getAsInteger(10, W) || !W)
          fail(N.At, "CFG001: invalid integer width");
        if (W != 8 && W != 16 && W != 32 && W != 64)
          fail(N.At, "CFG002: unavailable integer width " + Member.str());
        if (!O.IntegerWidths.insert(W).second)
          fail(N.At, "CFG001: duplicate integer width");
      }
    } else if (K == "diagnostics.minimum") {
      static const std::map<std::string, Severity> Levels{
          {"INFO", Severity::Info},
          {"WARNING", Severity::Warning},
          {"ANOMALY", Severity::Anomaly},
          {"ERROR", Severity::Error},
          {"none", Severity::None}};
      auto It = Levels.find(V);
      if (It == Levels.end())
        fail(N.At, "CFG001: invalid minimum diagnostic category");
      O.Minimum = It->second;
    } else if (K == "diagnostics.promote" || K == "diagnostics.suppress") {
      if (!StringRef(V).starts_with("[") || !StringRef(V).ends_with("]"))
        fail(N.At, "CFG001: diagnostic selection requires a list");
      static const std::set<std::string> NonErrors{
          "LIFE003", "LIFE004", "GEN001",  "MEM002",
          "NUM002",  "NUM003",  "STAT002", "EXC001"};
      bool Promoting = K == "diagnostics.promote";
      auto &Selection = Promoting ? O.Promote : O.Suppress;
      Selection.clear();
      llvm::SmallVector<StringRef> Codes;
      StringRef(V).drop_front().drop_back().split(Codes, ',', -1, false);
      for (auto Code : Codes) {
        bool Category =
            Code == "INFO" || Code == "WARNING" || Code == "ANOMALY";
        if (!NonErrors.count(Code.str()) && !(Promoting && Category))
          fail(N.At, "CFG001: invalid diagnostic selection for " + K);
        Selection.insert(Code.str());
      }
    } else
      fail(N.At, "CFG001: unknown configuration key '" + K + "'");
  }
  if (!O.CustomPreset) {
    unsigned DefaultWidth = 0;
    StringRef(O.DefaultInt).drop_front().getAsInteger(10, DefaultWidth);
    if (!O.IntegerWidths.count(DefaultWidth))
      fail(N.At, "CFG002: literal default " + O.DefaultInt + " is disabled");
    if (N.Settings.count("numeric.literal.real_default") &&
        !O.FloatFormats.count(O.DefaultReal))
      fail(N.At, "CFG002: literal default " + O.DefaultReal + " is disabled");
  }
}
