#include "Sema.h"
#include <array>
using namespace cpn;
namespace {
using Bindings = std::map<std::string, std::string>;
enum class AssignmentKind { Unknown, LValue, ConstLValue, RValue, ConstRValue };
struct Operation {
  std::string Name;
  std::vector<std::string> Types;
  std::array<AssignmentKind, 2> Assignment = {};
  bool operator<(const Operation &Other) const {
    return std::tie(Name, Types, Assignment) <
           std::tie(Other.Name, Other.Types, Other.Assignment);
  }
};
struct Domain {
  Bindings Equal;
  std::map<std::string, bool> Predicates;
  std::map<Operation, std::string> Operations;
};
using Alternatives = std::vector<Domain>;

bool needsWitness(const Node &N) {
  static const std::set<std::string> Binary = {
      "+",  "-",   "*",   "/",  "%",  "|",  "&",  "^",  "<<",
      ">>", "+=",  "-=",  "*=", "/=", "%=", "|=", "&=", "^=",
      "=",  "<<=", ">>=", "==", "!=", "<",  ">",  "<=", ">="};
  static const std::set<std::string> Unary = {"+", "-", "~", "!", "++", "--"};
  return N.K == Node::Binary ? Binary.count(N.Text)
                             : N.K == Node::Unary && Unary.count(N.Text);
}
std::string operatorKey(const Node &N) {
  if (N.K == Node::Unary)
    return std::string(N.Definition ? "postfix " : "prefix ") + N.Text;
  return N.Text;
}

std::string valueType(std::string T) {
  if (llvm::StringRef(T).starts_with("forward "))
    T.erase(0, 8);
  while (llvm::StringRef(T).ends_with("&"))
    T.pop_back();
  if (llvm::StringRef(T).starts_with("const<") && T.back() == '>')
    T = T.substr(6, T.size() - 7);
  return T;
}
std::string substitute(std::string T, const Bindings &B) {
  T = valueType(std::move(T));
  auto I = B.find(T);
  return I == B.end() ? T : I->second;
}
std::string representative(std::string T, const Domain &D) {
  for (auto I = D.Equal.find(T); I != D.Equal.end(); I = D.Equal.find(T))
    T = I->second;
  return T;
}
struct Checker {
  Context &U;
  Frame Names;
  std::set<std::string> Parameters;
  Bindings Variables;
  bool InConstructor = false;
  uint64_t Steps = 0;
  Checker(Context &U, const std::string &Prefix)
      : U(U), Names(U, nullptr, nullptr, Prefix) {}
  void step(const Token &T) {
    if (++Steps > U.Opt.MaxNormalNodes)
      throw ResourceExhausted{{T, "generic normalization resource exhausted"}};
  }
  std::string operand(const Node &E, const Bindings &Scope) const {
    if (E.K == Node::Name) {
      if (E.Text == "true" || E.Text == "false")
        return "bool";
      auto I = Scope.find(E.Text);
      return I == Scope.end() ? "" : valueType(I->second);
    }
    if (E.K == Node::Number)
      return "integer";
    if (E.K == Node::Real)
      return "real";
    if (E.K == Node::Call && E.Children[0].K == Node::Name) {
      const auto &C = E.Children[0];
      if (builtin(C.Text) || Parameters.count(C.Text))
        return C.Text;
      if ((C.Text == "std::move" || C.Text == "std::forward") &&
          E.Children.size() == 2)
        return operand(E.Children[1], Scope);
    }
    return "";
  }

  AssignmentKind assignmentKind(const Node &E, const Bindings &Scope) const {
    if (E.K == Node::Name) {
      if (auto I = Scope.find(E.Text); I != Scope.end()) {
        auto Type = llvm::StringRef(I->second);
        Type.consume_front("forward ");
        return Type.starts_with("const<") ? AssignmentKind::ConstLValue
                                          : AssignmentKind::LValue;
      }
    }
    if (E.K == Node::Binary && E.Text == "=")
      return assignmentKind(E.Children.front(), Scope);
    if (E.K == Node::Call && E.Children.front().K == Node::Name) {
      const auto &Name = E.Children.front().Text;
      if (Name == "std::move" && E.Children.size() == 2) {
        auto Kind = assignmentKind(E.Children.back(), Scope);
        if (Kind == AssignmentKind::LValue)
          return AssignmentKind::RValue;
        if (Kind == AssignmentKind::ConstLValue)
          return AssignmentKind::ConstRValue;
        return Kind;
      }
      if (!Scope.count(Name) && (builtin(Name) || Parameters.count(Name)))
        return AssignmentKind::RValue;
    }
    return AssignmentKind::Unknown;
  }

  // A method designator is bound together with its arguments. It does not
  // independently require a data field with the same spelling.
  template <class Child>
  std::optional<Operation> operation(const Node &N, const Bindings &Scope,
                                     Child type) const {
    const auto &A = N.Children;
    Operation Op;
    if (N.K == Node::Call) {
      const auto &C = A.front();
      if (C.K == Node::Member) {
        Op.Name = "." + C.Text + "()";
        Op.Types.push_back(type(C.Children.front()));
        if (C.Definition && llvm::StringRef(Op.Types.front()).ends_with("*"))
          Op.Types.front().pop_back();
      } else if (C.K == Node::Name && Scope.count(C.Text)) {
        Op.Name = "()";
        Op.Types.push_back(type(C));
      } else
        return {};
      for (const auto &Arg : llvm::ArrayRef(A).drop_front())
        Op.Types.push_back(type(Arg));
      return Op;
    }
    if (N.K == Node::Member) {
      Op.Name = "." + N.Text;
      Op.Types.push_back(type(A.front()));
      if (N.Definition && llvm::StringRef(Op.Types.front()).ends_with("*"))
        Op.Types.front().pop_back();
      return Op;
    }
    if (N.K == Node::Index)
      Op.Name = "[]";
    else if (needsWitness(N))
      Op.Name = operatorKey(N);
    else
      return {};
    for (const auto &Arg : A)
      Op.Types.push_back(type(Arg));
    if (Op.Name == "=")
      Op.Assignment = {assignmentKind(A[0], Scope),
                       assignmentKind(A[1], Scope)};
    return Op;
  }

  Alternatives refine(const Node &Q, bool True, Alternatives Alts,
                      const Bindings &Args = {}, unsigned Depth = 0) {
    step(Q.At);
    if (Depth > 128)
      throw ResourceExhausted{
          {Q.At, "constraint normalization nesting resource exhausted"}};
    if (Q.K == Node::Name && (Q.Text == "true" || Q.Text == "false"))
      return (Q.Text == "true") == True ? Alts : Alternatives{};
    if (Q.K == Node::Unary && Q.Text == "!")
      return refine(Q.Children.front(), !True, std::move(Alts), Args,
                    Depth + 1);
    if (Q.K == Node::Binary && (Q.Text == "&&" || Q.Text == "||")) {
      if ((Q.Text == "&&") == True) {
        Alts = refine(Q.Children[0], True, std::move(Alts), Args, Depth + 1);
        return refine(Q.Children[1], True, std::move(Alts), Args, Depth + 1);
      }
      auto Other = refine(Q.Children[1], True, Alts, Args, Depth + 1);
      Alts = refine(Q.Children[0], True, std::move(Alts), Args, Depth + 1);
      if (Alts.size() + Other.size() > U.Opt.MaxNormalNodes)
        throw ResourceExhausted{
            {Q.At, "generic normalization resource exhausted"}};
      Alts.insert(Alts.end(), Other.begin(), Other.end());
      return Alts;
    }
    if (Q.K != Node::Name)
      return Alts;
    if (Q.Text == "SameType" && Q.TemplateArgs.size() == 2) {
      const auto &Left = Q.TemplateArgs[0].Type;
      const auto &Right = Q.TemplateArgs[1].Type;
      auto L = substitute(Left, Args), R = substitute(Right, Args);
      // The value-type equivalence used for operations cannot prove an exact
      // type comparison between a symbolic type and a qualified version of it.
      if (L == R && Left != Right &&
          (valueType(Left) != Left || valueType(Right) != Right))
        return Alts;
      llvm::erase_if(Alts, [&](Domain &D) {
        auto X = representative(L, D), Y = representative(R, D);
        if (X == Y)
          return !True;
        if (!Parameters.count(X) && !Parameters.count(Y))
          return True && builtin(X) && builtin(Y);
        if (True) {
          if (!Parameters.count(X))
            std::swap(X, Y);
          D.Equal[X] = Y;
        }
        return false;
      });
      return Alts;
    }
    auto *C = Names.constraint(Q.Text);
    if (!C && Variables.count(Q.Text) && Variables.at(Q.Text) == "bool") {
      llvm::erase_if(Alts, [&](Domain &D) {
        auto [I, New] = D.Predicates.emplace(Q.Text, True);
        return !New && I->second != True;
      });
    }
    if (!True || !C)
      return Alts;
    Bindings Actual;
    for (size_t I = 0; I < C->Decl.Generics.size() && I < Q.TemplateArgs.size();
         ++I)
      if (C->Decl.Generics[I].K == Node::TypeParam)
        Actual[C->Decl.Generics[I].Text] =
            substitute(Q.TemplateArgs[I].Type, Args);
    llvm::SaveAndRestore Prefix(Names.Prefix, C->Prefix);
    llvm::SaveAndRestore Visibility(Names.LookupLimit, C->Site.Through);
    for (auto &R : C->Decl.Children) {
      if (R.Text == "requires") {
        Alts = refine(R.Children.front(), true, std::move(Alts), Actual,
                      Depth + 1);
        continue;
      }
      Bindings Locals;
      for (auto &P : R.Params)
        Locals[P.Text] = P.Type;
      for (auto &E : R.Children) {
        if (auto Op = operation(E, Locals, [&](const Node &N) {
              return substitute(operand(N, Locals), Actual);
            }))
          for (auto &D : Alts)
            D.Operations[*Op] = substitute(E.Type, Actual);
      }
    }
    return Alts;
  }
  std::string visit(const Node &N, const Alternatives &Alts) {
    if (Alts.empty())
      return "";
    if (N.K == Node::Block || N.K == Node::For || N.K == Node::Lambda) {
      llvm::SaveAndRestore Scope(Variables);
      for (auto &P : N.Params)
        Variables[P.Text] = P.Type;
      for (auto &C : N.Children)
        visit(C, Alts);
      return "";
    }
    if (N.K == Node::If && N.Required) {
      visit(N.Children[0], Alts);
      visit(N.Children[1], refine(N.Children[0], true, Alts));
      if (N.Children.size() > 2)
        visit(N.Children[2], refine(N.Children[0], false, Alts));
      return "";
    }
    if (N.K == Node::Call && N.Children.front().K == Node::Name) {
      auto Callee = operand(N.Children.front(), Variables);
      auto Function = llvm::StringRef(Callee);
      if (Function.consume_back("*"))
        if (auto Signature = splitCallableType(Function)) {
          auto ParamTypes = splitArguments(Signature->Parameters);
          auto Arguments = llvm::ArrayRef(N.Children).drop_front();
          if (ParamTypes.size() != Arguments.size())
            fail(N.At, "function pointer argument arity is not established");
          for (size_t I = 0; I < Arguments.size(); ++I) {
            auto Parameter = llvm::StringRef(ParamTypes[I]);
            if (Parameter.consume_back("...") != Arguments[I].Pack)
              fail(Arguments[I].At,
                   "function pointer pack shape is not established");
            auto Actual = visit(Arguments[I], Alts);
            auto Expected = valueType(Parameter.str());
            if (Actual.empty())
              continue;
            for (const auto &Facts : Alts) {
              auto A = representative(Actual, Facts);
              auto E = representative(Expected, Facts);
              if (A != E && (Parameters.count(A) || Parameters.count(E)))
                fail(Arguments[I].At,
                     "function pointer argument type is not established");
            }
          }
          return valueType(Signature->Result.str());
        }
    }
    // A constructor's first write to a slot can start its lifetime. The
    // specialized construction plan identifies those writes before lowering.
    auto Op = InConstructor && N.K == Node::Binary && N.Text == "="
                  ? std::optional<Operation>{}
                  : operation(N, Variables,
                              [&](const Node &C) { return visit(C, Alts); });
    if (!Op) {
      std::string First;
      for (size_t I = 0; I < N.Children.size(); ++I) {
        auto T = visit(N.Children[I], Alts);
        if (!I)
          First = T;
      }
      if (N.K == Node::Object)
        Variables[N.Text] = N.Type == "auto" ? First : N.Type;
      return operand(N, Variables);
    }
    const auto &Types = Op->Types;
    if (llvm::any_of(Types, [](const auto &T) { return T.empty(); }))
      return "";
    bool Boolean = N.Text == "!" || N.Text == "==" || N.Text == "!=" ||
                   N.Text == "<" || N.Text == ">" || N.Text == "<=" ||
                   N.Text == ">=";
    bool Intrinsic = needsWitness(N);
    std::string Result;
    for (const auto &D : Alts) {
      bool Dependent = llvm::any_of(Types, [&](const auto &T) {
        return Parameters.count(representative(T, D));
      });
      if (!Dependent)
        continue;
      auto W = llvm::find_if(D.Operations, [&](const auto &Entry) {
        const auto &Other = Entry.first;
        if (Other.Name != Op->Name || Other.Types.size() != Types.size())
          return false;
        for (size_t I = 0; I < Types.size(); ++I)
          if (representative(Other.Types[I], D) != representative(Types[I], D))
            return false;
        if (Op->Name == "=") {
          if (Op->Assignment[0] != AssignmentKind::LValue ||
              Other.Assignment[0] != AssignmentKind::LValue ||
              Op->Assignment[1] == AssignmentKind::Unknown)
            return false;
          return Other.Assignment[1] == Op->Assignment[1] ||
                 (Other.Assignment[1] == AssignmentKind::ConstLValue &&
                  Op->Assignment[1] == AssignmentKind::LValue &&
                  representative(Types[0], D) == representative(Types[1], D));
        }
        return true;
      });
      if (W == D.Operations.end())
        fail(N.At, "dependent operation '" + Op->Name +
                       "' is not established by the declared constraints");
      Result = W->second;
    }
    if (!Result.empty())
      return Result;
    if (!Intrinsic)
      return "";
    return Boolean                                     ? "bool"
           : Types.size() > 1 && Types[0] == "integer" ? Types[1]
                                                       : Types[0];
  }

  // Resolve lexical names immediately. A dependent base or type application
  // may supply its own members only after substitution.
  bool predicateName(const Node &N, const Node &Decl, const Node *Owner,
                     llvm::StringRef OwnerType, bool HasReceiver) {
    auto Name = llvm::StringRef(N.Text);
    if (Name == "this")
      return HasReceiver;
    auto RootName = Name;
    RootName.consume_front("::");
    if (RootName == "std::to_underlying" ||
        RootName == "std::from_underlying" ||
        RootName == "std::try_from_underlying")
      return true;
    if (Name == "true" || Name == "false" || Name == "nullptr" ||
        Name == "std::move" || Name == "std::forward" ||
        builtinPredicate(Name) || builtin(Name) || Names.constraint(N.Text) ||
        Variables.count(N.Text) || Names.Env.Values.count(N.Text))
      return true;
    if (Name == "return_value")
      return false;
    auto Head = Name.take_until([](char C) { return C == ':' || C == '<'; });
    if (Parameters.count(Head.str()) || Names.Env.Types.count(Head.str()) ||
        llvm::any_of(Decl.Generics,
                     [&](const Node &P) { return P.Text == Head; }))
      return true;
    if (Name == Decl.Text && Decl.K == Node::Function)
      return true;
    if (Owner && (Name == Owner->Text ||
                  llvm::any_of(Owner->Children,
                               [&](const Node &D) { return D.Text == Name; })))
      return true;
    if (!OwnerType.empty() && (U.lookupPath(OwnerType.str(), N.At, false) ||
                               U.lookupPath(OwnerType.str(), N.At, true)))
      return true;
    auto Visible = [&](const std::string &Key) {
      auto F = U.FunctionFamilies.find(Key);
      return U.Globals.count(Key) || U.Cases.count(Key) ||
             U.Aliases.count(Key) || U.Records.count(Key) ||
             !Names.visibleOverloads(Key).empty() ||
             (F != U.FunctionFamilies.end() &&
              llvm::any_of(F->second, [&](const auto &Family) {
                return Family.Site.Through <= Names.LookupLimit;
              }));
    };
    if (!scopeKey(Names.Prefix, Name, Visible).empty())
      return true;
    // A qualified designator may have a nominal dependent owner. Retain the
    // owner binding and defer its member lookup, including applied families.
    auto Nominal = Name.contains('<')    ? Name.split('<').first
                   : Name.contains("::") ? Name.rsplit("::").first
                                         : llvm::StringRef{};
    if (!Nominal.empty() &&
        !scopeKey(Names.Prefix, Nominal, [&](const std::string &Key) {
           return U.Records.count(Key) || U.Aliases.count(Key) ||
                  U.Families.count(Key);
         }).empty())
      return true;
    return HasReceiver && Owner && OwnerType.empty() &&
           !Owner->TemplateArgs.empty() && !Name.contains("::");
  }

  void bindPredicateNames(const Node &N, const Node &Decl, const Node *Owner,
                          llvm::StringRef OwnerType, bool HasReceiver) {
    if (N.K == Node::Name &&
        !predicateName(N, Decl, Owner, OwnerType, HasReceiver))
      fail(N.At, "unknown name '" + N.Text + "' in contract predicate");
    for (const auto &C : N.Children)
      bindPredicateNames(C, Decl, Owner, OwnerType, HasReceiver);
    for (const auto &A : N.TemplateArgs)
      bindPredicateNames(A, Decl, Owner, OwnerType, HasReceiver);
  }
};
} // namespace

void Context::checkDomain(const Node &N, const std::string &Prefix,
                          const Node *SymbolOwner) {
  Checker Check(*this, Prefix);
  const bool Record = N.K == Node::Record || N.K == Node::Union;
  std::string OwnerType = llvm::StringRef(Prefix).rtrim(':').str();
  if (auto Owner = Records.find(OwnerType); !Record && Owner != Records.end()) {
    SymbolOwner = &Owner->second.Decl;
    Check.Names.Env = Owner->second.Env;
  } else
    OwnerType.clear();
  if (Record && !SymbolOwner)
    SymbolOwner = &N;
  auto Callable = [](const Node &D) {
    return D.K == Node::Function || D.K == Node::Constructor ||
           D.K == Node::Destructor;
  };
  if (Record)
    for (const auto &D : N.Children)
      if (Callable(D))
        (void)genericEffectBound(D, !D.Settings.count("static"));
  for (auto &P : N.Generics) {
    if (P.K == Node::TypeParam)
      Check.Parameters.insert(P.Text);
    else
      Check.Variables[P.Text] = P.Type;
  }
  bool Dependent = !Check.Parameters.empty();
  Alternatives Alts(1);
  const auto &Conditions = Record ? N.Params : N.TemplateArgs;
  if (Dependent)
    for (auto &Q : Conditions)
      Alts = Check.refine(Q, true, std::move(Alts));
  auto Body = [&](const Node &D) {
    llvm::SaveAndRestore Scope(Check.Variables);
    llvm::SaveAndRestore Constructor(Check.InConstructor,
                                     D.K == Node::Constructor);
    for (auto &P : D.Params)
      Check.Variables[P.Text] = P.Type;
    for (const auto &Clause : D.Contracts) {
      llvm::SaveAndRestore Names(Check.Variables);
      if (Clause.Text == "ensures" && D.Type != "void" && D.Type != "never")
        Check.Variables["return_value"] = D.Type;
      bool HasReceiver =
          SymbolOwner && !D.Settings.count("static") &&
          !(D.K == Node::Constructor && Clause.Text == "requires");
      Check.bindPredicateNames(Clause.Children.front(), D, SymbolOwner,
                               OwnerType, HasReceiver);
      if (Dependent)
        Check.visit(Clause.Children.front(), Alts);
    }
    if (Dependent && N.K != Node::Union)
      for (auto &C : D.Children)
        Check.visit(C, Alts);
  };
  if (N.K == Node::Function)
    Body(N);
  if (Record) {
    for (auto &D : N.Children)
      if (D.K == Node::Field)
        Check.Variables[D.Text] = D.Type;
    for (auto &Clause : N.Contracts) {
      Check.bindPredicateNames(Clause.Children.front(), N, SymbolOwner,
                               OwnerType, true);
      if (Dependent)
        Check.visit(Clause.Children.front(), Alts);
    }
    for (auto &D : N.Children)
      if (Callable(D))
        Body(D);
  }
}
