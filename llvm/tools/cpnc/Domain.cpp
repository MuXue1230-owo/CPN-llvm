#include "Sema.h"
using namespace cpn;
namespace {
using Bindings = std::map<std::string, std::string>;
using Operation = std::pair<std::string, std::vector<std::string>>;
struct Domain {
  Bindings Equal;
  std::map<std::string, bool> Predicates;
  std::map<Operation, std::string> Operations;
};
using Alternatives = std::vector<Domain>;

bool needsWitness(const Node &N) {
  static const std::set<std::string> Binary = {
      "+",   "-",   "*",  "/",  "%",  "|",  "&",  "^",  "<<",
      ">>",  "+=",  "-=", "*=", "/=", "%=", "|=", "&=", "^=",
      "<<=", ">>=", "==", "!=", "<",  ">",  "<=", ">="};
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

  // A method designator is bound together with its arguments. It does not
  // independently require a data field with the same spelling.
  template <class Child>
  static std::optional<Operation> operation(const Node &N,
                                            const Bindings &Scope, Child type) {
    const auto &A = N.Children;
    Operation Op;
    if (N.K == Node::Call) {
      const auto &C = A.front();
      if (C.K == Node::Member) {
        Op.first = "." + C.Text + "()";
        Op.second.push_back(type(C.Children.front()));
        if (C.Definition && llvm::StringRef(Op.second.front()).ends_with("*"))
          Op.second.front().pop_back();
      } else if (C.K == Node::Name && Scope.count(C.Text)) {
        Op.first = "()";
        Op.second.push_back(type(C));
      } else
        return {};
      for (const auto &Arg : llvm::ArrayRef(A).drop_front())
        Op.second.push_back(type(Arg));
      return Op;
    }
    if (N.K == Node::Member) {
      Op.first = "." + N.Text;
      Op.second.push_back(type(A.front()));
      if (N.Definition && llvm::StringRef(Op.second.front()).ends_with("*"))
        Op.second.front().pop_back();
      return Op;
    }
    if (N.K == Node::Index)
      Op.first = "[]";
    else if (needsWitness(N))
      Op.first = operatorKey(N);
    else
      return {};
    for (const auto &Arg : A)
      Op.second.push_back(type(Arg));
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
      auto L = substitute(Q.TemplateArgs[0].Type, Args),
           R = substitute(Q.TemplateArgs[1].Type, Args);
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
        Locals[P.Text] = substitute(P.Type, Actual);
      for (auto &E : R.Children) {
        if (auto Op = operation(
                E, Locals, [&](const Node &N) { return operand(N, Locals); }))
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
    auto Op =
        operation(N, Variables, [&](const Node &C) { return visit(C, Alts); });
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
    const auto &Types = Op->second;
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
        if (Other.first != Op->first || Other.second.size() != Types.size())
          return false;
        for (size_t I = 0; I < Types.size(); ++I)
          if (representative(Other.second[I], D) != representative(Types[I], D))
            return false;
        return true;
      });
      if (W == D.Operations.end())
        fail(N.At, "dependent operation '" + Op->first +
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
};
} // namespace

void Context::checkDomain(const Node &N, const std::string &Prefix) {
  Checker Check(*this, Prefix);
  for (auto &P : N.Generics) {
    if (P.K == Node::TypeParam)
      Check.Parameters.insert(P.Text);
    else
      Check.Variables[P.Text] = P.Type;
  }
  if (Check.Parameters.empty())
    return;
  Alternatives Alts(1);
  const auto &Conditions = N.K == Node::Record ? N.Params : N.TemplateArgs;
  for (auto &Q : Conditions)
    Alts = Check.refine(Q, true, std::move(Alts));
  auto Body = [&](const Node &D) {
    llvm::SaveAndRestore Scope(Check.Variables);
    for (auto &P : D.Params)
      Check.Variables[P.Text] = P.Type;
    for (auto &C : D.Children)
      Check.visit(C, Alts);
  };
  if (N.K == Node::Function)
    Body(N);
  if (N.K == Node::Record) {
    for (auto &D : N.Children)
      if (D.K == Node::Field)
        Check.Variables[D.Text] = D.Type;
    for (auto &D : N.Children)
      if (D.K == Node::Function || D.K == Node::Constructor ||
          D.K == Node::Destructor)
        Body(D);
  }
}
