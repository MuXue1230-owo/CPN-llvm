#include "Sema.h"
#include <tuple>
using namespace cpn;
namespace {
using Bindings = std::map<std::string, std::string>;
using Operation = std::tuple<std::string, std::string, std::string>;
struct Domain {
  Bindings Equal;
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
      auto I = Scope.find(E.Text);
      return I == Scope.end() ? "" : valueType(I->second);
    }
    if (E.K == Node::Number)
      return "integer";
    if (E.K == Node::Real)
      return "real";
    if (E.K == Node::Call && E.Children[0].K == Node::Name &&
        (builtin(E.Children[0].Text) || Parameters.count(E.Children[0].Text)))
      return E.Children[0].Text;
    return "";
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
      for (auto &E : R.Children)
        if (needsWitness(E)) {
          Operation Op{operatorKey(E), operand(E.Children[0], Locals),
                       E.K == Node::Binary ? operand(E.Children[1], Locals)
                                           : ""};
          for (auto &D : Alts)
            D.Operations[Op] = substitute(E.Type, Actual);
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
    std::vector<std::string> Types;
    for (auto &C : N.Children)
      Types.push_back(visit(C, Alts));
    if (N.K == Node::Object)
      Variables[N.Text] =
          N.Type == "auto" && !Types.empty() ? Types.front() : N.Type;
    if (!needsWitness(N) || Types[0].empty() ||
        (N.K == Node::Binary && Types[1].empty()))
      return operand(N, Variables);
    auto A = Types[0], B = N.K == Node::Binary ? Types[1] : "";
    bool Boolean = N.Text == "!" || N.Text == "==" || N.Text == "!=" ||
                   N.Text == "<" || N.Text == ">" || N.Text == "<=" ||
                   N.Text == ">=";
    if (!Parameters.count(A) && !Parameters.count(B))
      return Boolean ? "bool" : A == "integer" && !B.empty() ? B : A;
    auto OpKey = operatorKey(N);
    std::string Result;
    for (const auto &D : Alts) {
      auto X = representative(A, D), Y = representative(B, D);
      // A concrete binding will undergo ordinary intrinsic/overload checking.
      if (!Parameters.count(X) && !Parameters.count(Y))
        continue;
      auto W = llvm::find_if(D.Operations, [&](auto &Entry) {
        auto &[Op, Left, Right] = Entry.first;
        return Op == OpKey && representative(Left, D) == X &&
               representative(Right, D) == Y;
      });
      if (W == D.Operations.end())
        fail(N.At, "dependent operation '" + N.Text +
                       "' is not established by the declared constraints");
      Result = W->second;
    }
    if (!Result.empty())
      return Result;
    return Boolean ? "bool" : Parameters.count(A) ? A : B;
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
