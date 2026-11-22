#include "Frontend.h"
#include "llvm/ADT/StringExtras.h"
#include <algorithm>

using namespace cpn;
using llvm::StringRef;
namespace {
const std::set<std::string> Reserved = {
    "alias",         "alignof",    "async",    "auto",         "await",
    "break",         "case",       "catch",    "class",        "cleanup",
    "configuration", "configured", "const",    "consteval",    "constexpr",
    "constraint",    "continue",   "declare",  "decltype",     "default",
    "define",        "delegate",   "delete",   "do",           "else",
    "enum",          "extern",     "false",    "fallthrough",  "for",
    "forward",       "function",   "generic",  "goto",         "if",
    "import",        "init",       "match",    "mutable",      "namespace",
    "noexcept",      "nullptr",    "operator", "private",      "protected",
    "public",        "requires",   "return",   "sizeof",       "static",
    "struct",        "switch",     "this",     "thread_local", "throw",
    "true",          "try",        "typefn",   "union",        "virtual",
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
  std::vector<Token> Tokens;
  size_t Pos = 0;
  std::set<std::string> Types;
  std::map<std::string, std::vector<Node>> Families;
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
    return Tokens[std::min(Pos + N, Tokens.size() - 1)];
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
  Token qualified() {
    auto T = take();
    while (eat("::")) {
      if (is("forward") && T.Text == "std")
        T.Text += "::" + take().Text;
      else
        T.Text += "::" + name().Text;
    }
    return T;
  }
  bool known(StringRef S) const {
    return builtin(S) || Types.count(S.str()) || S == "const" ||
           S == "function";
  }
  std::string spelling(size_t Start) const {
    std::string S;
    for (size_t I = Start; I < Pos; ++I)
      S += Tokens[I].Text;
    return S;
  }
  void closeAngle() {
    if (is(">>")) {
      Tokens[Pos].Text = ">";
      ++Tokens[Pos].Column;
    } else
      expect(">");
  }
  std::vector<Node> templateArgs(const std::string &Name) {
    expect("<");
    std::vector<Node> Out;
    if (eat(">"))
      return Out;
    auto It = Families.find(Name);
    do {
      size_t I = Out.size();
      bool T = It != Families.end() && !It->second.empty()
                   ? It->second[std::min(I, It->second.size() - 1)].K ==
                         Node::TypeParam
                   : known(peek().Text);
      if (T) {
        Node A(Node::TypeArg, peek());
        A.Type = type();
        Out.push_back(A);
      } else
        Out.push_back(expr(1, true));
      Out.back().Pack = eat("...");
    } while (eat(","));
    closeAngle();
    return Out;
  }
  std::string type() {
    Nest Guard(Depth, peek());
    auto T = peek();
    std::string S;
    if (eat("(")) {
      S = type();
      expect(")");
    } else if (eat("const")) {
      expect("<");
      S = "const<" + type() + ">";
      closeAngle();
    } else if (eat("function")) {
      expect("<");
      S = "function<" + type() + "(";
      expect("(");
      bool First = true;
      if (!eat(")")) {
        do {
          if (!First)
            S += ",";
          First = false;
          S += type();
          if (identifier(peek().Text))
            name();
          if (is("("))
            fail(peek(), "callable type cannot contain a parameter default");
        } while (eat(","));
        expect(")");
      }
      S += ")";
      if (eat("noexcept"))
        S += " noexcept";
      closeAngle();
      S += ">";
    } else if (eat("forward")) {
      S = "forward " + type();
    } else {
      S = qualified().Text;
      if (!known(S))
        fail(T, "unsupported or unknown type '" + S + "'");
      if (is("<") && Families.count(S)) {
        size_t Begin = Pos;
        templateArgs(S);
        S += spelling(Begin);
      }
    }
    for (;;) {
      if (is("*") || is("&") || is("&&"))
        S += take().Text;
      else if (eat("[")) {
        size_t Begin = Pos;
        expr();
        S += "[" + spelling(Begin) + "]";
        expect("]");
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
    } else if (is("+") || is("-") || is("!") || is("~") || is("&") || is("*") ||
               is("++") || is("--")) {
      N = Node(Node::Unary, take());
      N.Children.push_back(expr(13, InAngle));
    } else if (eat("[")) {
      N = Node(Node::Lambda, T);
      std::set<std::string> Captures;
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
          N.TemplateArgs.push_back(std::move(Capture));
        } while (eat(","));
        expect("]");
      }
      if (eat("async"))
        fail(T, "async closures require asynchronous execution");
      N.Type = type();
      N.Params = params();
      N.Const = !eat("mutable");
      N.Noexcept = eat("noexcept");
      N.Children = {block()};
    } else if (eat("configured")) {
      N = Node(Node::Configured, T);
      N.Settings = settings(false);
      expect("(");
      N.Children.push_back(expr());
      expect(")");
    } else if (is("sizeof") || is("alignof")) {
      N = Node(Node::Unary, take());
      expect("(");
      if (known(peek().Text)) {
        Node Ty(Node::TypeArg, peek());
        Ty.Type = type();
        N.Children.push_back(Ty);
      } else
        N.Children.push_back(expr());
      expect(")");
    } else if (!T.Text.empty() && llvm::isDigit(T.Text[0]))
      N = Node(realToken(T.Text) ? Node::Real : Node::Number, take());
    else if (!T.Text.empty() && (T.Text[0] == '\'' || T.Text[0] == '"'))
      N = Node(T.Text[0] == '\'' ? Node::Character : Node::String, take());
    else if (identifier(T.Text)) {
      if (Reserved.count(T.Text) && T.Text != "true" && T.Text != "false" &&
          T.Text != "nullptr" && T.Text != "this")
        fail(T, "expected expression");
      N = Node(Node::Name, qualified());
      if (is("<") && (Families.count(N.Text) || builtinPredicate(N.Text) ||
                      N.Text == "destroy_base" || N.Text == "abandon_base" ||
                      N.Text == "construct_at" || N.Text == "std::forward")) {
        N.ExplicitApplication = true;
        N.TemplateArgs = templateArgs(N.Text);
      }
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
        auto Id = name();
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
  std::map<std::string, std::string> settings(bool File) {
    expect(File ? "{" : "(");
    std::map<std::string, std::string> M;
    while (!eat(File ? "}" : ")")) {
      auto K = take();
      while (eat("."))
        K.Text += "." + take().Text;
      expect("=");
      if (M.count(K.Text))
        fail(K, "duplicate configuration key");
      std::string V;
      if (eat("[")) {
        V = "[";
        while (!eat("]")) {
          if (is("["))
            fail(peek(), "CFG001: invalid nested configuration list");
          V += take().Text;
        }
        V += "]";
      } else
        V = take().Text;
      M[K.Text] = V;
      if (File)
        expect(";");
      else if (!eat(",")) {
        expect(")");
        break;
      }
    }
    return M;
  }
  Node block(bool Construction = false) {
    Nest Guard(Depth, peek());
    Node B(Node::Block, expect("{"));
    while (!eat("}")) {
      if (Construction && eat("init")) {
        Node I(Node::Init, take());
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
    return B;
  }
  Node object(Token T, std::string Ty, bool RO, bool CX) {
    Node O(Node::Object, T);
    O.Type = std::move(Ty);
    O.Const = RO || CX;
    O.Required = CX;
    O.HasInitializer = is("(");
    if (O.HasInitializer)
      O.Children = args();
    if (O.Type == "auto" && O.Children.size() != 1)
      fail(T, "auto requires a single initializer");
    if (eat("->")) {
      if (O.Type == "auto")
        fail(T, "a construction tail requires a typed declaration");
      auto B = block(true);
      B.K = Node::Tail;
      O.Children.push_back(std::move(B));
    }
    expect(";");
    return O;
  }
  bool startsType() const {
    auto S = peek().Text;
    for (size_t I = 1; peek(I).Text == "::"; I += 2)
      S += "::" + peek(I + 1).Text;
    return known(S);
  }
  Node simple() {
    if (is("static") || is("thread_local")) {
      auto Storage = take();
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
    bool CX = eat("constexpr");
    if (RO || CX || is("auto") || (startsType() && peek(1).Text != "(")) {
      auto Ty = eat("auto") ? std::string("auto") : type();
      auto Id = name();
      return object(Id, Ty, RO, CX);
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
    if (eat("if")) {
      Node N(Node::If, T);
      N.Required = eat("constexpr");
      N.Children = {condition(), block()};
      if (eat("else"))
        N.Children.push_back(is("if") ? statement() : block());
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
      Node N(Node::For, T);
      expect("(");
      N.Children = {simple(), is(";") ? Node() : expr()};
      expect(";");
      N.Children.push_back(is(")") ? Node() : expr());
      expect(")");
      N.Children.push_back(block());
      return N;
    }
    if (eat("match")) {
      Node N(Node::Match, T);
      N.Children = {condition()};
      expect("{");
      while (!eat("}")) {
        expect("case");
        Node Arm(Node::Arm, qualified());
        if (eat("(")) {
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
      N.Text = is(";") ? "" : name().Text;
      expect(";");
      return N;
    }
    if (eat("configured")) {
      Node N(Node::Configured, T);
      N.Settings = settings(false);
      if (is("{"))
        N.Children = {block()};
      else {
        N.Children = {simple()};
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
      if (N.Children[0].K == Node::Object)
        fail(L, "a label requires a statement");
      return N;
    }
    return simple();
  }
  std::vector<Node> params() {
    expect("(");
    std::vector<Node> V;
    if (eat(")"))
      return V;
    do {
      Node P(Node::Parameter, peek());
      P.Const = is("const") && peek(1).Text != "<";
      if (P.Const)
        take();
      P.Type = type();
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
      if (is("("))
        P.Children = args();
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
    return peek(I).Text == "{" || peek(I).Text == "=";
  }
  std::vector<Node> generic() {
    std::vector<Node> G;
    expect("<");
    do {
      auto T = peek();
      Node P(Node::TypeParam, T);
      if (!eat("type")) {
        expect("const");
        P.K = Node::ValueParam;
        P.Type = type();
      }
      P.Pack = eat("...");
      P.At = name();
      P.Text = P.At.Text;
      if (P.K == Node::TypeParam)
        Types.insert(P.Text);
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
  Node declaration(bool Foreign = false, bool Member = false) {
    Nest Guard(Depth, peek());
    auto T = peek();
    if (eat("configured")) {
      Node Policy(Node::Configured, T);
      Policy.Settings = settings(false);
      auto D = declaration(Foreign, Member);
      D.Policies.insert(D.Policies.begin(), std::move(Policy));
      return D;
    }
    if (is("[") && peek(1).Text == "[") {
      std::map<std::string, std::string> Attr;
      while (eat("[")) {
        expect("[");
        do {
          auto Key = take();
          if (Key.Text != "static_id" && Key.Text != "init_after")
            fail(Key, "unsupported attribute");
          expect("(");
          auto V = Key.Text == "static_id" ? unquote(take()) : qualified().Text;
          expect(")");
          if (!Attr.emplace(Key.Text, V).second)
            fail(Key, "duplicate attribute");
        } while (eat(","));
        expect("]");
        expect("]");
      }
      auto D = declaration(Foreign, Member);
      if (D.K != Node::Object)
        fail(T, "static attribute requires an object");
      D.Settings.insert(Attr.begin(), Attr.end());
      return D;
    }
    if (eat("configuration")) {
      Node N(Node::Config, T);
      N.Settings = settings(true);
      expect(";");
      return N;
    }
    if (eat("namespace") || eat("extern")) {
      bool NS = T.Text == "namespace";
      Node N(NS ? Node::Namespace : Node::Linkage, T);
      if (NS)
        N.Text = name().Text;
      else
        expect("\"C\"");
      if (eat("{")) {
        while (!eat("}"))
          N.Children.push_back(declaration(Foreign || !NS));
      } else if (!NS)
        N.Children.push_back(declaration(true));
      else
        fail(T, "expected '{'");
      if (NS) {
        for (auto &C : N.Children) {
          auto Key = N.Text + "::" + C.Text;
          if (C.K == Node::Record || C.K == Node::Alias ||
              C.K == Node::Enumeration || C.K == Node::Union)
            Types.insert(Key);
          if (!C.Generics.empty())
            Families[Key] = C.Generics;
        }
      }
      return N;
    }
    if (eat("constraint")) {
      Node N(Node::Constraint, name());
      auto Saved = Types;
      N.Generics = generic();
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
          Rule.Params = params();
          expect("{");
          while (!eat("}")) {
            size_t End = Pos, Arrow = Tokens.size();
            unsigned D = 0;
            while (End < Tokens.size() && !(Tokens[End].Text == ";" && !D)) {
              auto &W = Tokens[End].Text;
              if (W == "->" && !D)
                Arrow = End;
              D += (W == "(" || W == "[");
              D -= (W == ")" || W == "]");
              ++End;
            }
            if (Arrow == Tokens.size())
              fail(peek(), "expression requirement needs a result type");
            Tokens[Arrow].Text = "$result";
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
      Types = std::move(Saved);
      return N;
    }
    if (eat("alias")) {
      Node N(Node::Alias, name());
      expect("=");
      N.Type = type();
      expect(";");
      Types.insert(N.Text);
      return N;
    }
    auto Saved = Types;
    std::vector<Node> G;
    if (eat("generic"))
      G = generic();
    Node Requires;
    if (eat("requires"))
      Requires = condition();
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
      return D;
    }
    if (is("struct") || is("class")) {
      bool Class = take().Text == "class";
      bool Manual = Class && eat("Manual");
      Node R(Node::Record, name());
      R.Generics = G;
      Types.insert(R.Text);
      if (!G.empty())
        Families[R.Text] = G;
      if (Requires.K != Node::Empty)
        R.Params.push_back(Requires);
      if (is(";"))
        fail(R.At, "incomplete declaration requires declare");
      if (Manual)
        R.Settings["manual"] = "1";
      if (eat("final"))
        R.Settings["final"] = "1";
      if (eat(":")) {
        do {
          Node B(Node::TypeArg, peek());
          B.Definition = eat("virtual");
          B.Type = type();
          R.TemplateArgs.push_back(B);
        } while (eat(","));
      }
      expect("{");
      std::string Access = Class ? "private" : "public";
      while (!eat("}")) {
        if (is("public") || is("private") || is("protected")) {
          Access = take().Text;
          expect(":");
          continue;
        }
        bool SpecialProto =
            is("declare") &&
            ((peek(1).Text == R.Text && peek(2).Text == "(") ||
             peek(1).Text == "~" ||
             (peek(1).Text == "virtual" && peek(2).Text == "~"));
        if (SpecialProto)
          take();
        bool Virt = eat("virtual");
        Node D;
        if (is("Complete")) {
          take();
          Node I(Node::Init, peek());
          I.Type = "Complete";
          if (!is(";")) {
            I.Text = take().Text;
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
          D.Params = params();
          if (Drop && !D.Params.empty())
            fail(D.At, "a destructor takes no parameters");
          D.Noexcept = eat("noexcept");
          if (eat("override"))
            D.Settings["override"] = "1";
          if (eat("final"))
            D.Settings["final"] = "1";
          if (SpecialProto) {
            expect(";");
            D.Prototype = true;
          } else if (eat("="))
            D.Settings["control"] = definitionControl();
          else {
            D.Children.push_back(block(!Drop));
            if (Drop && eat("cleanup"))
              D.Children.push_back(block());
          }
        } else {
          D = declaration(false, true);
          if (D.K == Node::Object)
            D.K = Node::Field;
        }
        if (Virt)
          D.Settings["virtual"] = "1";
        D.Settings["access"] = Access;
        R.Children.push_back(std::move(D));
      }
      expect(";");
      Types = std::move(Saved);
      Types.insert(R.Text);
      return R;
    }
    if (eat("union")) {
      Node R(Node::Union, name());
      Types.insert(R.Text);
      expect("{");
      while (!eat("}")) {
        bool Default = eat("default");
        expect("case");
        Node C(Node::Variant, name());
        C.Definition = Default;
        if (is("("))
          C.Params = params();
        expect(";");
        R.Children.push_back(std::move(C));
      }
      expect(";");
      return R;
    }
    if (eat("enum")) {
      Node E(Node::Enumeration, name());
      expect(":");
      E.Type = type();
      Types.insert(E.Text);
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
    if (Foreign && is("declare"))
      fail(peek(), "a foreign prototype uses its linkage declaration");
    if (!Foreign && is("define"))
      fail(peek(), "define requires an external object definition");
    bool Proto = eat("declare"), Def = eat("define");
    eat("static");
    bool RO = is("const") && peek(1).Text != "<";
    if (RO)
      take();
    bool CE = eat("constexpr"), Eval = eat("consteval");
    auto Ty = eat("auto") ? std::string("auto") : type();
    if (Member && eat("operator")) {
      auto Id = expect("=");
      Node F(Node::Function, Id);
      F.Text = "operator=";
      F.Type = Ty;
      F.Params = params();
      F.Noexcept = eat("noexcept");
      if (Proto) {
        expect(";");
        F.Prototype = true;
      } else if (eat("="))
        F.Settings["control"] = definitionControl();
      else
        F.Children.push_back(block());
      return F;
    }
    auto Id = name();
    bool Fn =
        !Def && (Proto || (Foreign && is("(")) || !G.empty() || functionBody());
    if (!Fn) {
      if (Foreign && !Def && !is(";"))
        fail(Id, "an external object initializer requires define");
      auto O = object(Id, Ty, RO, CE);
      O.Foreign = Foreign;
      O.Definition = Def;
      return O;
    }
    Node F(Node::Function, Id);
    F.Type = Ty;
    F.Generics = G;
    F.Foreign = Foreign;
    F.Required = CE || Eval;
    if (Eval)
      F.Settings["mode"] = "consteval";
    if (!G.empty())
      Families[Id.Text] = G;
    if (Requires.K != Node::Empty)
      F.TemplateArgs.push_back(std::move(Requires));
    F.Params = params();
    if (Member) {
      F.Const = eat("const");
      if (is("&") || is("&&"))
        F.Settings["category"] = take().Text;
    }
    F.Noexcept = eat("noexcept");
    if (Member && eat("override"))
      F.Settings["override"] = "1";
    if (Member && eat("final"))
      F.Settings["final"] = "1";
    if (Proto || (Foreign && is(";"))) {
      expect(";");
      F.Prototype = true;
    } else if (eat("=")) {
      F.Settings["control"] = definitionControl();
      if (F.Settings["control"] == "default")
        fail(F.At, "this function has no generated default definition");
    } else
      F.Children.push_back(block());
    Types = std::move(Saved);
    return F;
  }

public:
  explicit Parser(std::vector<Token> T) : Tokens(std::move(T)) {}
  std::vector<Node> unit() {
    std::vector<Node> V;
    while (!is(""))
      V.push_back(declaration());
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
std::vector<Node> cpn::parse(StringRef S, const Options &O) {
  return Parser(lex(S, O)).unit();
}
Node cpn::parseExpression(StringRef S, const Options &O) {
  return Parser(lex(S, O)).expression();
}
void cpn::configure(Options &O, const Node &N) {
  auto P = N.Settings.find("preset");
  if (P != N.Settings.end()) {
    auto V = P->second;
    if (V != "Debug" && V != "Release" && V != "MinimalDebug" &&
        V != "MinimalRelease")
      fail(N.At, "unknown preset");
    O.FPProfile = StringRef(V).ends_with("Debug") ? "strict" : "native";
    O.Overflow = StringRef(V).ends_with("Debug") ? "checked" : "native";
  }
  for (auto &KV : N.Settings) {
    auto &K = KV.first;
    auto &V = KV.second;
    if (K == "preset")
      continue;
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
      if (!floating(V))
        fail(N.At, "unsupported real default");
      O.DefaultReal = V;
      continue;
    }
    if (K == "numeric.literal.real_rounding") {
      static const std::set<std::string> Modes = {
          "nearest_ties_even", "nearest_ties_away", "toward_zero",
          "toward_positive_infinity", "toward_negative_infinity"};
      if (!Modes.count(V))
        fail(N.At, "unsupported literal rounding");
      O.LiteralRounding = V;
      continue;
    }
    if (K == "numeric.fp.profile") {
      if (V != "strict" && V != "native")
        fail(N.At, "unavailable floating profile");
      O.FPProfile = V;
      continue;
    }
    if (K == "numeric.float.formats") {
      if (V == "[]")
        O.FloatFormats.clear();
      else if (V == "[f32]")
        O.FloatFormats = {"f32"};
      else if (V == "[f64]")
        O.FloatFormats = {"f64"};
      else if (V == "[f32,f64]" || V == "[f64,f32]")
        O.FloatFormats = {"f32", "f64"};
      else
        fail(N.At, "unsupported floating format list");
      continue;
    }
    if (K == "numeric.integer.overflow") {
      if (V != "checked" && V != "native" && V != "wrapping" &&
          V != "saturating")
        fail(N.At, "unknown overflow policy");
      O.Overflow = V;
    } else if (K == "source.identifiers") {
      if (V != "ascii" && V != "unicode")
        fail(N.At, "unknown identifier profile");
      O.ASCII = V == "ascii";
    } else if (K == "numeric.literal.integer_default") {
      if (!builtin(V) || V.empty() || V[0] != 'i')
        fail(N.At, "invalid default integer");
      O.DefaultInt = V;
    } else if (K == "target") {
      if (V != "\"x86_64-linux-gnu\"")
        fail(N.At, "unsupported target");
    } else if (K == "numeric.integer.widths") {
      if (V != "[8,16,32,64]")
        fail(N.At, "unsupported integer width catalogue");
    } else if (K == "diagnostics.promote")
      O.Promote = V.find("WARNING") != std::string::npos;
    else if (K == "diagnostics.suppress") {
      if (V.find("LIFE") != std::string::npos ||
          V.find("ERROR") != std::string::npos)
        fail(N.At, "CFG001: mandatory error cannot be suppressed");
      O.Silence = V.find("WARNING") != std::string::npos;
    } else
      fail(N.At, "CFG002: unsupported configuration key '" + K + "'");
  }
}
