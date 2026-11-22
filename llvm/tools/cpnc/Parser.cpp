#include "Frontend.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SaveAndRestore.h"
#include <algorithm>
#include <iterator>

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
  std::vector<Token> Tokens;
  size_t Pos = 0;
  std::set<std::string> Types, HiddenTypes, TypeParameters;
  void publishMemberNames(const Node &Owner, const std::string &Prefix) {
    for (const auto &C : Owner.Children) {
      auto Key = Prefix + C.Text;
      if (C.K == Node::Record || C.K == Node::Alias ||
          C.K == Node::Enumeration || C.K == Node::Union)
        Types.insert(Key);
      if (!C.Generics.empty() || C.K == Node::Constraint)
        Families[Key] = C.Generics;
      if (C.K == Node::Record || C.K == Node::Union || C.K == Node::Namespace)
        publishMemberNames(C, Key + "::");
    }
  }
  std::map<std::string, Node> TypeQueries;
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
  Token qualified(bool AllowBuiltin = false, Node *Application = nullptr) {
    bool Root = eat("::");
    auto T = Application && is("operator")          ? operatorName()
             : AllowBuiltin && builtin(peek().Text) ? take()
                                                    : name();
    std::string Schema = T.Text;
    while (true) {
      if (is("<") &&
          (Families.count(Schema) ||
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
        } else
          Args = templateArgs(Schema, &Canonical);
        if (!Application || is("::") || Types.count(Schema))
          T.Text += Canonical.empty() ? spelling(Start) : Canonical;
        else {
          Application->ExplicitApplication = true;
          Application->TemplateArgs = std::move(Args);
        }
      }
      if (!eat("::"))
        break;
      auto Next = Application && is("operator")      ? operatorName()
                  : is("forward") && T.Text == "std" ? take()
                                                     : name();
      T.Text += "::" + Next.Text;
      Schema += "::" + Next.Text;
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
      S += Tokens[I].Text;
    return S;
  }
  void closeAngle() {
    if (is(">>")) {
      Tokens[Pos].Text = ">";
      auto Second = Tokens[Pos++];
      ++Second.Column;
      Tokens.insert(Tokens.begin() + Pos, std::move(Second));
    } else
      expect(">");
  }
  std::vector<Node> templateArgs(const std::string &Name,
                                 std::string *Canonical = nullptr) {
    expect("<");
    if (Canonical)
      *Canonical = "<";
    std::vector<Node> Out;
    if (eat(">")) {
      if (Canonical)
        *Canonical += ">";
      return Out;
    }
    auto It = Families.find(Name);
    do {
      size_t I = Out.size(), Begin = Pos;
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
      if (Canonical) {
        if (I)
          *Canonical += ",";
        *Canonical += T ? Out.back().Type : spelling(Begin);
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
  std::string type() {
    Nest Guard(Depth, peek());
    auto T = peek();
    std::string S;
    if (eat("(")) {
      S = type();
      expect(")");
    } else if (eat("decltype")) {
      expect("(");
      Node Query(Node::TypeQuery, T);
      Query.Children.push_back(expr());
      expect(")");
      S = "$decltype." + std::to_string(T.Line) + "." +
          std::to_string(T.Column);
      Query.Text = S;
      TypeQueries[S] = std::move(Query);
    } else if (eat("const")) {
      expect("<");
      S = "const<" + type() + ">";
      closeAngle();
    } else if (eat("function")) {
      expect("<");
      auto Return = type();
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
      S = qualified(true).Text;
      if (!known(S) && !(StringRef(S).contains("::") &&
                         known(StringRef(S).split("::").first)))
        fail(T, "unsupported or unknown type '" + S + "'");
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
      N.Grouped = true;
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
      applyAttributes(N, attributes());
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
      N.At = qualified(true, &N);
      N.Text = N.At.Text;
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
          if (is("<") && Families.count(Id.Text)) {
            M.TemplateArgs = templateArgs(Id.Text);
            M.ExplicitApplication = true;
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
  Node block(bool Construction = false) {
    Nest Guard(Depth, peek());
    auto OuterTypes = Types;
    auto OuterHidden = HiddenTypes;
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
    if (O.HasInitializer)
      O.Children = args();
    if (O.Type == "auto" && O.Children.size() != 1)
      fail(T, "auto requires a single initializer");
    if (eat("->")) {
      O.HasInitializer = true;
      if (O.Type == "auto")
        fail(T, "a construction tail requires a typed declaration");
      auto B = block(true);
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
    bool CX = !RO && eat("constexpr");
    if (RO || CX || is("auto") || typeBefore(true)) {
      auto Ty = eat("auto") ? std::string("auto") : type();
      auto Id = name();
      if (Types.count(Id.Text))
        HiddenTypes.insert(Id.Text);
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
    if (is("alias") || is("struct") || is("class") || is("union") ||
        is("enum") ||
        (is("declare") &&
         (peek(1).Text == "struct" || peek(1).Text == "class" ||
          peek(1).Text == "union" || peek(1).Text == "enum")))
      return declaration();
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
      bool Forward = eat("forward");
      P.Type = type();
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
      if (P.K == Node::TypeParam) {
        Types.insert(P.Text);
        TypeParameters.insert(P.Text);
      }
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
  Token declarationName(std::string &Qualifier, bool &Dtor) {
    bool Root = eat("::");
    auto Id = is("operator") ? operatorName() : name();
    std::string Schema = Id.Text;
    for (;;) {
      auto Component = Id.Text;
      if (is("<") && Families.count(Schema)) {
        std::string Args;
        templateArgs(Schema, &Args);
        Component += Args;
        if (!is("::"))
          fail(peek(),
               "an applied declaration qualifier must name an owning scope");
      }
      if (!eat("::"))
        break;
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
    D.Params = params();
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
      D.Children.push_back(block(!Drop));
      if (Drop && eat("cleanup"))
        D.Children.push_back(block());
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
        else if (Key.Text == "static_id") {
          auto ID = take();
          if (!StringRef(ID.Text).starts_with("\""))
            fail(ID, "static_id requires a string literal");
          Value = unquote(ID);
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
    if (!Attrs.Contracts.empty()) {
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
      } else if (D.K != Node::Object)
        fail(D.At, "static attribute requires an object");
      if (!D.Settings.emplace(Key, Value).second)
        fail(D.At, "duplicate attribute");
    }
  }
  Node declaration(bool Foreign = false, bool Member = false) {
    llvm::SaveAndRestore Binders(TypeParameters);
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
      if (NS)
        publishMemberNames(N, N.Text + "::");
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
      HiddenTypes.erase(N.Text);
      return N;
    }
    auto Saved = Types;
    std::vector<Node> G;
    if (eat("generic"))
      G = generic();
    Node Requires;
    if (!G.empty() && eat("requires"))
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
    bool Specialize = eat("specialize");
    if (Specialize && !is("struct") && !is("class") && !is("union"))
      fail(peek(), "specialize requires a type family");
    if (is("struct") || is("class") || is("union")) {
      auto Kind = take().Text;
      bool Union = Kind == "union", Class = Kind == "class";
      bool Manual = Class && eat("Manual");
      Node R(Union ? Node::Union : Node::Record, name());
      R.Generics = G;
      if (Specialize) {
        while (eat("::"))
          R.Text += "::" + name().Text;
        if (!Families.count(R.Text))
          fail(R.At, "specialization must name an existing type family");
        R.Pattern = templateArgs(R.Text);
        R.Settings["specialize"] = "1";
      }
      Types.insert(R.Text);
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
            is("declare") &&
            ((peek(1).Text == R.Text && peek(2).Text == "(") ||
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
             D.Settings.count("init_cancel") ||
             D.Settings.count("init_effect")))
          fail(D.At, "static initialization metadata requires static storage");
        if (D.K == Node::Object)
          D.K = Node::Field;
        if (Virt)
          D.Settings["virtual"] = "1";
        D.Settings["access"] = Access;
        R.Children.push_back(std::move(D));
      }
      expect(";");
      Types = std::move(Saved);
      Types.insert(R.Text);
      publishMemberNames(R, R.Text + "::");
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
    if (!Member && !Foreign && separateSpecial()) {
      std::string Q;
      bool Dtor = false;
      auto Id = declarationName(Q, Dtor);
      Node D(Dtor ? Node::Destructor : Node::Constructor, Id);
      D.Settings["qualifier"] = Q;
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
    auto Ty = eat("auto") ? std::string("auto") : type();
    std::string Q;
    bool Dtor = false;
    auto Id = declarationName(Q, Dtor);
    if (Dtor || (!Q.empty() && (Member || Foreign || Proto || Def)))
      fail(Id, "invalid qualified declaration");
    bool Fn = !Def && (!Q.empty() || operatorSpelling(Id.Text) || Proto ||
                       (Foreign && is("(")) || !G.empty() || functionBody());
    if (!Fn) {
      if (Foreign && !Def && !is(";"))
        fail(Id, "an external object initializer requires define");
      if (Virtual || Eval || (Static && !StorageStatic) || (Foreign && Static))
        fail(Id, "invalid object declaration modifier");
      auto O = object(Id, Ty, RO, CE);
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
    if (Static)
      F.Settings["static"] = "1";
    if (Virtual)
      F.Settings["virtual"] = "1";
    F.Type = Ty;
    F.Generics = G;
    if (!Q.empty())
      F.Settings["qualifier"] = Q;
    F.Foreign = Foreign;
    F.Required = CE || Eval;
    if (Eval)
      F.Settings["mode"] = "consteval";
    if (!G.empty() && Q.empty())
      Families[Id.Text] = G;
    if (Requires.K != Node::Empty)
      F.TemplateArgs.push_back(std::move(Requires));
    F.Params = params();
    if ((Member && !Static) || !Q.empty()) {
      F.Const = eat("const");
      if (is("&") || is("&&"))
        F.Settings["category"] = take().Text;
    }
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
        if (Types.count(P.Text))
          HiddenTypes.insert(P.Text);
      F.Children.push_back(block());
      HiddenTypes = std::move(OuterHidden);
    }
    Types = std::move(Saved);
    return F;
  }

public:
  explicit Parser(std::vector<Token> T) : Tokens(std::move(T)) {}
  std::vector<Node> unit() {
    std::vector<Node> V;
    while (!is(""))
      V.push_back(declaration());
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
std::vector<Node> cpn::parse(StringRef S, const Options &O) {
  return Parser(lex(S, O)).unit();
}
Node cpn::parseExpression(StringRef S, const Options &O) {
  return Parser(lex(S, O)).expression();
}
void cpn::configure(Options &O, const Node &N, ConfigScope Scope) {
  auto P = N.Settings.find("preset");
  if (P != N.Settings.end()) {
    auto V = P->second;
    if (V != "Debug" && V != "Release" && V != "MinimalDebug" &&
        V != "MinimalRelease")
      fail(N.At, "unknown preset");
    O.ContractsEnabled = !StringRef(V).starts_with("Minimal");
    O.ContractValidation = V == "Debug" ? "check" : "document";
    O.InvariantValidation =
        !O.ContractsEnabled ? "disabled" : O.ContractValidation;
    O.TrustedAssumptions = false;
    O.InterproceduralConstruction = O.InterproceduralEffects =
        StringRef(V).ends_with("Debug");
    O.StrictEffectDiagnostics = false;
    O.FPProfile = StringRef(V).ends_with("Debug") ? "strict" : "native";
    O.Overflow = StringRef(V).ends_with("Debug") ? "checked" : "native";
  }
  for (auto &KV : N.Settings) {
    auto &K = KV.first;
    auto &V = KV.second;
    if (K == "preset")
      continue;
    if (K == "compilation.modules" || K == "compilation.separate" ||
        K == "tooling.contract_export") {
      if (V == "true")
        fail(N.At, "CFG002: " + K + " is unavailable");
      if (V != "false")
        fail(N.At, "CFG001: expected Boolean value for " + K);
    }
    if ((K == "target" || K == "source.identifiers" ||
         K == "source.unicode_version" || K == "compilation.modules" ||
         K == "compilation.separate" || K == "tooling.contract_export") &&
        Scope != ConfigScope::Project)
      fail(N.At, "CFG001: " + K +
                     " must be bound before source tokenization or binding");
    if ((K == "numeric.float.formats" || K == "numeric.integer.widths") &&
        Scope > ConfigScope::Declaration)
      fail(N.At,
           "CFG001: " + K + " cannot be overridden below declaration scope");
    if (K == "compilation.modules" || K == "compilation.separate" ||
        K == "tooling.contract_export")
      continue;
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
      if (V != "\"17.0.0\"")
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
      if (!floating(V))
        fail(N.At, "unsupported real default");
      O.DefaultReal = V;
      continue;
    }
    if (K == "numeric.fp.trap_mask" || K == "numeric.fp.initial_trap_mask") {
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
    if (K == "numeric.fp.relaxations") {
      if (V != "[]")
        fail(N.At,
             "CFG002: requested floating-point relaxations are unavailable");
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
      if (!builtin(V) || V.empty() || V[0] != 'i' || V == "isize")
        fail(N.At, "CFG001: invalid default integer");
      O.DefaultInt = V;
    } else if (K == "target") {
      if (V != "\"x86_64-linux-gnu\"")
        fail(N.At, "unsupported target");
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
          "LIFE003", "LIFE004", "GEN001", "NUM002",
          "NUM003",  "STAT002", "EXC001"};
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
  unsigned DefaultWidth = 0;
  StringRef(O.DefaultInt).drop_front().getAsInteger(10, DefaultWidth);
  if (!O.IntegerWidths.count(DefaultWidth))
    fail(N.At, "CFG002: literal default " + O.DefaultInt + " is disabled");
  if (N.Settings.count("numeric.literal.real_default") &&
      !O.FloatFormats.count(O.DefaultReal))
    fail(N.At, "CFG002: literal default " + O.DefaultReal + " is disabled");
}
