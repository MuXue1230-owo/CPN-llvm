//===-- Frontend.h - CPN26 syntax and native frontend -----------*- C++ -*-===//
#ifndef LLVM_TOOLS_CPNC_FRONTEND_H
#define LLVM_TOOLS_CPNC_FRONTEND_H

#include "llvm/ADT/StringRef.h"
#include <map>
#include <set>
#include <string>
#include <vector>

namespace llvm {
class Module;
}
namespace cpn {
struct Token {
  std::string Text;
  unsigned Line = 1, Column = 1;
};
struct Diagnostic {
  Token At;
  std::string Message;
};
[[noreturn]] inline void fail(const Token &At, const std::string &Message) {
  throw Diagnostic{At, Message};
}
struct ResourceExhausted : Diagnostic {};
struct Options {
  uint64_t MaxNormalNodes = 100000, MaxSolverSteps = 1000000,
           MaxInstantiations = 1000000;
  std::string Input, Output, Config, RootID;
  std::string FPProfile = "strict", DefaultReal = "f64",
              LiteralRounding = "nearest_ties_even";
  std::set<std::string> FloatFormats{"f32", "f64"};
  std::string Overflow = "checked", DefaultInt = "i32";
  bool ASCII = false, Promote = false, Silence = false, Check = false,
       IR = false;
  bool PromoteAbandon = false, SilenceAbandon = false;
  void warn(const Token &, llvm::StringRef) const;
};
std::vector<Token> lex(llvm::StringRef, const Options &);
std::string unquote(const Token &);
bool identifier(llvm::StringRef);
inline bool operatorSpelling(llvm::StringRef Name) {
  return Name.consume_front("operator") && !Name.empty() &&
         llvm::StringRef(" ([+-*/%~!&|^<=>").contains(Name.front());
}
bool builtin(llvm::StringRef);
bool builtinPredicate(llvm::StringRef);
bool realToken(llvm::StringRef);
bool floating(llvm::StringRef);
struct Node {
  enum Kind {
    Empty,
    Lambda,
    Capture,
    Name,
    Number,
    Real,
    Character,
    String,
    Call,
    Unary,
    Binary,
    Conditional,
    Index,
    Member,
    Block,
    Object,
    Expression,
    Return,
    If,
    While,
    Do,
    For,
    Break,
    Continue,
    Switch,
    Arm,
    Fallthrough,
    Label,
    Goto,
    Configured,
    Config,
    Function,
    Parameter,
    TypeParam,
    ValueParam,
    TypeArg,
    TypeQuery,
    Alias,
    Record,
    Field,
    Constructor,
    Destructor,
    DestructionOwner,
    Init,
    Delegate,
    Enumeration,
    Enumerator,
    Namespace,
    Linkage,
    Constraint,
    Requirement,
    Union,
    Variant,
    Match,
    Tail
  } K = Empty;
  Token At;
  std::string Text, Type;
  std::vector<Node> Children, Params, Generics, TemplateArgs, Policies, Pattern;
  std::map<std::string, std::string> Settings;
  bool HasInitializer = false, ExplicitApplication = false;
  bool Const = false, Required = false, Foreign = false, Prototype = false,
       Definition = false, Noexcept = false, Pack = false;
  Node() = default;
  Node(Kind K, Token At) : K(K), At(std::move(At)), Text(this->At.Text) {}
};
std::string borrowEffects(const std::set<unsigned> &NoEscape,
                          const std::set<unsigned> &Borrowed);
std::vector<Node> parse(llvm::StringRef, const Options &);
Node parseExpression(llvm::StringRef, const Options &);
void configure(Options &, const Node &);
void compile(llvm::Module &, const std::vector<Node> &, Options);
} // namespace cpn
#endif
