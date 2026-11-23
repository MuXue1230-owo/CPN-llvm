//===-- Frontend.h - CPN26 syntax and native frontend -----------*- C++ -*-===//
#ifndef LLVM_TOOLS_CPNC_FRONTEND_H
#define LLVM_TOOLS_CPNC_FRONTEND_H

#include "llvm/ADT/StringRef.h"
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace llvm {
class Module;
class APInt;
} // namespace llvm
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
enum class ConfigScope { Project, File, Declaration, Block, Expression };
enum class Severity { Info, Warning, Anomaly, Error, None };
struct Options {
  uint64_t MaxNormalNodes = 100000, MaxSolverSteps = 1000000,
           MaxInstantiations = 1000000;
  std::string Input, Output, Config, RootID;
  std::string FPProfile = "strict", FPRounding, DefaultReal = "f64",
              LiteralRounding = "nearest_ties_even";
  std::string InitialRounding, FPSubnormal, InitialSubnormal;
  std::optional<unsigned> FPTrapMask, FPInitialTraps;
  std::set<unsigned> IntegerWidths{8, 16, 32, 64};
  std::set<std::string> FloatFormats{"f32", "f64"};
  std::string Overflow = "checked", DefaultInt = "i32";
  bool ContractsEnabled = true, TrustedAssumptions = false;
  std::string ContractValidation = "check", InvariantValidation = "check";
  bool ASCII = false, Check = false, IR = false;
  bool CustomPreset = false;
  bool RawValidation = true;
  bool InterproceduralConstruction = true, InterproceduralEffects = true;
  bool StrictEffectDiagnostics = false;
  Severity Minimum = Severity::Warning;
  std::set<std::string> ExplicitConfiguration;
  std::set<std::string> Promote, Suppress;
  void diagnose(const Token &, Severity, llvm::StringRef Code,
                llvm::StringRef Message) const;
  void warn(const Token &, llvm::StringRef) const;
};
std::vector<Token> lex(llvm::StringRef, const Options &,
                       bool ExpandedPackNames = false);
std::string unquote(const Token &);
llvm::APInt integerLiteral(const Token &);
bool identifier(llvm::StringRef);
inline bool operatorSpelling(llvm::StringRef Name) {
  return Name.consume_front("operator") && !Name.empty() &&
         llvm::StringRef(" ([+-*/%~!&|^<=>").contains(Name.front());
}
bool builtin(llvm::StringRef);
bool builtinPredicate(llvm::StringRef);
bool integerLibraryName(llvm::StringRef, bool ExplicitDestination = false);
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
    Contract,
    Union,
    Variant,
    Match,
    Tail
  } K = Empty;
  Token At;
  std::string Text, Type;
  std::vector<Node> Children, Params, Generics, TemplateArgs, Policies, Pattern,
      Contracts;
  std::map<std::string, std::string> Settings;
  bool HasInitializer = false, ExplicitApplication = false, Grouped = false;
  bool Const = false, Required = false, Foreign = false, Prototype = false,
       Definition = false, Noexcept = false, Pack = false;
  Node() = default;
  Node(Kind K, Token At) : K(K), At(std::move(At)), Text(this->At.Text) {}
};
using EffectSet = std::set<std::string>;
bool usesNumericLibrary(const Node &);
using EffectBound = std::optional<EffectSet>;
EffectSet bindEffectNames(llvm::StringRef, const std::vector<Node> &,
                          bool HasReceiver, const Token &);
std::string effectFlags(const EffectBound &);
bool effectsFit(const EffectBound &Source, const EffectBound &Target);
std::string parameterEffects(const std::set<unsigned> &NoEscape,
                             const std::set<unsigned> &Borrowed,
                             const std::set<unsigned> &Consumes);
std::vector<Node> parse(llvm::StringRef, const Options &);
Node parseExpression(llvm::StringRef, const Options &);
void configure(Options &, const Node &, ConfigScope);
void compile(llvm::Module &, const std::vector<Node> &, Options);
} // namespace cpn
#endif
