#ifndef LLVM_TOOLS_CPNC_SEMA_H
#define LLVM_TOOLS_CPNC_SEMA_H
#include "Frontend.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include <deque>
#include <optional>
namespace cpn {
struct Value {
  std::string Type;
  llvm::Value *IR = nullptr, *Address = nullptr;
  bool Readonly = false, Expiring = false;
  std::string Storage, RealText;
  llvm::Value *Generation = nullptr;
  bool BaseView = false;
  Value() = default;
  Value(std::string T, llvm::Value *V = nullptr, llvm::Value *A = nullptr,
        bool RO = false)
      : Type(std::move(T)), IR(V), Address(A), Readonly(RO) {}
};
struct Substitution {
  std::map<std::string, std::string> Types;
  std::map<std::string, Value> Values;
};
struct Function {
  Node Decl;
  std::string Name, Result, Owner, Prefix, DefaultPrefix;
  std::vector<std::string> Params;
  std::vector<Node> DefaultParams;
  Substitution Env;
  Options Configuration;
  llvm::Function *IR = nullptr;
  bool Emitting = false, Emitted = false;
  int Slot = -1;
};
struct Field {
  Node Decl;
  std::string Type;
};
struct Record {
  Node Decl;
  llvm::StructType *IR = nullptr;
  std::vector<Field> Fields;
  std::vector<std::string> Bases;
  Substitution Env;
  bool Complete = false, Polymorphic = false, VirtualDestructor = false;
  std::vector<Function *> Virtuals;
  std::vector<std::pair<uint64_t, llvm::GlobalVariable *>> Tables;
};
struct Case {
  std::string Owner;
  unsigned Tag, First;
  Node Decl;
  std::vector<std::string> Types;
};
struct Family {
  Node Decl;
  std::string Prefix;
};
struct Context {
  llvm::Module &M;
  llvm::LLVMContext &C;
  Options Opt;
  std::map<std::string, std::string> Aliases, Enums;
  std::map<std::string, Record> Records;
  std::map<std::string, Value> Globals, ExternalObjects;
  std::map<std::string, Function *> ExternalFunctions;
  std::map<std::string, llvm::Function *> CleanupEntries;
  llvm::Function *cleanupEntry(const std::string &);
  std::map<std::string, Case> Cases;
  std::map<std::string, std::vector<std::string>> Variants;
  std::map<std::string, std::string> DefaultCase;
  std::map<llvm::Value *, llvm::GlobalVariable *> Ready;
  std::vector<std::pair<std::string, Node>> Statics;
  unsigned ConstantSteps = 0, ConstantDepth = 0;
  std::map<std::string, Family> Families;
  std::map<std::string, std::vector<std::string>> Signatures;
  std::map<std::string, Family> Constraints;
  std::map<std::string, std::vector<Function *>> Overloads;
  std::deque<Function> Functions;
  std::map<std::string, Function *> Instances;
  std::vector<llvm::Function *> Startup, Shutdown;
  unsigned Serial = 0;
  explicit Context(llvm::Module &M, Options O)
      : M(M), C(M.getContext()), Opt(std::move(O)) {}
  llvm::Type *ir(const std::string &T, const Token &At = {});
  Function *declare(const Node &, const std::string &, const std::string &,
                    const Substitution &, const std::string &Owner = "");
  void buildTables(const std::string &, const std::vector<Function *> &);
  void tagged(const Node &, const std::string &, const std::string &);
  void record(const Node &, const std::string &, const std::string &,
              const Substitution &);
  void unit(const std::vector<Node> &, std::string Prefix = "");
  void emit(Function &);
  void validate(const Node &, const std::string &,
                const std::string &Owner = "");
};
Family expand(const Family &, size_t, const Token &);
std::string element(const std::string &T);
bool integer(const std::string &T);
bool implicitInteger(Value, const std::string &);
bool signedType(const std::string &T);
unsigned width(const std::string &T);
struct Local {
  std::map<std::string, Value> Names;
  std::vector<Value> Drops;
};
struct Loop {
  llvm::BasicBlock *Break, *Continue;
  size_t Depth;
  std::string Name;
  bool BreakUsed = false;
};
class Construction;
class Frame {
public:
  Context &U;
  Function *F;
  llvm::IRBuilder<> B;
  Options Opt;
  std::string Prefix;
  llvm::Function *IR;
  Substitution Env;
  std::vector<Local> Scopes;
  std::vector<Loop> Loops;
  std::vector<Value> Temps;
  std::map<std::string, int> Active;
  struct Registration {
    llvm::Value *Stamp, *Destructor;
  };
  bool TracksStorage = false;
  std::map<std::string, Registration> Registrations;
  std::map<std::string, Value> Extents;
  std::string StatementLabel;
  std::map<std::string, llvm::BasicBlock *> Labels;
  std::set<std::string> DefinedLabels;
  Value Self;
  Construction *Transaction = nullptr;
  llvm::BasicBlock *InlineReturn = nullptr;
  bool HasDelegated = false;
  std::map<std::string, llvm::Value *> FieldFlags;
  void retirement();
  void endField(const std::string &, const Token &, bool RunDestructor,
                bool Explicit);
  std::string directField(const Node &) const;
  llvm::Value *PendingObject = nullptr;
  std::set<std::string> PendingSlots;
  bool Live = true;
  Frame(Context &, Function *, llvm::Function *, std::string Prefix = "");
  llvm::BasicBlock *block(llvm::StringRef);
  llvm::AllocaInst *allocate(const std::string &, const Token &);
  Value load(Value);
  Value constant(llvm::APInt, std::string Type = "integer");
  Value literal(int64_t, const std::string &Ty = "integer");
  Value convert(Value, const std::string &, const Token &);
  Value binary(const Node &, Value, Value);
  Value boolean(const Node &);
  Value eval(const Node &, std::string Expected = "");
  Value constantEval(const Node &);
  Value floatingConvert(Value, const std::string &, const Token &,
                        bool Explicit = false);
  Value floatingBinary(const Node &, Value, Value,
                       const std::string &Expected = "");
  Value place(const Node &);
  Value lookup(const Token &);
  std::string resolve(std::string, const Token &);
  Value call(const Node &, const std::vector<Node> &, Value Receiver = {});
  Value invoke(Function &, std::vector<Value>, const Token &,
               Value Receiver = {});
  std::optional<unsigned> conversionRank(Value, const std::string &,
                                         const Token &);
  Function *select(std::string, const Node &, const std::vector<Value> &,
                   Value Receiver = {});
  Substitution bind(const Family &, const std::vector<Node> &,
                    const std::vector<Value> &, const Token &);
  Value construct(const std::string &, const std::vector<Node> &, const Token &,
                  llvm::Value *Dest = nullptr, const Node *Tail = nullptr);
  void checkAccess(const Node &, const std::string &Owner, const Token &);
  Function *checkSelected(Function *, const Token &);
  Value member(Value, const Token &);
  void stmt(const Node &);
  void object(const Node &, bool Global = false);
  void drop(Value);
  void track(Value &);
  void ensureLive(const Value &, const Token &);
  void replaceGeneration(const Value &, const std::string &, const Token &);
  void retireStorage(const Value &, bool);
  void forgetStorage();
  void joinStorage(const std::map<std::string, int> &);
  static bool usesStorage(const Node &);
  void cleanup(size_t);
  void endExpression(size_t From = 0);
  void consume(Value);
  bool adjust(Value &, const std::string &, const Token &, bool Emit = true);
  Value closure(const Node &);
  Value callClosure(Value, const std::vector<Node> &, const Token &);
  void bindCaptures();
  Value indirect(Value, const std::vector<Node> &, const Token &);
  void guard(llvm::Value *);
  void branch(llvm::BasicBlock *);
  bool predicate(const Node &);
  Value variant(const Case &, const std::vector<Node> &, const Token &);
  void match(const Node &);
  void installTables(Value);
  std::string methodOwner(const std::string &, const Token &);
  void bindParams();
};
class Construction {
  Value Object;
  Frame *TailFrame;
  struct Producer {
    Function *Owner;
    const Node *Source;
  };
  std::map<std::string, Producer> Explicit;
  std::vector<std::pair<Function *, const Node *>> Chain;
  std::map<Function *, Frame *> Activations;
  std::vector<std::string> Order;
  size_t Frontier = 0;
  std::set<size_t> Alternatives;
  std::set<std::string> Reserved;
  llvm::Value *Cursor = nullptr;
  const Node *OrdinaryAssignment = nullptr;
  void findReservations(Frame &);
  void atEachPosition(Frame &, const std::function<void()> &);
  void publish(Frame &);
  void advance(Frame &);
  void enter(Frame &, size_t);

public:
  Construction(Frame &, Function &, Value, const Node *, Frame *);
  void run(Frame &);
  void delegate(Frame &, const Node &);
  using Positions = std::set<size_t>;
  Positions positions() const;
  void restore(const Positions &);
  Positions loopPositions(const Node &) const;
  void checkAccess(Frame &, const Token &) const;
  std::optional<Value> firstWrite(Frame &, const Node &);
  bool needsDelegate(const Frame &) const;
};
} // namespace cpn
#endif
