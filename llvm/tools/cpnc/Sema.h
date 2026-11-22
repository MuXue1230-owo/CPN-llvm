#ifndef LLVM_TOOLS_CPNC_SEMA_H
#define LLVM_TOOLS_CPNC_SEMA_H
#include "Frontend.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SaveAndRestore.h"
#include <deque>
#include <optional>
namespace cpn {
struct Value {
  std::string Type;
  llvm::Value *IR = nullptr, *Address = nullptr;
  bool Readonly = false, Expiring = false;
  std::string Storage, RealText;
  llvm::Value *Generation = nullptr;
  bool BaseView = false, Prvalue = false;
  Value() = default;
  Value(std::string T, llvm::Value *V = nullptr, llvm::Value *A = nullptr,
        bool RO = false)
      : Type(std::move(T)), IR(V), Address(A), Readonly(RO) {}
};
struct Substitution {
  std::map<std::string, std::string> Types;
  std::map<std::string, Value> Values;
};
struct DefinitionSite {
  Options Configuration;
  size_t Through;
};
struct Family;
struct Function {
  Node Decl;
  std::string Name, Result, Owner, Prefix, DefaultPrefix;
  std::vector<std::string> Params;
  std::vector<Node> DefaultParams;
  Substitution Env;
  DefinitionSite Definition, Defaults;
  size_t DeclaredAt = 0;
  const Family *Origin = nullptr;
  llvm::Function *IR = nullptr, *BaseIR = nullptr;
  bool Emitting = false, Emitted = false;
  int Slot = -1;
};
struct Field {
  Node Decl;
  std::string Type;
};
enum class SpecialOperation {
  CopyConstruct,
  MoveConstruct,
  CopyAssign,
  MoveAssign
};
struct SpecialMember {
  Node Decl;
  Function *Body = nullptr;
};
using BasePath = std::vector<unsigned>;
struct DispatchTable {
  BasePath View;
  llvm::GlobalVariable *Entries;
  std::vector<BasePath> Receivers;
};
struct Record {
  Node Decl;
  llvm::StructType *IR = nullptr, *Layer = nullptr;
  std::vector<Field> Fields;
  std::map<SpecialOperation, SpecialMember> Special;
  // Canonical slots: distinct virtual bases, direct nonvirtual bases, members.
  std::vector<std::string> Bases;
  unsigned VirtualCount = 0;
  std::vector<unsigned> Direct;
  std::map<BasePath, std::string> Views;
  std::map<BasePath, std::vector<BasePath>> Edges;
  unsigned tailSlot(unsigned I) const {
    return Layer->getNumElements() + 1 + I;
  }
  unsigned offsetSlot(unsigned I) const {
    return Fields.size() + (Polymorphic ? 2 : 0) + I;
  }
  Substitution Env;
  bool Complete = false, Polymorphic = false, VirtualDestructor = false;
  std::vector<Function *> Virtuals;
  std::vector<DispatchTable> Tables;
};
struct Case {
  std::string Owner;
  unsigned Tag;
  llvm::StructType *Payload;
  Node Decl;
  std::vector<std::string> Types;
};
struct DeductionFailure : Diagnostic {};
struct Family {
  Node Decl;
  std::string Prefix;
  DefinitionSite Site;
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
  unsigned ConstantSteps = 0, ConstantDepth = 0, SpecializationDepth = 0;
  uint64_t Instantiations = 0, SolverSteps = 0;
  void chargeInstance(const Token &);
  void chargeSolver(const Token &);
  void checkNormalForm(const Node &);
  void checkDomain(const Node &, const std::string &);

  std::map<std::string, Family> Families;
  std::map<std::string, std::deque<Family>> FunctionFamilies;
  std::map<std::string, std::vector<std::string>> Signatures;
  std::map<std::string, Family> Constraints;
  std::map<std::string, std::vector<Function *>> Overloads;
  std::deque<Function> Functions;
  std::map<std::string, Function *> Instances;
  std::vector<llvm::Function *> Startup, Shutdown;
  unsigned Serial = 0;
  size_t Sequence = 0, LookupLimit = SIZE_MAX;
  DefinitionSite site() const { return {Opt, std::min(Sequence, LookupLimit)}; }
  explicit Context(llvm::Module &M, Options O)
      : M(M), C(M.getContext()), Opt(std::move(O)) {}
  llvm::Type *ir(const std::string &T, const Token &At = {});
  Function *declare(const Node &, const std::string &, const std::string &,
                    const Substitution &, const std::string &Owner = "");
  void declareMembers(const std::string &, const std::string &);
  void buildViews(const std::string &);
  std::optional<BasePath> lookupPath(const std::string &, const Token &,
                                     bool Method) const;
  void buildTables(const std::string &, const std::vector<Function *> &);
  void tagged(const Node &, const std::string &, const std::string &);
  void record(const Node &, const std::string &, const std::string &,
              const Substitution &);
  void unit(const std::vector<Node> &, std::string Prefix = "");
  void emit(Function &);
  void emitBody(Function &, llvm::Function *, bool);
  void validate(const Node &, const std::string &,
                const std::string &Owner = "");
};
struct EnterDefinition {
  llvm::SaveAndRestore<Options> OptionsScope;
  llvm::SaveAndRestore<size_t> LookupScope;
  EnterDefinition(Context &U, const DefinitionSite &Site)
      : OptionsScope(U.Opt, Site.Configuration),
        LookupScope(U.LookupLimit, Site.Through) {}
};
bool sameGenericSignature(const Node &, const Node &);
bool betterPattern(const Node &, const Node &);
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
struct CallArguments {
  std::vector<Value> Values;
  std::vector<llvm::BasicBlock *> Entries, Exits;
};
class Construction;
class Frame {
public:
  Context &U;
  Function *F;
  llvm::IRBuilder<> B;
  Options Opt;
  size_t LookupLimit;
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
  bool Live = true, RequireNoexcept = false, BaseLayer = false;
  Frame(Context &, Function *, llvm::Function *, std::string Prefix = "");
  llvm::BasicBlock *block(llvm::StringRef);
  llvm::AllocaInst *allocate(const std::string &, const Token &);
  Value load(Value);
  Value materialize(Value, const Token &, llvm::Value *Dest = nullptr);
  void transfer(Value, llvm::Value *Dest, SpecialOperation, const Token &,
                bool AsBase = false);
  Value bindReference(Value, const std::string &, const Token &);
  Value callResult(const std::string &, llvm::Value *, const Token &);
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
  CallArguments evaluateArguments(const std::vector<Node> &,
                                  Function *Context = nullptr);
  void admitArguments(CallArguments &, Function *, const Token &);
  Value invoke(Function &, std::vector<Value>, const Token &,
               Value Receiver = {}, bool Prepared = false);
  std::optional<unsigned> conversionRank(Value, const std::string &,
                                         const Token &);
  std::vector<Function *> visibleOverloads(const std::string &) const;
  std::string callKey(const std::string &, const std::string &Owner = "") const;
  Function *select(std::string, const Node &, const std::vector<Value> &,
                   Value Receiver = {});
  Function *prepareCandidate(const Family &, const std::string &, const Node &,
                             const std::vector<Value> &);
  Substitution bind(const Family &, const std::vector<Node> &,
                    const std::vector<Value> &, const Token &);
  std::string initSlot(const Node &);
  std::optional<Value> directConstruction(const Node &, const std::string &,
                                          llvm::Value *);
  Value construct(const std::string &, const std::vector<Node> &, const Token &,
                  llvm::Value *Dest = nullptr, const Node *Tail = nullptr,
                  bool AsBase = false);
  void checkAccess(const Node &, const std::string &Owner, const Token &);
  Function *checkSelected(Function *, const Token &);
  Value member(Value, const Token &);
  void stmt(const Node &);
  void object(const Node &, bool Global = false);
  void drop(Value, bool AsBase = false);
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
  const Family *constraint(const std::string &) const;
  bool predicate(const Node &);
  bool constructible(const std::string &, SpecialOperation, const Token &);
  Value variant(const Case &, const std::vector<Node> &, const Token &,
                llvm::Value *Dest = nullptr, bool Default = false);
  void visitPayload(Value, llvm::function_ref<void(const Case &)>);
  void dropPayload(Value);
  llvm::Value *payloadAddress(const Case &, llvm::Value *, unsigned);
  void match(const Node &);
  llvm::Value *fieldAddress(Value, unsigned);
  Value baseView(Value, const BasePath &);
  void bindVirtualLayout(Value);
  llvm::Value *snapshot(Value);
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
