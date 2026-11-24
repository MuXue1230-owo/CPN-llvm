#ifndef LLVM_TOOLS_CPNC_SEMA_H
#define LLVM_TOOLS_CPNC_SEMA_H
#include "Frontend.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SaveAndRestore.h"
#include <deque>
#include <optional>
namespace cpn {
inline constexpr char StorageViewType[] = "$cpn.storage";
inline constexpr char StorageIdentityType[] = "$cpn.storage_identity";
inline constexpr char StorageArgumentBundle[] = "cpn.storage.arguments";
inline constexpr char StorageRetirementBundle[] = "cpn.storage.retire";
inline constexpr char StorageReplacementBundle[] = "cpn.storage.replace";
inline constexpr char StorageProjectionBundle[] = "cpn.storage.projection";
inline constexpr char IncomingPointerStorage[] = "cpn.storage.incoming.pointer";
inline constexpr char IncomingArrayStorage[] = "cpn.storage.incoming.array";
inline constexpr char IncomingReferenceStorage[] =
    "cpn.storage.incoming.reference";
inline constexpr char RetiredReference[] = "cpn.storage.reference.retire";
inline constexpr unsigned StorageArgumentFields = 5;
inline bool memoryIdentity(llvm::StringRef T) {
  return T == StorageIdentityType;
}
bool usesMemoryLibrary(const Node &);
bool usesFloatingContext(const Node &);
using SourcePosition = std::pair<unsigned, unsigned>;
struct JumpCleanups {
  std::map<SourcePosition, std::set<SourcePosition>> Exited;
  std::set<std::string> Targets;
};
std::string unconst(const std::string &T);
std::string qualifyConst(const std::string &T);
llvm::Constant *constantElement(llvm::Constant *, uint64_t Index);
std::string nativeLinkName(const llvm::Module &, llvm::StringRef Category,
                           llvm::ArrayRef<llvm::StringRef> Components);
std::string externalIRName(llvm::StringRef Symbol);
struct ConstantPlace;
struct Case;
struct Value;
struct ConstantStorageSlot {
  bool Ended = false;
  bool Constructing = false;
  bool Retiring = false;
  uint64_t Identity = 0;
  std::shared_ptr<Value> Replacement;
};
struct ConstantStorage : ConstantStorageSlot {
  std::vector<llvm::GlobalVariable *> Designations;
  std::map<std::vector<uint64_t>, ConstantStorageSlot> Subobjects;
  std::shared_ptr<ConstantPlace> OriginalExtent;
};
// Each evaluation-local object has its own lifetime. Copying its value creates
// a separate object, while assignment preserves the target storage identity.
struct ConstantStorageIdentity {
  std::shared_ptr<ConstantStorage> Storage;
  ConstantStorageIdentity() = default;
  ConstantStorageIdentity(const ConstantStorageIdentity &) {}
  ConstantStorageIdentity &operator=(const ConstantStorageIdentity &) {
    return *this;
  }
};
struct Value {
  std::shared_ptr<ConstantPlace> Location;
  std::shared_ptr<Value> ConstantTemporary;
  ConstantStorageIdentity ConstantIdentity;
  SourcePosition DeclaredAt;
  std::string Type;
  llvm::Value *IR = nullptr, *Address = nullptr;
  bool Readonly = false, Expiring = false;
  std::string Storage, RealText;
  llvm::Value *Generation = nullptr, *Slot = nullptr;
  std::string ExtentType;
  std::optional<std::pair<llvm::Value *, unsigned>> ConstructionBase;
  // Bounds of a pointer value and of a designated array element are distinct
  // for arrays of pointers. BoundsCell follows reassignment of a local pointer.
  llvm::Value *Lower = nullptr, *Upper = nullptr, *BoundsCell = nullptr;
  llvm::Value *ElementLower = nullptr, *ElementUpper = nullptr;
  llvm::GlobalVariable *ReferenceCell = nullptr;
  llvm::Value *ArraySlot = nullptr, *ArrayGeneration = nullptr;
  struct PointerCellLifetime {
    llvm::Value *Slot = nullptr, *Generation = nullptr, *ArraySlot = nullptr,
                *ArrayGeneration = nullptr;
    std::string Storage, ExtentType;
    bool Subobject = false, BaseView = false;
  };
  // A pointer object's lifetime is independent of the designation stored in it.
  std::optional<PointerCellLifetime> PointerCell;
  void rememberPointerCell(const Value &Cell);
  Value objectDesignation() const;
  std::set<unsigned> Origins;
  bool Subobject = false, OptionalTemp = false;
  void borrow(const Value &V) {
    Generation = V.Generation;
    Slot = V.Slot;
    Storage = V.Storage;
    ExtentType = V.ExtentType;
    ConstructionBase = V.ConstructionBase;
    Subobject = V.Subobject;
    BaseView = V.BaseView;
    Lower = V.Lower;
    Upper = V.Upper;
    Origins = V.Origins;
    ArraySlot = V.ArraySlot;
    ArrayGeneration = V.ArrayGeneration;
  }
  bool BaseView = false, Prvalue = false;
  bool Rollback = false;
  llvm::Value *ConstructionProgress = nullptr;
  llvm::Value *ConstructionReservation = nullptr;
  const Case *ConstructionCase = nullptr;
  Value() = default;
  Value(std::string T, llvm::Value *V = nullptr, llvm::Value *A = nullptr,
        bool RO = false)
      : Type(std::move(T)), IR(V), Address(A), Readonly(RO) {}
};
struct ConstantTransfer {
  Node::Kind Kind;
  Value Result;
  std::string Label;
  Token At;
};
struct Substitution {
  std::map<std::string, std::string> Types;
  std::map<std::string, Value> Values;
  std::map<std::string, size_t> PackLengths;
};
struct TypeApplication {
  std::string Family;
  // Type arguments carry their canonical type and constant arguments also
  // carry their constant LLVM value.
  std::vector<Value> Arguments;
};
struct DefinitionSite {
  Options Configuration;
  size_t Through;
};
struct StaticDeclaration {
  std::string Name, Prefix;
  Node Decl;
};
class Frame;
struct Family;
struct Function {
  Node Decl;
  EffectBound Effects;
  EffectSet PredicateEffects;
  std::string Name, Result, Owner, Prefix, DefaultPrefix;
  std::string ExternalSymbol;
  std::vector<std::string> Params;
  std::vector<Node> DefaultParams;
  Substitution Env, DefaultEnv;
  DefinitionSite Definition, Defaults;
  size_t DeclaredAt = 0;
  const Family *Origin = nullptr;
  llvm::Function *IR = nullptr, *BaseIR = nullptr, *ImportAdapter = nullptr;
  bool Emitting = false, Emitted = false;
  bool ContractsBound = false;
  int Slot = -1;
  JumpCleanups ExitedLifetimes;
  bool MayWhole = false;
  std::set<unsigned> NoEscape, BorrowedResult, Consumes;
  std::set<unsigned> RequiresAlive, Initializes;
  std::set<Function *> Calls;
  bool isStatic() const { return Decl.Settings.count("static"); }
};
struct Field {
  Node Decl;
  std::string Type;
  std::optional<DefinitionSite> DefaultSite = std::nullopt;
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
  std::vector<Function *> Targets;
};
struct Record {
  Node Decl;
  std::string EnclosingScope;
  llvm::StructType *IR = nullptr, *Layer = nullptr;
  std::vector<Field> Fields;
  std::map<SpecialOperation, SpecialMember> Special;
  // Canonical slots: distinct virtual bases, direct nonvirtual bases, members.
  std::vector<std::string> Bases;
  unsigned VirtualCount = 0;
  std::vector<unsigned> Direct;
  std::map<BasePath, std::string> Views;
  std::map<BasePath, std::vector<BasePath>> Edges;
  std::map<std::string, BasePath> LocalOwners, Owners;
  bool contains(const BasePath &, const BasePath &) const;
  unsigned tailSlot(unsigned I) const {
    return Layer->getNumElements() + 1 + I;
  }
  unsigned offsetSlot(unsigned I) const {
    return Fields.size() + (Polymorphic ? 2 : 0) + I;
  }
  unsigned ownerOffsetSlot(unsigned I) const {
    return offsetSlot(VirtualCount + I);
  }
  unsigned layerIndexSlot() const { return ownerOffsetSlot(VirtualCount); }
  unsigned layerEnteredSlot() const { return layerIndexSlot() + 1; }
  unsigned obligationsSlot() const { return tailSlot(VirtualCount); }
  Substitution Env;
  std::optional<DefinitionSite> InvariantSite;
  bool Complete = false, Polymorphic = false, VirtualDestructor = false;
  std::vector<Function *> Virtuals;
  std::vector<DispatchTable> Tables;
  llvm::Function *ClosureEntry = nullptr;
};
struct Case {
  std::string Owner;
  unsigned Tag;
  llvm::StructType *Payload;
  Node Decl;
  std::vector<std::string> Types;
};
// Paths into evaluation-local values survive immutable LLVM aggregate updates.
struct ConstantPlace {
  struct Step {
    uint64_t Index;
    const Case *Alternative = nullptr;
    std::string BaseOwner;
    bool operator==(const Step &Other) const {
      return Index == Other.Index && Alternative == Other.Alternative &&
             BaseOwner == Other.BaseOwner;
    }
  };
  Value *Root;
  std::vector<Step> Steps;
  std::string Type;
  bool Readonly;
  std::shared_ptr<Value> SymbolicRoot;
  std::optional<std::weak_ptr<ConstantStorage>> Lifetime;
  void trackLifetime();
  std::vector<uint64_t> indices() const;
  const ConstantStorageSlot *registeredExtent() const;
  ConstantStorageSlot &registerExtent() const;
  bool hasLiveExtent() const;
  void checkLifetime(const Token &, bool ExtentOnly = false) const;
  Value read(Frame &, const Token &) const;
  void write(Frame &, Value, const Token &) const;
};
struct DeductionFailure : Diagnostic {};
struct Family {
  Node Decl;
  std::string Prefix;
  DefinitionSite Site;
  Substitution Enclosing{};
  std::string Owner{};
  std::optional<Node> Body{};
  std::optional<DefinitionSite> BodySite{};
  Substitution BodyBindings{};
};
struct Context {
  llvm::Module &M;
  llvm::LLVMContext &C;
  Options Opt;
  std::map<std::string, std::string> Aliases, Enums;
  std::map<std::string, Node::Kind> Declarations;
  std::set<std::string> DefinedEnums;
  std::map<std::string, std::vector<llvm::ConstantInt *>> EnumValues;
  std::set<std::pair<std::string, SourcePosition>> LocalTypeSites;
  std::map<std::string, Record> Records;
  std::map<llvm::GlobalVariable *, std::pair<std::string, size_t>>
      DispatchTables;
  std::map<std::string, std::pair<std::string, Node>> StaticMembers;
  struct MemberType {
    std::string Owner;
    std::vector<Node> Declarations;
    DefinitionSite Site;
    bool Binding = false, Bound = false;
    const Node &first() const { return Declarations.front(); }
  };
  std::map<std::string, MemberType> MemberTypes;
  std::set<std::string> BindingMemberAliases;
  unsigned MemberAliasDepth = 0;
  std::map<std::string, Value> Globals, ExternalObjects;
  std::map<std::string, Function *> ExternalFunctions;
  std::map<std::string, llvm::Function *> CleanupEntries;
  bool aggregate(const std::string &T) const {
    return Records.count(unconst(T)) || llvm::StringRef(T).ends_with("]");
  }
  llvm::StructType *SlotType = nullptr;
  llvm::StructType *ownerRecordType();
  std::map<std::string, llvm::Constant *> TypeIDs;
  void enableStorage();
  void finishPointerStorage();
  llvm::Constant *typeID(const std::string &);
  llvm::Function *cleanupEntry(const std::string &);
  std::map<std::string, Case> Cases;
  std::map<std::string, std::vector<std::string>> Variants;
  std::map<std::string, std::string> DefaultCase;
  std::map<llvm::Value *, llvm::GlobalVariable *> Ready;
  std::map<llvm::Function *, llvm::GlobalVariable *> Initializing;
  llvm::Function *StaticRead = nullptr;
  llvm::GlobalVariable *CurrentInitializer = nullptr;
  void checkStaticRead(llvm::IRBuilder<> &, llvm::Value *);
  void finishStaticReads();
  std::set<llvm::GlobalVariable *> ConstantObjects;
  std::vector<StaticDeclaration> Statics;
  std::map<llvm::Constant *, llvm::Constant *> ConstantPayloads;
  struct LocalConstantAddress {
    ConstantPlace Place;
    std::weak_ptr<ConstantStorage> Lifetime;
    Token At;
    llvm::GlobalVariable *PhysicalAddress = nullptr;
  };
  std::map<llvm::GlobalVariable *, LocalConstantAddress> LocalConstantAddresses;
  uint64_t NextConstantStorageIdentity = 2;
  void finishLocalConstantAddresses();
  std::vector<const Value *> ConstantInvariantLifetimes;
  void chargeConstant(const Token &, uint64_t Steps = 1);
  unsigned ConstantSteps = 0, ConstantDepth = 0, SpecializationDepth = 0;
  uint64_t Instantiations = 0, SolverSteps = 0;
  void chargeInstance(const Token &);
  void chargeSolver(const Token &);
  void checkNormalForm(const Node &);
  void checkDomain(const Node &, const std::string &,
                   const Node *SymbolOwner = nullptr);

  std::map<std::string, Node> TypeQueries;
  std::map<std::pair<SourcePosition, std::string>, const Node *> ArrayExtents;
  uint64_t ExpandedTypeQueries = 0;
  std::map<std::string, Family> Families;
  std::map<std::string, TypeApplication> TypeApplications;
  std::map<std::string, std::vector<Family>> Specializations;
  std::map<std::string, std::deque<Family>> FunctionFamilies;
  std::map<std::string, std::vector<std::string>> Signatures;
  std::map<std::string, Family> Constraints;
  std::map<std::string, std::vector<Function *>> Overloads;
  std::deque<Function> Functions;
  std::map<std::string, Function *> Instances;
  std::vector<std::pair<std::string, llvm::Function *>> Startup, Shutdown;
  size_t Sequence = 0, LookupLimit = SIZE_MAX;
  unsigned StorageSerial = 0;
  DefinitionSite site() const { return {Opt, std::min(Sequence, LookupLimit)}; }
  explicit Context(llvm::Module &M, Options O)
      : M(M), C(M.getContext()), Opt(std::move(O)) {}
  llvm::Type *ir(const std::string &T, const Token &At = {});
  void checkRecordLayout(llvm::ArrayRef<llvm::Type *>, const Token &) const;
  bool cScalarType(const std::string &T) const;
  Function *declare(const Node &, const std::string &, const std::string &,
                    const Substitution &, const std::string &Owner = "");
  void defineQualified(const Node &, const std::string &,
                       const Substitution * = nullptr);
  struct MemberBody {
    struct OwnerBinding {
      SourcePosition Position;
      std::vector<Node> Parameters;
    };
    std::vector<OwnerBinding> GenericOwners;
    SourcePosition Member;
    Node Definition;
    DefinitionSite Site;
  };
  std::map<SourcePosition, std::map<SourcePosition, MemberBody>> OwnerBodies;
  void defineFamilyMember(const Node &, const std::string &);
  void bindFamilyMember(const std::string &, const MemberBody &);
  void declareMembers(const std::string &, const std::string &);
  struct RecordBodies {
    std::string Owner;
    DefinitionSite Site;
    std::vector<Function *> Members;
  };
  unsigned RecordLayoutDepth = 0;
  std::vector<RecordBodies> PendingRecordBodies;
  void finishRecordBodies();
  void validateDefaultCase(const std::string &);
  void validateInvariants(const std::string &);
  bool hasCheckedInvariant(const Function &) const;
  bool Whole = false;
  std::vector<std::pair<Function *, Token>> RestrictedPointers;
  void checkWholeContracts();
  void checkEffects();
  EffectSet bindPredicateEffects(const Function &, llvm::Function &Probe,
                                 const llvm::Argument *Result);
  struct ContractProof {
    llvm::BasicBlock *Before, *Success, *Failure;
    Token At;
    std::string Label;
  };
  std::vector<ContractProof> ContractProofs;
  void verifyProvenContracts();
  void bindScalarLibrary();
  void bindMemoryLibrary(bool Owners);
  void bindNumericLibrary(bool WithFPContext);
  void initializeFloatingRoot();
  void checkBorrowEscapes();
  std::map<std::string, llvm::Function *> Coordinators, BaseCleanups;
  llvm::Function *coordinator(const std::string &);
  llvm::Function *baseCleanup(const std::string &);
  void bindOwners(const std::string &, const std::string &);
  void buildViews(const std::string &);
  std::optional<BasePath> lookupPath(const std::string &, const Token &,
                                     bool Method) const;
  void buildTables(const std::string &, const std::vector<Function *> &);
  void validateOverrides(const std::string &, const std::vector<Function *> &);
  void proveValueOverride(Function &Derived, Function &Base, const BasePath &);
  bool proveNoContractFailure(llvm::Function &);
  void genericFunction(const Node &, const std::string &, const std::string &,
                       const std::string &Owner = "");
  void attachGenericBody(Function &, const Family &);
  void setGenericBody(Family &, Node, DefinitionSite, Substitution = {});
  void enumeration(Frame &, const Node &, const std::string &);
  void indexMemberTypes(llvm::ArrayRef<Node>, const std::string &);
  void completeMemberTypes(llvm::ArrayRef<Node>, const std::string &);
  void completeMemberType(const std::string &, const Token &);
  std::string bindMemberAlias(const std::string &);
  void tagged(const Node &, const std::string &, const std::string &,
              const Substitution & = {});
  void record(const Node &, const std::string &, const std::string &,
              const Substitution &);
  std::string callableType(const Function &);
  llvm::AttributeList scalarCallABI(const std::string &Result,
                                    llvm::ArrayRef<std::string> Params,
                                    unsigned HiddenPrefix = 0) const;
  bool compatibleCallable(const std::string &From, const std::string &To) const;
  void unit(const std::vector<Node> &, std::string Prefix = "");
  void emit(Function &);
  void emitBody(Function &, llvm::Function *, bool);
  void bindContracts(Function &);
  llvm::Function *foreignContractEntry(Function &);
  void emitForeignContractAdapters();
  JumpCleanups validate(const Node &, const std::string &,
                        const std::string &Owner = "",
                        const Node *FamilyOwner = nullptr,
                        const Substitution *Captured = nullptr);
};
struct EnterDefinition {
  llvm::SaveAndRestore<Options> OptionsScope;
  llvm::SaveAndRestore<size_t> LookupScope;
  EnterDefinition(Context &U, const DefinitionSite &Site)
      : OptionsScope(U.Opt, Site.Configuration),
        LookupScope(U.LookupLimit, Site.Through) {}
};
// Find the nearest namespace binding, or begin at the module root for ::names.
inline bool callableFlag(llvm::StringRef T, llvm::StringRef Flag) {
  return T.take_back(T.size() - (T.rfind(')') + 1)).contains(Flag);
}
std::string rebindTypeNames(llvm::StringRef, const Node &, const Node &);
size_t arrayExtentStart(llvm::StringRef);
struct CallableTypeParts {
  llvm::StringRef Result, Parameters, Flags;
};
std::optional<CallableTypeParts> splitCallableType(llvm::StringRef);
bool sameGenericSignature(const Node &, const Node &);
bool sameGenericResult(const Node &, const Node &);
bool sameGenericValueContracts(const Node &, const Node &);
bool containsUnexpandedPack(const Context &, const Node &,
                            llvm::function_ref<bool(llvm::StringRef)>);
bool containsUnexpandedPack(const Context &, llvm::StringRef,
                            llvm::function_ref<bool(llvm::StringRef)>);
void validateTypePackExpansions(const Context &, llvm::StringRef, const Token &,
                                llvm::function_ref<bool(llvm::StringRef)>);
void visitTypeQueries(const Context &, llvm::StringRef,
                      llvm::function_ref<void(const Node &)>);
std::optional<std::vector<size_t>>
matchOwnerBinders(llvm::ArrayRef<Node> Pattern, llvm::ArrayRef<Node> Arguments,
                  llvm::ArrayRef<Node> Formals, llvm::ArrayRef<Node> Binders,
                  llvm::ArrayRef<size_t> Enclosing);
EffectBound genericEffectBound(const Node &, bool HasReceiver);
std::set<llvm::StringRef> callableFlags(llvm::StringRef);
EffectBound callableEffects(llvm::StringRef);
EffectSet callablePredicateEffects(llvm::StringRef);
std::string predicateEffectFlags(const EffectSet &);
void describeBorrowCall(llvm::CallBase &, const Token &, const Options &,
                        llvm::ArrayRef<std::string> Params, unsigned Headers,
                        const std::set<unsigned> &NoEscape,
                        const std::set<unsigned> &Returned,
                        const EffectBound &Effects, bool MayWriteCallStorage);
void describeEffectCall(llvm::CallBase &, const EffectBound &, unsigned Headers,
                        bool Receiver = false,
                        llvm::Function *Contract = nullptr,
                        llvm::ArrayRef<unsigned> ValueAggregates = {},
                        const EffectSet &Predicate = {});
std::string parameterBinding(const Node &, size_t);
void normalizeContracts(Node &);
bool sameContracts(const Node &, const Node &);
std::vector<std::string> splitArguments(llvm::StringRef);
Family expand(Context &, const Family &, size_t, const Token &);
std::string element(const std::string &T);
bool implicitInteger(Value, const std::string &);
bool signedType(const std::string &T);
unsigned width(const std::string &T);
enum class NumericProjection { Checked, Exact, Wrapping, Saturating, Ordinary };
struct ScalarCastProjection {
  llvm::Value *Number, *Outside, *NonFinite, *Inexact;
  llvm::Value *Clamped, *Wrapped, *FPFlags = nullptr;
};
struct Local {
  std::map<std::string, Node::Kind> Nominals;
  std::map<std::string, std::string> Aliases;
  std::map<std::string, Value> Names;
  std::map<std::string, std::string> StaticNames;
  std::set<std::string> UnavailableNames;
  std::vector<Value> Drops;
  std::vector<std::string> ConstantDrops;
  std::map<std::string, SourcePosition> ConstantTypeSites;
};
struct Loop {
  llvm::BasicBlock *Break, *Continue;
  size_t Depth;
  std::string Name;
  bool BreakUsed = false;
};
struct Initializer {
  Value Result;
  llvm::BasicBlock *Entry, *Exit;
  llvm::AllocaInst *Storage;
};
struct PointerCall {
  llvm::Value *Previous = nullptr, *Rows = nullptr;
};
bool carriesPointerBounds(const std::string &);
bool carriesBorrow(const std::string &);
void forwardPointerCall(llvm::IRBuilder<> &, llvm::Function *,
                        llvm::Function *);
struct CallArguments {
  std::vector<Value> Values;
  std::vector<llvm::BasicBlock *> Entries, Exits;
};
class ConstantActivation {
  llvm::SaveAndRestore<unsigned> Depth;

public:
  ConstantActivation(Context &, const Token &);
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
  // Positive states name a live generation. Zero is ended, -1 is unknown,
  // and LiveGeneration is a live registration with an unknown generation.
  static constexpr int LiveGeneration = -2;
  std::map<std::string, int> Active;
  std::map<const llvm::Value *, int> StorageGenerations;
  int NextStorageGeneration = 1;
  struct Registration {
    llvm::Value *Slot;
  };
  bool TracksStorage = false;
  std::map<std::string, Registration> Registrations;
  std::map<std::string, Value> Extents;
  std::string StatementLabel;
  std::map<std::string, llvm::BasicBlock *> Labels;
  std::set<std::string> DefinedLabels;
  Value Self;
  Value *ConstantReceiver = nullptr;
  std::map<std::string, bool> ConstantMembersAlive;
  Construction *Transaction = nullptr;
  llvm::BasicBlock *InlineReturn = nullptr;
  bool HasDelegated = false;
  std::map<std::string, llvm::Value *> FieldFlags;
  std::set<std::string> ManualDropSlots;
  bool InDestructorCleanup = false;
  bool UnionPayloadConstructed = false;
  void retirement();
  void checkAbandon(const std::string &, const Token &);
  void endField(const std::string &, const Token &, bool RunDestructor,
                bool Explicit);
  llvm::Value *destructionMemberRegistration(unsigned Index);
  llvm::Value *destructionSlotAlive(unsigned Index);
  void checkCleanupFrontier(const std::string &, const Token &);
  void checkCleanupStorageRequest(Value, bool Destroy);
  std::string directField(const Node &) const;
  llvm::Value *PendingObject = nullptr;
  std::set<std::string> PendingSlots;
  Value ExpressionDestination;
  llvm::Value *resultAddress(const std::string &, const Token &);
  bool Live = true, RequireNoexcept = false, BaseLayer = false;
  bool TypeQuery = false;
  bool InPredicate = false;
  Frame(Context &, Function *, llvm::Function *, std::string Prefix = "");
  llvm::BasicBlock *block(llvm::StringRef);
  llvm::AllocaInst *allocate(const std::string &, const Token &);
  Value load(Value, const Token &At = {});
  Value materialize(Value, const Token &, llvm::Value *Dest = nullptr,
                    bool CheckInvariant = true);
  void transfer(Value, llvm::Value *Dest, SpecialOperation, const Token &,
                bool AsBase = false, bool CheckInvariant = true);
  Value bindReference(Value, const std::string &, const Token &);
  Value callResult(const std::string &, llvm::Value *, const Token &,
                   llvm::Value *Storage);
  Value constant(llvm::APInt, std::string Type = "integer");
  Value literal(int64_t, const std::string &Ty = "integer");
  Value convert(Value, const std::string &, const Token &);
  Value pointerBinary(const Node &, Value, Value);
  llvm::StructType *pointerMetadataType();
  void readBounds(Value &, llvm::Value *);
  void readReferent(Value &, llvm::Value *);
  llvm::Value *IncomingPointerRows = nullptr;
  void receivePointerCall();
  llvm::Value *incomingPointerCell(size_t);
  void publishPointerResult(const Value &);
  llvm::SmallVector<llvm::OperandBundleDef, 1>
  storageArgumentBundles(llvm::ArrayRef<std::string>, llvm::ArrayRef<Value>,
                         unsigned ABIHeaders);
  PointerCall openPointerCall(llvm::Value *, const std::string &,
                              llvm::ArrayRef<std::string>,
                              llvm::ArrayRef<Value>);
  void closePointerCall(const PointerCall &);
  Value pointerCallResult(Value, const PointerCall &, const std::string &);
  Value constantPointerOffset(const Node &, Value, Value, const std::string &);
  llvm::Constant *symbolicAddress(Value, const Token &);
  Value openStaticReference(Value);
  void staticReference(const Node &, const std::string &, const std::string &);
  llvm::Value *storedPointerCell(llvm::Value *);
  void copyStoredBounds(Value, llvm::Value *);
  void saveBounds(llvm::Value *, Value);
  void offsetRegistration(Value &, llvm::Value *, const std::string &,
                          const Token &, std::optional<int64_t>);
  Value binary(const Node &, Value, Value);
  std::string commonIntegerType(const std::string &, const std::string &,
                                const Token &);
  Value boolean(const Node &);
  llvm::Value *evaluatePredicate(const Node &, llvm::StringRef Declaration,
                                 unsigned Ordinal, llvm::StringRef Mode,
                                 bool ValidateOnly, bool OwnBoundary = true);
  void checkContracts(bool Entry, Value Result = {}, bool ValidateOnly = false,
                      bool *MayTrap = nullptr);
  void requireObserver(const EffectBound &, const Token &,
                       const Function * = nullptr);
  void requirePredicateCleanup(const std::string &Type, const Token &);
  Value eval(const Node &, std::string Expected = "",
             llvm::Value *Dest = nullptr);
  Value constantEval(const Node &);
  std::string unevaluatedType(const Node &, bool IncludeCategory);
  Value floatingConvert(Value, const std::string &, const Token &,
                        bool Explicit = false);
  Value floatingBinary(const Node &, Value, Value,
                       const std::string &Expected = "",
                       llvm::Value **LocalFlags = nullptr);
  ScalarCastProjection projectScalarCast(Value, const std::string &,
                                         NumericProjection, llvm::Value *,
                                         const Token &);
  Value numericRepresentationResult(const Token &, const Value &,
                                    llvm::Value *Invalid);
  Value place(const Node &, bool NeedLive = true);
  Value pointedObject(Value, const Token &);
  Value subscript(const Node &);
  Value lookup(const Token &, bool NeedLive = true);
  std::string resolve(std::string, const Token &);
  std::string materializationType(const std::string &, const Token &);
  Value call(const Node &, const std::vector<Node> &, Value Receiver = {});
  std::optional<Value> resultObserver(const Node &, const std::vector<Node> &,
                                      Value Receiver);
  std::optional<Value> scalarConversion(const Node &, llvm::StringRef,
                                        const std::vector<Node> &);
  std::optional<Value> libraryDiagnostic(const Node &,
                                         const std::vector<Node> &);
  std::optional<Value> memoryCall(const Node &, const std::vector<Node> &,
                                  Value Receiver);
  std::optional<Value> namedInteger(const Node &, llvm::StringRef,
                                    const std::vector<Node> &);
  Value floatingContextCall(const Node &, llvm::StringRef,
                            const std::vector<Node> &);
  std::optional<Value> floatingSpecial(const Node &, llvm::StringRef,
                                       const std::vector<Node> &);
  CallArguments evaluateArguments(const std::vector<Node> &,
                                  Function *Context = nullptr,
                                  Value SingleDestination = {});
  void admitArguments(CallArguments &, Function *, const Token &);
  Value invoke(Function &, std::vector<Value>, const Token &,
               Value Receiver = {}, bool Prepared = false);
  std::optional<unsigned> conversionRank(Value, const std::string &,
                                         const Token &);
  std::vector<Function *> visibleOverloads(const std::string &) const;
  std::string callKey(const std::string &, const std::string &Owner = "") const;
  Value applyOperator(const std::string &, const Token &, CallArguments);
  Function *select(std::string, const Node &, const std::vector<Value> &,
                   Value Receiver = {}, bool Operator = false,
                   Function *Generated = nullptr);
  Function *prepareCandidate(const Family &, const std::string &, const Node &,
                             const std::vector<Value> &);
  bool betterOverloadPattern(const Function &, const Function &, const Token &);
  void selectTypeSpecialization(const std::string &, Family &, Substitution &,
                                const Token &);
  Substitution bind(const Family &, const std::vector<Node> &,
                    const std::vector<Value> &, const Token &);
  size_t deducePackArity(const Family &, const Node &, llvm::ArrayRef<Value>);
  std::optional<Value> deduceGenericArgument(const Family &, const Node &,
                                             llvm::ArrayRef<Value>,
                                             const Token &,
                                             const std::string &ValueType = "");
  std::string initSlot(const Node &);
  Initializer deferInitializer(const Node &, const std::string &Expected);
  Value runInitializer(Initializer &, Value Target, const Token &);
  std::optional<Value> directConstruction(const Node &, const std::string &,
                                          llvm::Value *);
  Value construct(const std::string &, const std::vector<Node> &, const Token &,
                  llvm::Value *Dest = nullptr, const Node *Tail = nullptr,
                  bool AsBase = false, llvm::function_ref<void()> Admit = {});
  void localType(const Node &);
  void runConstructionTail(Value, const Node *, bool BoundSlots = false);
  void checkAccess(const Node &, const std::string &Owner, const Token &);
  void evaluateInvariants(Value, bool ValidateOnly, bool OwnBoundary = false);
  void checkInvariants(Value, bool IncludeBases = false,
                       bool OwnBoundary = false);
  void checkMethodInvariant(bool Entry);
  struct PendingInvariantLifetime {
    llvm::Value *Previous;
    size_t Depth;
    std::optional<SourcePosition> Tail;
  };
  std::vector<PendingInvariantLifetime> InvariantConstructionLifetimes;
  llvm::Value *pushInvariantLifetime(const Value &, const Node *Tail = nullptr,
                                     bool IsConstruction = true);
  void popInvariantLifetime(llvm::Value *, bool IsConstruction = true);
  void exitInvariantConstructionLifetimes(
      size_t Depth = 0, const std::set<SourcePosition> *Exited = nullptr);
  Function *checkSelected(Function *, const Token &);
  Value member(Value, const Token &, bool NeedLive = true);
  void stmt(const Node &, llvm::StringRef EntryLabel = {});
  void constantSequence(llvm::ArrayRef<Node>, llvm::StringRef EntryLabel);
  void rewindConstantScope(const ConstantTransfer &, const Token &Destination);
  void object(const Node &, bool Global = false);
  void drop(Value, bool AsBase = false);
  void dropLayer(Value, bool AsBase, bool Rollback = false);
  llvm::Value *beginConstructionPrefix(Value, const Case * = nullptr);
  void endConstructionPrefix(llvm::Value *);
  void rollbackConstructionPrefix(Value, llvm::Value *Count);
  void dropArrayPrefix(Value, llvm::Value *Count);
  BasePath selectBase(const Record &, const BasePath &, const Node &);
  Value transferOwner(const Node &, const Node &);
  Value baseRequest(const Node &, const Node &);
  llvm::Value *wholeEpoch();
  void propagateWhole(llvm::Value *);
  void exitWhole();
  static bool usesWhole(const Node &);
  llvm::Value *slotFor(Value);
  Value subobject(Value, Value, llvm::ArrayRef<llvm::OperandBundleDef> = {});
  void dropChild(Value, Value, bool AsBase = false);
  Value storageCall(const Node &, const std::vector<Node> &);
  void track(Value &, llvm::GlobalVariable *GlobalSlot = nullptr);
  void trackLocal(Value &, llvm::StringRef Prefix);
  void ensureLive(const Value &, const Token &);
  llvm::Value *replaceGeneration(const Value &, const std::string &);
  void retireStorage(const Value &, bool Destroy, bool Explicit = false);
  void markStorageWrite(llvm::Value *);
  void forgetStorage();
  void joinStorage(const std::map<std::string, int> &);
  static bool usesStorage(const Node &);
  void cleanup(size_t, const std::set<SourcePosition> *Exited = nullptr);
  void cleanupScope(size_t, const std::set<SourcePosition> *Exited = nullptr);
  void endExpression(size_t From = 0);
  void consume(Value);
  bool adjust(Value &, const std::string &, const Token &, bool Emit = true);
  Value closure(const Node &);
  Value closurePointer(const Value &, const std::string &, const Token &);
  Value callClosure(Value, const std::vector<Node> &, const Token &);
  void bindCaptures();
  Value indirect(Value, const std::vector<Node> &, const Token &);
  Value endDivergentCall();
  void guard(llvm::Value *, llvm::StringRef Kind = {});
  void branch(llvm::BasicBlock *);
  const Family *constraint(const std::string &) const;
  bool predicate(const Node &);
  bool constructible(const std::string &, SpecialOperation, const Token &);
  bool typeCallee(const std::string &, const Token &);
  std::optional<std::string> memberQualifier(const std::string &, const Token &,
                                             std::string &);
  const Case *findCase(const std::string &, const Token &);
  Value variant(const Case &, const std::vector<Node> &, const Token &,
                llvm::Value *Dest = nullptr, bool Default = false,
                bool CheckInvariant = true);
  void visitPayload(Value, llvm::function_ref<void(const Case &)>);
  void dropPayload(Value);
  void transferPayload(Value, llvm::Value *, SpecialOperation, const Token &);
  void beginUnionConstructor();
  llvm::Value *payloadAddress(const Case &, llvm::Value *, unsigned);
  void match(const Node &);
  void constantMatch(const Node &);
  llvm::Constant *packVariant(const Case &, llvm::Constant *, const Token &);
  llvm::Constant *unpackVariant(const Case &, llvm::Constant *, const Token &);
  std::optional<ConstantPlace> constantPlace(const Node &);
  Value constantAddress(const ConstantPlace &, const Token &,
                        bool ExtentOnly = false);
  ConstantPlace constantPointerPlace(const Value &, const Token &);
  llvm::Value *fieldAddress(Value, unsigned);
  Value baseView(Value, const BasePath &);
  llvm::Value *ownerRecord(Value, unsigned);
  void enterOwnerLayer(Value);
  bool containsPointerField(const std::string &) const;
  bool containsDispatchState(const std::string &) const;
  Value constantAssignment(const Node &);
  Value constantCall(Function &, const std::vector<Node> &, const Token &,
                     Value Receiver = {});
  Function *constantOverload(const std::string &, const Node &,
                             const std::vector<Node> &, Value, Function *);
  Value constantTemporary(Value);
  Value constantSelf(const Token &);
  Value constantCopy(Value, const Token &, bool CheckInvariant = true,
                     Value *BaseDestination = nullptr);
  Value constantConstructor(Function &, const std::vector<Value> &,
                            const Token &, const Node *,
                            Value *BaseDestination = nullptr);
  Value constantAggregate(const std::string &, const std::vector<Node> &,
                          const Token &, const Node *,
                          Value *BaseDestination = nullptr);
  ConstantPlace constantBasePlace(ConstantPlace, const BasePath &) const;
  ConstantPlace constantFieldPlace(Value &, unsigned) const;
  Value constantField(Value &, unsigned, const Token &);
  void bindConstantVirtualLayout(Value &, const Token &);
  void finishVirtualBase(Value, unsigned);
  void bindVirtualLayout(Value);
  llvm::Value *snapshot(Value);
  void installTables(Value);
  void installConstantTables(Value &, const Token &);
  Function &constantVirtualTarget(Function &, Value &, const Token &);
  std::string methodOwner(const std::string &, const Token &);
  void bindParams();
  void endConstantScope();
  void constantDrop(Value, const Token &, bool AsBase = false,
                    bool RunOwnDestructor = true);
  void retireConstantCell(Value &, const Token &, bool Explicit = false,
                          bool Destroy = true);
  void retireConstantExtent(ConstantPlace, const Token &, bool Explicit,
                            bool Destroy, bool AsBase = false);
  Value constantStorageCall(const Node &, const std::vector<Node> &);
  Value storageViewObserver(Value, llvm::StringRef, const Token &);
  void endConstantField(const std::string &, bool, const Token &,
                        bool Explicit = false);
  void constructorBody(const Node &);
  void bindInlineParams(const std::vector<Value> &,
                        const Function *DefaultDeclaration = nullptr,
                        Value *DefaultReceiver = nullptr);
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
  Function *MethodContract = nullptr;
  using Facts = std::map<SourcePosition, std::map<size_t, unsigned>>;
  Facts Entries, Exits;
  void finishSlot(Frame &);
  std::pair<llvm::Function *, llvm::Value *> slotCallback(Frame &, unsigned);
  void findReservations(Frame &);
  void atEachPosition(Frame &, const std::function<void()> &);
  void publish(Frame &);
  void advance(Frame &);
  void enter(Frame &, size_t);
  void checkSlot(Frame &, size_t, const Token &,
                 llvm::Value *Designated = nullptr) const;

public:
  Construction(Frame &, Function &, Value, const Node *, Frame *);
  void run(Frame &);
  void rollback(Frame &) const;
  Value constantResult() const { return Object; }
  Construction(Frame &, Function &Method);
  llvm::Value *admitCall(Frame &, const Function &, const Token &);
  void checkReturn(const Token &) const;
  void delegate(Frame &, const Node &);
  using Positions = std::set<size_t>;
  Positions positions() const;
  void restore(const Positions &);
  void restoreFlow(const Node &, bool Exit = false);
  void checkAccess(Frame &, const Token &,
                   llvm::Value *Designated = nullptr) const;
  void checkBaseAccess(Frame &, const Value &, const Token &) const;
  void checkWholeView(Frame &, const Value &, const Token &) const;
  void checkReceiver(Frame &, const Function &, const Token &,
                     llvm::Value *Designated = nullptr) const;
  static bool mayAccess(const EffectBound &, const EffectSet &Predicate,
                        llvm::StringRef Region);
  void checkCallArguments(Frame &, llvm::ArrayRef<Value>,
                          llvm::ArrayRef<std::string>, const EffectBound &,
                          const EffectSet &Predicate, const Token &) const;
  std::optional<Value> firstWrite(Frame &, const Node &);
  bool needsDelegate(const Frame &) const;
};
} // namespace cpn
#endif
