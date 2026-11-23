#include "Sema.h"
#include "llvm/ADT/StringSwitch.h"

using namespace cpn;
using llvm::StringRef;

namespace {
enum class Operation {
  Add,
  Sub,
  Mul,
  Div,
  Rem,
  Neg,
  Abs,
  Shl,
  Shr,
  LogicalShr,
  EuclideanMod,
  Magnitude,
  Cast
};
enum class Projection { Checked, Wrapping, Saturating, Ordinary };
enum class BitOperation { Reinterpret, Extract, Insert };
enum class Extension { Source, Zero, Sign };
struct BitInterface {
  BitOperation Op;
  bool Result = false, Assign = false, Truncate = false;
};
struct NumericOperation {
  Operation Op;
  Projection Policy;
  bool Result = false, Assign = false, Report = false;
  bool unary() const {
    return Op == Operation::Neg || Op == Operation::Abs ||
           Op == Operation::Magnitude || Op == Operation::Cast;
  }
  bool shift() const {
    return Op == Operation::Shl || Op == Operation::Shr ||
           Op == Operation::LogicalShr;
  }
  bool division() const {
    return Op == Operation::Div || Op == Operation::Rem ||
           Op == Operation::EuclideanMod;
  }
  bool destination() const {
    return !Assign && !Report && Policy != Projection::Ordinary &&
           Op != Operation::LogicalShr && Op != Operation::Magnitude;
  }
};

StringRef numericName(StringRef Name) {
  Name.consume_front("::");
  Name.consume_front("std::numeric::");
  return Name;
}

std::optional<BitInterface> lookupBits(StringRef Name) {
  Name = numericName(Name);
  if (Name == "reinterpret_bits")
    return BitInterface{BitOperation::Reinterpret};
  bool Result = Name.consume_front("checked_");
  if (Name == "extract_bits")
    return BitInterface{BitOperation::Extract, Result};
  bool Assign = Name.consume_back("_assign");
  if (Name == "insert_bits" || Name == "insert_bits_trunc")
    return BitInterface{BitOperation::Insert, Result, Assign,
                        Name == "insert_bits_trunc"};
  return std::nullopt;
}

std::optional<Extension> extensionArgument(const Node &N) {
  if (N.K != Node::Name)
    return std::nullopt;
  return llvm::StringSwitch<std::optional<Extension>>(N.Text)
      .Case("Source", Extension::Source)
      .Case("Zero", Extension::Zero)
      .Case("Sign", Extension::Sign)
      .Default(std::nullopt);
}

std::optional<NumericOperation> lookupOperation(StringRef Name) {
  Name = numericName(Name);
  if (Name == "abs")
    return NumericOperation{Operation::Abs, Projection::Ordinary};
  if (Name == "magnitude")
    return NumericOperation{Operation::Magnitude, Projection::Wrapping};
  if (Name.consume_front("report_")) {
    auto Op = llvm::StringSwitch<std::optional<Operation>>(Name)
                  .Case("add", Operation::Add)
                  .Case("sub", Operation::Sub)
                  .Case("mul", Operation::Mul)
                  .Case("div", Operation::Div)
                  .Default(std::nullopt);
    if (!Op)
      return std::nullopt;
    return NumericOperation{*Op, Projection::Checked, false, false, true};
  }
  bool Result = Name.consume_front("try_");
  if (Name == "logical_shr")
    return NumericOperation{Operation::LogicalShr, Projection::Checked, Result};
  if (Name == "euclidean_mod")
    return NumericOperation{Operation::EuclideanMod, Projection::Checked,
                            Result};
  Projection Policy = Projection::Checked;
  if (Name.consume_front("wrapping_"))
    Policy = Projection::Wrapping;
  else if (Name.consume_front("saturating_"))
    Policy = Projection::Saturating;
  else if (Name == "exact_cast" || Name == "truncating_cast")
    return NumericOperation{Operation::Cast,
                            Name == "exact_cast" ? Projection::Checked
                                                 : Projection::Wrapping,
                            Result};
  else {
    const bool CheckedName = Name.consume_front("checked_");
    if ((!CheckedName && !Result) ||
        (Result && CheckedName != (Name == "cast")))
      return std::nullopt;
  }

  // Op aliases with projections absent from the standard catalogue are left
  // to ordinary source name lookup.
  bool Assign = Name.consume_back("_assign");
  auto Op = llvm::StringSwitch<std::optional<Operation>>(Name)
                .Case("add", Operation::Add)
                .Case("sub", Operation::Sub)
                .Case("mul", Operation::Mul)
                .Case("div", Operation::Div)
                .Case("rem", Operation::Rem)
                .Case("neg", Operation::Neg)
                .Case("abs", Operation::Abs)
                .Case("shl", Operation::Shl)
                .Case("shr", Operation::Shr)
                .Case("cast", Operation::Cast)
                .Default(std::nullopt);
  if (!Op ||
      (Assign && (Policy != Projection::Checked ||
                  (*Op != Operation::Add && *Op != Operation::Sub &&
                   *Op != Operation::Mul && *Op != Operation::Div))) ||
      (Policy != Projection::Checked &&
       (*Op == Operation::Abs || *Op == Operation::Shr)))
    return std::nullopt;
  return NumericOperation{*Op, Policy, Result, Assign};
}

std::string unsignedInteger(const std::string &T) { return "u" + T.substr(1); }

llvm::Constant *numericError(Context &U, StringRef Code) {
  return llvm::cast<llvm::Constant>(
      U.Globals.at(("std::numeric::NumericErrorCode::" + Code).str()).IR);
}

llvm::Value *numericStatus(Frame &F, llvm::Value *Inexact, llvm::Value *Clamped,
                           llvm::Value *Wrapped, llvm::Value *FPFlags) {
  auto *StatusType = F.U.ir("std::numeric::NumericStatus");
  llvm::Value *Status = llvm::Constant::getNullValue(StatusType);
  Status = F.B.CreateInsertValue(Status, Inexact, 0);
  Status = F.B.CreateInsertValue(Status, Clamped, 1);
  Status = F.B.CreateInsertValue(Status, Wrapped, 2);
  if (FPFlags) {
    auto *FlagsType = F.U.ir("std::numeric::FPFlagSet");
    auto *Flags = F.B.CreateInsertValue(llvm::Constant::getNullValue(FlagsType),
                                        FPFlags, 0);
    Status = F.B.CreateInsertValue(Status, Flags, 4);
  }
  return Status;
}

Value numericResult(Frame &F, const Token &At, const std::string &ResultType,
                    llvm::Value *Number, llvm::Value *Failed, llvm::Value *Code,
                    llvm::Value *Inexact, llvm::Value *Clamped,
                    llvm::Value *Wrapped, llvm::function_ref<void()> Commit,
                    llvm::Value *FPFlags = nullptr) {
  const auto Type =
      F.resolve("::std::numeric::NumericResult<" + ResultType + ">", At);
  const auto &Ok = F.U.Cases.at(Type + "::Ok");
  const auto &Err = F.U.Cases.at(Type + "::Err");
  auto *Status = numericStatus(F, Inexact, Clamped, Wrapped, FPFlags);
  auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Failed);
  if (!F.IR) {
    if (!Known)
      fail(At, "numeric result requires constant operands");
    bool Success = Known->isZero();
    if (Success && Commit)
      Commit();
    const auto &Alternative = Success ? Ok : Err;
    llvm::SmallVector<llvm::Constant *, 2> Payload;
    if (!Success || Number)
      Payload.push_back(llvm::cast<llvm::Constant>(Success ? Number : Code));
    Payload.push_back(llvm::cast<llvm::Constant>(Status));
    Value V{Type,
            F.packVariant(
                Alternative,
                llvm::ConstantStruct::get(Alternative.Payload, Payload), At)};
    V.Prvalue = V.Expiring = true;
    return V;
  }

  auto *Storage = F.resultAddress(Type, At);
  auto Finish = [&](bool Success) {
    const auto &Alternative = Success ? Ok : Err;
    unsigned I = 0;
    if (!Success || Number)
      F.B.CreateStore(Success ? Number : Code,
                      F.payloadAddress(Alternative, Storage, I++));
    F.B.CreateStore(Status, F.payloadAddress(Alternative, Storage, I));
    F.B.CreateStore(F.B.getInt32(Alternative.Tag),
                    F.B.CreateStructGEP(F.U.ir(Type), Storage, 0));
    if (Success && Commit)
      Commit();
  };
  if (Known)
    Finish(Known->isZero());
  else {
    auto *Success = F.block("numeric.ok"), *Failure = F.block("numeric.err"),
         *Done = F.block("numeric.result");
    F.B.CreateCondBr(Failed, Failure, Success);
    F.B.SetInsertPoint(Success);
    Finish(true);
    F.B.CreateBr(Done);
    F.B.SetInsertPoint(Failure);
    Finish(false);
    F.B.CreateBr(Done);
    F.B.SetInsertPoint(Done);
  }
  return F.callResult(Type, nullptr, At, Storage);
}

Value floatingResult(Frame &F, const Node &Call, const NumericOperation &Spec,
                     Value Left, Value Right) {
  if (Spec.Policy != Projection::Checked || Spec.Assign ||
      !Call.TemplateArgs.empty())
    fail(Call.At, "floating operation does not accept these arguments");
  Node Binary{Node::Binary, Call.At};
  switch (Spec.Op) {
  case Operation::Add:
    Binary.Text = "+";
    break;
  case Operation::Sub:
    Binary.Text = "-";
    break;
  case Operation::Mul:
    Binary.Text = "*";
    break;
  case Operation::Div:
    Binary.Text = "/";
    break;
  default:
    fail(Call.At, "no corresponding floating operation");
  }
  llvm::Value *Events = nullptr;
  auto Number = F.floatingBinary(Binary, Left, Right, "", &Events);
  auto &B = F.B;
  auto *Inexact = B.CreateIsNotNull(B.CreateAnd(Events, 32));
  // FPFlagSet uses five consecutive bits. MXCSR bit 1 is reserved here
  // because denormal inputs are not a CPN26 IEEE event.
  auto *DenseFlags = B.CreateOr(B.CreateAnd(Events, 1),
                                B.CreateLShr(B.CreateAnd(Events, 0x3c), 1));
  auto *Flags = B.CreateTrunc(DenseFlags, B.getInt8Ty());
  if (Spec.Report) {
    const auto Type = F.resolve(
        "::std::numeric::NumericReport<" + Number.Type + ">", Call.At);
    auto *Ty = F.U.ir(Type);
    auto *Status = numericStatus(F, Inexact, B.getFalse(), B.getFalse(), Flags);
    if (!F.IR) {
      auto *Image =
          llvm::ConstantStruct::get(llvm::cast<llvm::StructType>(Ty),
                                    {llvm::cast<llvm::Constant>(Number.IR),
                                     llvm::cast<llvm::Constant>(Status)});
      Value Result{Type, Image};
      Result.Prvalue = Result.Expiring = true;
      return Result;
    }
    auto *Storage = F.resultAddress(Type, Call.At);
    B.CreateStore(Number.IR, B.CreateStructGEP(Ty, Storage, 0));
    B.CreateStore(Status, B.CreateStructGEP(Ty, Storage, 1));
    return F.callResult(Type, nullptr, Call.At, Storage);
  }
  auto *Selected = B.CreateAnd(Events, F.Opt.FPResultMask);
  auto *Failed = B.CreateIsNotNull(Selected);
  if (F.Opt.FPRequireFinite) {
    const bool Single = Number.Type == "f32";
    const uint64_t Exponent = Single ? 0x7f800000ULL : 0x7ff0000000000000ULL;
    auto *Bits = B.CreateBitCast(Number.IR, B.getIntNTy(Single ? 32 : 64));
    auto *Mask = llvm::ConstantInt::get(Bits->getType(), Exponent);
    auto *NonFinite = B.CreateICmpEQ(B.CreateAnd(Bits, Mask), Mask);
    Failed = B.CreateOr(Failed, NonFinite);
  }
  if (!Spec.Result) {
    if (!F.IR && !llvm::cast<llvm::ConstantInt>(Failed)->isZero())
      fail(Call.At, "floating operation traps in constant evaluation");
    F.guard(Failed, "numeric");
    return Number;
  }

  // Check the lowest priority first so the highest selected event wins.
  llvm::Value *Code = numericError(F.U, "NonFinite");
  for (const auto &[Bit, Name] :
       std::array<std::pair<unsigned, StringRef>, 5>{{{32, "Inexact"},
                                                      {16, "Underflow"},
                                                      {8, "Overflow"},
                                                      {4, "DivideByZero"},
                                                      {1, "Invalid"}}}) {
    auto *Raised = B.CreateIsNotNull(B.CreateAnd(Selected, Bit));
    Code = B.CreateSelect(Raised, numericError(F.U, Name), Code);
  }
  return numericResult(F, Call.At, Number.Type, Number.IR, Failed, Code,
                       Inexact, B.getFalse(), B.getFalse(), {}, Flags);
}

Value numericTarget(Frame &F, const Node &Arg) {
  if (F.InPredicate)
    fail(Arg.At, "contract predicate cannot perform numeric assignment");
  Value Target;
  if (F.IR)
    Target = F.place(Arg);
  else if (auto Location = F.constantPlace(Arg)) {
    Target.Type = Location->Type;
    Target.Readonly = Location->Readonly;
    Target.Location = std::make_shared<ConstantPlace>(std::move(*Location));
  } else
    fail(Arg.At, "numeric assignment requires a mutable target");
  if (Target.Readonly || Target.Expiring || Target.Prvalue)
    fail(Arg.At, "numeric assignment requires a mutable lvalue");
  return Target;
}

Value deliverInteger(Frame &F, const Token &At, Value Number,
                     const Value &Target, llvm::Value *Failed,
                     llvm::Value *Code, llvm::Value *Changed,
                     llvm::Value *Clamped, llvm::Value *Wrapped) {
  bool Assign = !Target.Type.empty();
  auto Commit = [&] {
    if (F.IR)
      F.B.CreateStore(Number.IR, Target.Address);
    else
      Target.Location->write(F, Number, At);
  };
  if (Code)
    return numericResult(F, At, Assign ? "void" : Number.Type,
                         Assign ? nullptr : Number.IR, Failed, Code, Changed,
                         Clamped, Wrapped,
                         Assign ? llvm::function_ref<void()>(Commit)
                                : llvm::function_ref<void()>());
  if (auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Failed);
      Known && !Known->isZero()) {
    if (!F.IR)
      fail(At, "numeric operation fails in required constant evaluation");
    F.Opt.diagnose(At, Severity::Anomaly, {},
                   "named operation selects NumericTrap");
  }
  F.guard(Failed, "numeric");
  if (Assign)
    Commit();
  return Assign ? Value{"void"} : Number;
}

Value representationSource(Frame &F, Value Input, const Token &At) {
  if (!integer(Input.Type))
    fail(At, "bit operation requires a representation-width integer");
  return F.convert(Input, F.materializationType(Input.Type, At), At);
}

Value reinterpretBits(Frame &F, const Node &Call,
                      const std::vector<Node> &Args) {
  if (Call.TemplateArgs.size() != 1 || Args.empty() || Args.size() > 2)
    fail(Call.At, "reinterpret_bits requires a destination and a source");
  auto T = F.resolve(Call.TemplateArgs.front().Type, Call.At);
  if (!integer(T) || T == "integer")
    fail(Call.At,
         "bit reinterpretation requires an enabled integer destination");
  auto Source = F.load(F.eval(Args.front()));
  if (Source.Type == "never")
    return Source;
  Source = representationSource(F, std::move(Source), Call.At);
  auto ExtensionMode =
      Args.size() == 2 ? extensionArgument(Args.back()) : Extension::Source;
  if (!ExtensionMode)
    fail(Args.back().At, "bit extension must be Source, Zero or Sign");
  if (width(T) < width(Source.Type))
    F.Opt.diagnose(Call.At, Severity::Warning, "NUM002",
                   "bit reinterpretation discards high representation bits");
  return {T, F.B.CreateIntCast(Source.IR, F.U.ir(T),
                               *ExtensionMode == Extension::Sign ||
                                   (*ExtensionMode == Extension::Source &&
                                    signedType(Source.Type)))};
}

Value bitField(Frame &F, const Node &Call, const std::vector<Node> &Args,
               BitInterface Interface) {
  const bool Extract = Interface.Op == BitOperation::Extract;
  const bool Static = Extract && Call.TemplateArgs.size() == 2;
  if ((Extract && ((!Static && Call.TemplateArgs.size() != 1) ||
                   Args.size() != (Static ? 1u : 3u))) ||
      (!Extract && (!Call.TemplateArgs.empty() || Args.size() != 4)))
    fail(Call.At, "invalid bit field operation arguments");
  Value Target;
  Value Source;
  if (Interface.Assign)
    Target = numericTarget(F, Args.front());
  else
    Source = F.load(F.eval(Args.front()));
  auto Index = [&](unsigned I) {
    return Static ? F.load(F.constantEval(Call.TemplateArgs[I]))
                  : F.load(F.eval(Args[I + 1]));
  };
  auto Start = Index(0);
  auto Length = Index(1);
  Value Field;
  if (!Extract)
    Field = F.load(F.eval(Args[3]));
  if (Interface.Assign)
    Source = F.load(Target);
  if (Source.Type == "never" || Start.Type == "never" ||
      Length.Type == "never" || Field.Type == "never")
    return {"never"};
  Source = representationSource(F, std::move(Source), Call.At);
  if (!integer(Start.Type) || !integer(Length.Type))
    fail(Call.At, "bit range requires integer start and width");
  if (!Extract && !integer(Field.Type))
    fail(Call.At, "bit insertion requires an integer value");

  const unsigned N = width(Source.Type);
  auto &B = F.B;
  auto Bits = [](const Value &V) {
    return V.IR->getType()->getIntegerBitWidth();
  };
  auto *RangeType = B.getIntNTy(std::max({Bits(Start), Bits(Length), 8u}) + 1);
  auto *Zero = llvm::ConstantInt::get(RangeType, 0);
  auto *End = llvm::ConstantInt::get(RangeType, N);
  auto *S = B.CreateIntCast(Start.IR, RangeType, signedType(Start.Type));
  auto *W = B.CreateIntCast(Length.IR, RangeType, signedType(Length.Type));
  auto *BadStart = B.CreateICmpUGE(S, End);
  auto *BadWidth =
      B.CreateOr(B.CreateICmpSLE(W, Zero), B.CreateICmpUGT(W, End));
  auto *Remaining = B.CreateSub(End, B.CreateSelect(BadStart, Zero, S));
  auto *BadRange =
      B.CreateOr(B.CreateOr(BadStart, BadWidth), B.CreateICmpUGT(W, Remaining));
  auto KnownTrue = [](llvm::Value *Test) {
    auto *C = llvm::dyn_cast<llvm::ConstantInt>(Test);
    return C && C->isOne();
  };
  if (KnownTrue(BadStart) || KnownTrue(BadWidth) || KnownTrue(BadRange))
    fail(Call.At, "NUM001: statically invalid bit range");

  auto T = Source.Type;
  if (Static) {
    auto Width = llvm::cast<llvm::ConstantInt>(W)->getZExtValue();
    T = "u" + std::to_string(Width);
    if (!F.Opt.IntegerWidths.count(Width))
      fail(Call.At,
           "CFG002: bit extraction result type " + T + " is unavailable");
  } else if (Extract) {
    T = F.resolve(Call.TemplateArgs.front().Type, Call.At);
    if (T != "u8" && T != "u16" && T != "u32" && T != "u64")
      fail(Call.At,
           "bit extraction destination must be an unsigned fixed integer");
    BadRange = B.CreateOr(
        BadRange,
        B.CreateICmpUGT(W, llvm::ConstantInt::get(RangeType, width(T))));
  }
  // Keep the shifts defined even on a failing Result path. A one-bit wider
  // work type also handles an admitted full-width mask.
  auto *Work = B.getIntNTy(N + 1);
  auto *SafeStart =
      B.CreateIntCast(B.CreateSelect(BadRange, Zero, S), Work, false);
  auto *SafeWidth =
      B.CreateIntCast(B.CreateSelect(BadRange, Zero, W), Work, false);
  auto *One = llvm::ConstantInt::get(Work, 1);
  auto *Mask = B.CreateSub(B.CreateShl(One, SafeWidth), One);
  auto *Input = B.CreateZExt(Source.IR, Work);
  llvm::Value *Failure = BadRange;
  llvm::Value *Changed = B.getFalse();
  llvm::Value *Output;
  if (Extract)
    Output = B.CreateAnd(B.CreateLShr(Input, SafeStart), Mask);
  else {
    auto *FieldType = B.getIntNTy(std::max(N, Bits(Field)) + 1);
    auto *Exact = B.CreateIntCast(Field.IR, FieldType, signedType(Field.Type));
    auto *Bound = B.CreateIntCast(Mask, FieldType, false);
    auto *DoesNotFit =
        B.CreateOr(B.CreateIsNeg(Exact), B.CreateICmpUGT(Exact, Bound));
    auto *Selected = B.CreateAnd(B.CreateIntCast(Exact, Work, false), Mask);
    auto *Cleared =
        B.CreateAnd(Input, B.CreateNot(B.CreateShl(Mask, SafeStart)));
    Output = B.CreateOr(Cleared, B.CreateShl(Selected, SafeStart));
    if (Interface.Truncate)
      Changed = B.CreateAnd(DoesNotFit, B.CreateNot(BadRange));
    else
      Failure = B.CreateOr(BadRange, DoesNotFit);
  }
  llvm::Value *Code = nullptr;
  if (Interface.Result)
    Code = B.CreateSelect(BadRange, numericError(F.U, "InvalidBitRange"),
                          numericError(F.U, "OutOfRange"));
  return deliverInteger(F, Call.At,
                        {T, B.CreateIntCast(Output, F.U.ir(T), false)}, Target,
                        Failure, Code, Changed, B.getFalse(), Changed);
}
} // namespace

bool cpn::integerLibraryName(StringRef Name, bool ExplicitDestination) {
  if (auto Bits = lookupBits(Name))
    return !ExplicitDestination || Bits->Op != BitOperation::Insert;
  auto Op = lookupOperation(Name);
  return Op && (!ExplicitDestination || Op->destination());
}

bool cpn::bitExtractionName(StringRef Name) {
  Name = numericName(Name);
  return Name == "extract_bits" || Name == "checked_extract_bits";
}

bool cpn::bitExtensionArgument(const Node &Call) {
  auto &A = Call.Children;
  return Call.K == Node::Call && A.size() == 3 && A.front().K == Node::Name &&
         numericName(A.front().Text) == "reinterpret_bits" &&
         extensionArgument(A.back()).has_value();
}

bool cpn::usesNumericLibrary(const Node &D) {
  if (StringRef(D.Type).contains("std::numeric::") ||
      StringRef(D.Text).contains("std::numeric::") ||
      (D.K == Node::Name && integerLibraryName(D.Text)))
    return true;
  for (const auto *Nodes : {&D.Children, &D.Params, &D.Generics,
                            &D.TemplateArgs, &D.Pattern, &D.Contracts})
    if (llvm::any_of(*Nodes, usesNumericLibrary))
      return true;
  return false;
}

void Context::bindNumericLibrary() {
  // The provider's private u8 representation remains available even when
  // the source restricts its own fixed-width arithmetic types.
  llvm::SaveAndRestore Policy(Opt);
  Opt.IntegerWidths.insert(8);
  auto Library = parse(R"cpn(
    namespace std {
      namespace numeric {
        enum NumericErrorCode : u8 {
          case OutOfRange(0), case NonFinite(1),
          case NotExactlyRepresentable(2), case ZeroDivisor(3),
          case NonTerminatingExpansion(4), case InvalidOperation(5),
          case InvalidShift(6), case InvalidBitRange(7), case ResourceLimit(8),
          case AllocationFailure(9), case TransferUnavailable(10),
          case Invalid(11), case DivideByZero(12), case Overflow(13),
          case Underflow(14), case Inexact(15)
        };
        enum FPFlag : u8 {
          case Invalid(0), case DivideByZero(1), case Overflow(2),
          case Underflow(3), case Inexact(4)
        };
        class FPFlagSet {
          u8 bits;
          constexpr static u8 bit(FPFlag flag) noexcept {
            if(flag==FPFlag::Invalid){return 1;}
            if(flag==FPFlag::DivideByZero){return 2;}
            if(flag==FPFlag::Overflow){return 4;}
            if(flag==FPFlag::Underflow){return 8;}
            return 16;
          }
          FPFlagSet(u8 mask) noexcept { init bits(mask); }
        public:
          FPFlagSet() noexcept {}
          FPFlagSet(FPFlag flag) noexcept { init bits(bit(flag)); }
          FPFlagSet(const<FPFlagSet>& other)=default;
          FPFlagSet(FPFlagSet&& other)=default;
          FPFlagSet& operator=(const<FPFlagSet>& other)=default;
          FPFlagSet& operator=(FPFlagSet&& other)=default;
          constexpr bool empty() const noexcept { return bits==0; }
          constexpr bool contains(FPFlag flag) const noexcept {
            return (bits & bit(flag))!=0;
          }
          constexpr bool operator==(const<FPFlagSet>& other) const noexcept {
            return bits==other.bits;
          }
          constexpr FPFlagSet operator|(const<FPFlagSet>& other) const noexcept {
            return FPFlagSet(bits | other.bits);
          }
          constexpr FPFlagSet operator&(const<FPFlagSet>& other) const noexcept {
            return FPFlagSet(bits & other.bits);
          }
          constexpr FPFlagSet operator^(const<FPFlagSet>& other) const noexcept {
            return FPFlagSet(bits ^ other.bits);
          }
          constexpr FPFlagSet operator~() const noexcept {
            return FPFlagSet(bits ^ u8(31));
          }
          constexpr FPFlagSet& operator|=(const<FPFlagSet>& other) noexcept {
            bits |= other.bits;
            return *this;
          }
          constexpr FPFlagSet& operator&=(const<FPFlagSet>& other) noexcept {
            bits &= other.bits;
            return *this;
          }
          constexpr FPFlagSet& operator^=(const<FPFlagSet>& other) noexcept {
            bits ^= other.bits;
            return *this;
          }
        };
        struct NumericStatus {
          bool value_inexact; bool clamped; bool wrapped;
          bool payload_changed; FPFlagSet fp_flags;
          NumericStatus(const<NumericStatus>& other)=default;
          NumericStatus(NumericStatus&& other)=default;
          NumericStatus& operator=(const<NumericStatus>& other)=default;
          NumericStatus& operator=(NumericStatus&& other)=default;
        };
        generic<type T> struct NumericReport {
          T value;
          NumericStatus status;
        };
        generic<type T> union NumericResult {
          case Ok(T value, NumericStatus status);
          case Err(NumericErrorCode code, NumericStatus status);
          NumericResult(const<NumericResult>& other)=default;
          NumericResult(NumericResult&& other)=default;
        };
        specialize union NumericResult<void> {
          case Ok(NumericStatus status);
          case Err(NumericErrorCode code, NumericStatus status);
          NumericResult(const<NumericResult>& other)=default;
          NumericResult(NumericResult&& other)=default;
        };
      }
    }
  )cpn",
                       Opt);
  // Keep library family declaration sites distinct from source families and
  // from the separately bound Core Result declarations.
  for (auto [Index, Decl] :
       llvm::enumerate(Library.front().Children.front().Children)) {
    Decl.At.Line = 0;
    Decl.At.Column = Index + 100;
  }
  unit(Library);
}

std::optional<Value> Frame::namedInteger(const Node &Call, StringRef Name,
                                         const std::vector<Node> &Args) {
  if (Call.K != Node::Name)
    return std::nullopt;
  if (auto Bits = lookupBits(Name))
    return Bits->Op == BitOperation::Reinterpret
               ? reinterpretBits(*this, Call, Args)
               : bitField(*this, Call, Args, *Bits);
  auto Spec = lookupOperation(Name);
  if (!Spec)
    return std::nullopt;
  const auto &[Op, Policy, Fallible, Assign, Report] = *Spec;
  if (Args.size() != (Spec->unary() ? 1u : 2u) ||
      Call.TemplateArgs.size() > (Spec->destination() ? 1u : 0u) ||
      (Op == Operation::Cast && Call.TemplateArgs.empty()))
    fail(Call.At, "invalid named numeric operation arguments");
  Value Target;
  Value Left;
  if (Assign)
    Target = numericTarget(*this, Args.front());
  else
    Left = load(eval(Args.front()));
  if (Left.Type == "never")
    return Value{"never"};
  Value Right;
  if (!Spec->unary())
    Right = load(eval(Args[1]));
  if (Assign)
    Left = load(Target);
  if (Right.Type == "never")
    return Value{"never"};
  if (floating(Left.Type) || Left.Type == "real" || floating(Right.Type) ||
      Right.Type == "real")
    return floatingResult(*this, Call, *Spec, std::move(Left),
                          std::move(Right));
  if (Report)
    fail(Call.At, "named floating report requires floating operands");
  if (!integer(Left.Type) || (!Spec->unary() && !integer(Right.Type)))
    fail(Call.At, "CFG002: named numeric operation requires an available "
                  "integer interface");

  const bool Explicit = !Call.TemplateArgs.empty();
  std::string T;
  if (Assign)
    T = Left.Type;
  else if (Explicit) {
    T = resolve(Call.TemplateArgs.front().Type, Call.At);
    if (!integer(T) || T == "integer")
      fail(Call.At,
           "named integer destination must be an enabled integer type");
  } else if (Spec->unary() || Spec->shift())
    T = materializationType(Left.Type, Call.At);
  else
    T = commonIntegerType(Left.Type, Right.Type, Call.At);
  if (!Spec->unary() && !Spec->shift() && Left.Type != "integer" &&
      Right.Type != "integer" &&
      StringRef(Left.Type).ends_with("size") !=
          StringRef(Right.Type).ends_with("size"))
    fail(Call.At, "incompatible integer families");
  if (!Explicit && !Assign) {
    Left = convert(Left, T, Call.At);
    if (!Spec->unary() && !Spec->shift())
      Right = convert(Right, T, Call.At);
  }
  if (Op == Operation::Magnitude || Op == Operation::LogicalShr)
    T = resolve(unsignedInteger(T), Call.At);

  const unsigned N = width(T);
  unsigned A = Left.IR->getType()->getIntegerBitWidth();
  unsigned D = Right.IR ? Right.IR->getType()->getIntegerBitWidth() : 0;
  unsigned Bits = std::max({N, A, Spec->shift() ? 0u : D}) + 2;
  if (Op == Operation::Mul)
    Bits = std::max(Bits, A + D + 1);
  else if (Op == Operation::Shl)
    Bits = std::max(Bits, A + N + 1);
  auto *Wide = B.getIntNTy(Bits);
  auto *X = B.CreateIntCast(
      Left.IR, Wide, signedType(Left.Type) && Op != Operation::LogicalShr);
  llvm::Value *BadDomain = B.getFalse();
  StringRef DomainCode;
  llvm::Value *Y = nullptr;
  if (Spec->shift()) {
    auto *Count = B.CreateIntCast(Right.IR, B.getIntNTy(std::max(D, 8u)),
                                  signedType(Right.Type));
    auto *Limit = llvm::ConstantInt::get(Count->getType(), N);
    BadDomain = B.CreateICmpUGE(Count, Limit);
    Y = B.CreateSelect(BadDomain, llvm::ConstantInt::get(Wide, 0),
                       B.CreateIntCast(Count, Wide, false));
    DomainCode = "InvalidShift";
  } else if (!Spec->unary()) {
    Y = B.CreateIntCast(Right.IR, Wide, signedType(Right.Type));
    if (Spec->division()) {
      BadDomain = B.CreateIsNull(Y);
      Y = B.CreateSelect(BadDomain, llvm::ConstantInt::get(Wide, 1), Y);
      DomainCode = "ZeroDivisor";
    }
  }

  llvm::Value *Exact = X;
  switch (Op) {
  case Operation::Add:
    Exact = B.CreateAdd(X, Y);
    break;
  case Operation::Sub:
    Exact = B.CreateSub(X, Y);
    break;
  case Operation::Mul:
    Exact = B.CreateMul(X, Y);
    break;
  case Operation::Div:
    Exact = B.CreateSDiv(X, Y);
    break;
  case Operation::Rem:
    Exact = B.CreateSRem(X, Y);
    break;
  case Operation::Neg:
    Exact = B.CreateNeg(X);
    break;
  case Operation::Abs:
  case Operation::Magnitude:
    Exact = B.CreateSelect(B.CreateIsNeg(X), B.CreateNeg(X), X);
    break;
  case Operation::Shl:
    Exact = B.CreateShl(X, Y);
    break;
  case Operation::Shr:
    Exact = B.CreateAShr(X, Y);
    break;
  case Operation::LogicalShr:
    Exact = B.CreateLShr(X, Y);
    break;
  case Operation::EuclideanMod: {
    auto *Remainder = B.CreateSRem(X, Y);
    auto *Magnitude = B.CreateSelect(B.CreateIsNeg(Y), B.CreateNeg(Y), Y);
    Exact = B.CreateSelect(B.CreateIsNeg(Remainder),
                           B.CreateAdd(Remainder, Magnitude), Remainder);
    break;
  }
  case Operation::Cast:
    break;
  }

  auto *Minimum = llvm::ConstantInt::get(
      Wide, signedType(T) ? llvm::APInt::getSignedMinValue(N).sext(Bits)
                          : llvm::APInt(Bits, 0));
  auto *Maximum = llvm::ConstantInt::get(
      Wide, signedType(T) ? llvm::APInt::getSignedMaxValue(N).sext(Bits)
                          : llvm::APInt::getMaxValue(N).zext(Bits));
  auto *Low = B.CreateICmpSLT(Exact, Minimum);
  auto *High = B.CreateICmpSGT(Exact, Maximum);
  auto *Outside = B.CreateOr(Low, High);
  const bool Checked =
      Policy == Projection::Checked ||
      (Policy == Projection::Ordinary && Opt.Overflow == "checked");
  const bool Saturating =
      Policy == Projection::Saturating ||
      (Policy == Projection::Ordinary && Opt.Overflow == "saturating");
  auto *Failed = Checked ? B.CreateOr(BadDomain, Outside) : BadDomain;
  auto *Number = B.CreateTrunc(
      Saturating
          ? B.CreateSelect(Low, Minimum, B.CreateSelect(High, Maximum, Exact))
          : Exact,
      U.ir(T, Call.At));
  auto *Changed =
      Checked ? B.getFalse() : B.CreateAnd(Outside, B.CreateNot(BadDomain));
  llvm::Value *Code = nullptr;
  if (Fallible) {
    Code = numericError(U, "OutOfRange");
    if (!DomainCode.empty())
      Code = B.CreateSelect(BadDomain, numericError(U, DomainCode), Code);
  }
  return deliverInteger(*this, Call.At, {T, Number}, Target, Failed, Code,
                        Changed, Saturating ? Changed : B.getFalse(),
                        Saturating ? B.getFalse() : Changed);
}
