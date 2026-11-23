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
struct NumericOperation {
  Operation Op;
  Projection Policy;
  bool Result = false, Assign = false;
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
    return !Assign && Policy != Projection::Ordinary &&
           Op != Operation::LogicalShr && Op != Operation::Magnitude;
  }
};

std::optional<NumericOperation> lookupOperation(StringRef Name) {
  Name.consume_front("::");
  Name.consume_front("std::numeric::");
  if (Name == "abs")
    return NumericOperation{Operation::Abs, Projection::Ordinary};
  if (Name == "magnitude")
    return NumericOperation{Operation::Magnitude, Projection::Wrapping};
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

Value numericResult(Frame &F, const Token &At, const std::string &ResultType,
                    llvm::Value *Number, llvm::Value *Failed, llvm::Value *Code,
                    llvm::Value *Inexact, llvm::Value *Clamped,
                    llvm::Value *Wrapped, llvm::function_ref<void()> Commit) {
  const auto Type =
      F.resolve("::std::numeric::NumericResult<" + ResultType + ">", At);
  const auto &Ok = F.U.Cases.at(Type + "::Ok");
  const auto &Err = F.U.Cases.at(Type + "::Err");
  auto *StatusType = F.U.ir("std::numeric::NumericStatus");
  llvm::Value *Status = llvm::Constant::getNullValue(StatusType);
  Status = F.B.CreateInsertValue(Status, Inexact, 0);
  Status = F.B.CreateInsertValue(Status, Clamped, 1);
  Status = F.B.CreateInsertValue(Status, Wrapped, 2);
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
} // namespace

bool cpn::integerLibraryName(StringRef Name, bool ExplicitDestination) {
  auto Op = lookupOperation(Name);
  return Op && (!ExplicitDestination || Op->destination());
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
  auto Spec = lookupOperation(Name);
  if (!Spec)
    return std::nullopt;
  const auto &[Op, Policy, Fallible, Assign] = *Spec;
  if (Args.size() != (Spec->unary() ? 1u : 2u) ||
      Call.TemplateArgs.size() > (Spec->destination() ? 1u : 0u) ||
      (Op == Operation::Cast && Call.TemplateArgs.empty()))
    fail(Call.At, "invalid named numeric operation arguments");
  if (InPredicate && Assign)
    fail(Call.At, "contract predicate cannot perform numeric assignment");

  Value Target;
  Value Left;
  if (Assign) {
    if (IR)
      Target = place(Args.front());
    else if (auto Location = constantPlace(Args.front())) {
      Target.Type = Location->Type;
      Target.Readonly = Location->Readonly;
      Target.Location = std::make_shared<ConstantPlace>(std::move(*Location));
    } else
      fail(Args.front().At, "numeric assignment requires a mutable target");
    if (Target.Readonly)
      fail(Args.front().At, "numeric assignment to a read-only target");
  } else
    Left = load(eval(Args.front()));
  Value Right;
  if (!Spec->unary())
    Right = load(eval(Args[1]));
  if (Assign)
    Left = load(Target);
  if (Left.Type == "never" || Right.Type == "never")
    return Value{"never"};
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
  auto Commit = [&] {
    if (IR)
      B.CreateStore(Number, Target.Address);
    else
      Target.Location->write(*this, {T, Number}, Call.At);
  };
  if (!Fallible) {
    if (auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Failed);
        Known && !Known->isZero()) {
      if (!IR)
        fail(Call.At,
             "numeric operation fails in required constant evaluation");
      Opt.diagnose(Call.At, Severity::Anomaly, "NUM002",
                   "named operation selects NumericTrap");
    }
    guard(Failed, "numeric");
    if (Assign)
      Commit();
    return Assign ? Value{"void"} : Value{T, Number};
  }
  auto *Changed =
      Checked ? B.getFalse() : B.CreateAnd(Outside, B.CreateNot(BadDomain));
  llvm::Value *Code = numericError(U, "OutOfRange");
  if (!DomainCode.empty())
    Code = B.CreateSelect(BadDomain, numericError(U, DomainCode), Code);
  return numericResult(*this, Call.At, Assign ? "void" : T,
                       Assign ? nullptr : Number, Failed, Code, Changed,
                       Saturating ? Changed : B.getFalse(),
                       Saturating ? B.getFalse() : Changed,
                       Assign ? llvm::function_ref<void()>(Commit)
                              : llvm::function_ref<void()>());
}
