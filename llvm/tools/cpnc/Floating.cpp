#include "NumericLiteral.h"
#include "Sema.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/IR/IntrinsicsX86.h"
using namespace cpn;
namespace {
llvm::RoundingMode rounding(const std::string &Name) {
  if (Name == "toward_zero")
    return llvm::RoundingMode::TowardZero;
  if (Name == "toward_positive_infinity")
    return llvm::RoundingMode::TowardPositive;
  if (Name == "toward_negative_infinity")
    return llvm::RoundingMode::TowardNegative;
  if (Name == "nearest_ties_away")
    return llvm::RoundingMode::NearestTiesToAway;
  return llvm::RoundingMode::NearestTiesToEven;
}

llvm::AllocaInst *mxcsrSlot(Frame &F) {
  llvm::IRBuilder<> Entry(F.IR->getEntryBlock().begin());
  return Entry.CreateAlloca(F.B.getInt32Ty(), nullptr, "fp.control");
}
llvm::Value *readMXCSR(Frame &F, llvm::Value *Cell) {
  F.B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
                     &F.U.M, llvm::Intrinsic::x86_sse_stmxcsr),
                 {Cell});
  return F.B.CreateLoad(F.B.getInt32Ty(), Cell);
}
void writeMXCSR(Frame &F, llvm::Value *Cell, llvm::Value *V) {
  F.B.CreateStore(V, Cell);
  F.B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
                     &F.U.M, llvm::Intrinsic::x86_sse_ldmxcsr),
                 {Cell});
}

// MXCSR contains the active rounding and subnormal controls, exception masks,
// and sticky history. An observed operation must classify its own events even
// when an identical event was already sticky on entry.
class FloatingOperation {
  Frame &F;
  llvm::AllocaInst *Cell = nullptr;
  llvm::Value *Saved = nullptr, *Traps = nullptr;
  static constexpr unsigned Rounding = 3u << 13;
  static constexpr unsigned Subnormal = (1u << 15) | (1u << 6);
  static constexpr unsigned Flags = 0x3f, Masks = Flags << 7, Events = 0x3d;

public:
  llvm::RoundingMode Mode;
  explicit FloatingOperation(Frame &F, bool Observed = false) : F(F) {
    const bool Strict = F.Opt.FPProfile == "strict";
    auto Name = F.Opt.FPRounding;
    if (Name.empty())
      Name = Strict ? "current" : "nearest_ties_even";
    if (Name == "current" && !F.Opt.InitialRounding.empty())
      Name = F.Opt.InitialRounding;
    Mode = Name == "current" ? llvm::RoundingMode::NearestTiesToEven
                             : rounding(Name);
    F.B.setIsFPConstrained(F.IR != nullptr);
    F.B.setDefaultConstrainedExcept(llvm::fp::ebStrict);
    F.B.setDefaultConstrainedRounding(llvm::RoundingMode::Dynamic);
    if (!F.IR)
      return;
    bool Preserve = F.Opt.FPSubnormal == "preserve" ||
                    (Observed && F.Opt.FPSubnormal.empty()) ||
                    ((F.Opt.FPSubnormal == "current" ||
                      (Strict && F.Opt.FPSubnormal.empty())) &&
                     F.Opt.InitialSubnormal == "preserve");
    if (!Observed && !Strict && !F.Opt.FPTrapMask && Name == "current" &&
        !Preserve)
      return;
    Cell = mxcsrSlot(F);
    Saved = readMXCSR(F, Cell);
    auto *Controls = Saved;
    if (Observed || Strict || F.Opt.FPTrapMask) {
      if (!Observed) {
        if (F.Opt.FPTrapMask || F.Opt.FPInitialTraps)
          Traps = F.B.getInt32(
              F.Opt.FPTrapMask.value_or(F.Opt.FPInitialTraps.value_or(0)));
        else
          Traps =
              F.B.CreateAnd(F.B.CreateNot(F.B.CreateLShr(Saved, 7)), Events);
      }
      Controls = F.B.CreateOr(F.B.CreateAnd(Controls, ~Flags), Masks);
    }
    if (Name != "current") {
      unsigned RC = Mode == llvm::RoundingMode::TowardNegative   ? 1
                    : Mode == llvm::RoundingMode::TowardPositive ? 2
                    : Mode == llvm::RoundingMode::TowardZero     ? 3
                                                                 : 0;
      Controls = F.B.CreateOr(F.B.CreateAnd(Controls, ~Rounding), RC << 13);
    }
    if (Preserve)
      Controls = F.B.CreateAnd(Controls, ~Subnormal);
    writeMXCSR(F, Cell, Controls);
  }
  llvm::Value *finish() {
    if (!Saved)
      return F.B.getInt32(0);
    auto *Local = F.B.CreateAnd(readMXCSR(F, Cell), Flags);
    writeMXCSR(F, Cell, F.B.CreateOr(Saved, Local));
    Saved = nullptr;
    if (Traps)
      F.guard(F.B.CreateIsNotNull(F.B.CreateAnd(Local, Traps)), "numeric");
    return F.B.CreateAnd(Local, Events);
  }
  ~FloatingOperation() { finish(); }
  static unsigned eventBits(llvm::APFloat::opStatus Status) {
    unsigned IEEE = Status;
    // APFloat has contiguous event bits. MXCSR reserves bit 1 for denormal
    // inputs.
    return (IEEE & 1) | ((IEEE & ~1u) << 1);
  }
  void check(llvm::APFloat::opStatus Status, const Token &At) const {
    if (eventBits(Status) &
        F.Opt.FPTrapMask.value_or(F.Opt.FPInitialTraps.value_or(0)))
      fail(At, "floating operation traps in constant evaluation");
  }
};

// Strict arithmetic selects the first quiet NaN, then the first signaling
// NaN. Representation operations do not themselves generate an FP event.
struct NaNBits {
  llvm::Value *Bits, *IsNaN, *IsQuiet;
  uint64_t Quiet, Exponent;
  NaNBits(llvm::IRBuilder<> &B, llvm::Value *V) {
    bool Single = V->getType()->isFloatTy();
    Quiet = uint64_t(1) << (Single ? 22 : 51);
    Exponent = Single ? 0x7f800000ULL : 0x7ff0000000000000ULL;
    Bits = B.CreateBitCast(V, B.getIntNTy(Single ? 32 : 64));
    auto *All =
        B.CreateICmpEQ(B.CreateAnd(Bits, Exponent),
                       llvm::ConstantInt::get(Bits->getType(), Exponent));
    auto *Payload = B.CreateAnd(Bits, 2 * Quiet - 1);
    IsNaN = B.CreateAnd(All, B.CreateIsNotNull(Payload));
    IsQuiet =
        B.CreateAnd(IsNaN, B.CreateIsNotNull(B.CreateAnd(Payload, Quiet)));
  }
};
llvm::Value *strictBinary(llvm::IRBuilder<> &B, llvm::Value *Out,
                          llvm::Value *Left, llvm::Value *Right) {
  NaNBits R(B, Out), X(B, Left), Y(B, Right);
  auto *Canonical =
      llvm::ConstantInt::get(R.Bits->getType(), R.Exponent | R.Quiet);
  auto *Bits = B.CreateSelect(R.IsNaN, Canonical, R.Bits);
  Bits = B.CreateSelect(Y.IsNaN, B.CreateOr(Y.Bits, Y.Quiet), Bits);
  Bits = B.CreateSelect(X.IsNaN, B.CreateOr(X.Bits, X.Quiet), Bits);
  Bits = B.CreateSelect(Y.IsQuiet, Y.Bits, Bits);
  return B.CreateBitCast(B.CreateSelect(X.IsQuiet, X.Bits, Bits),
                         Out->getType());
}
llvm::Value *strictCast(llvm::IRBuilder<> &B, llvm::Value *Out,
                        llvm::Value *Input) {
  NaNBits X(B, Input), R(B, Out);
  auto *Ty = R.Bits->getType();
  auto *Payload = B.CreateZExtOrTrunc(B.CreateAnd(X.Bits, X.Quiet - 1), Ty);
  auto *Body =
      B.CreateOr(B.CreateAnd(Payload, R.Quiet - 1), R.Exponent | R.Quiet);
  auto SignMask = llvm::APInt::getSignMask(Ty->getIntegerBitWidth());
  auto *Sign = B.CreateSelect(B.CreateIsNeg(X.Bits),
                              llvm::ConstantInt::get(Ty, SignMask),
                              llvm::ConstantInt::get(Ty, 0));
  return B.CreateBitCast(
      B.CreateSelect(X.IsNaN, B.CreateOr(Sign, Body), R.Bits), Out->getType());
}

llvm::Value *nonraisingCompare(llvm::IRBuilder<> &B, llvm::CmpInst::Predicate P,
                               llvm::Value *Left, llvm::Value *Right) {
  NaNBits X(B, Left), Y(B, Right);
  auto *Ty = X.Bits->getType();
  auto *Sign = llvm::ConstantInt::get(
      Ty, llvm::APInt::getSignMask(Ty->getIntegerBitWidth()));
  auto OrderedKey = [&](llvm::Value *Bits) {
    // Use a common encoding for both zeros and reverse the ordering of the
    // negative encodings. The integer comparisons never update FP status.
    auto *Zero = B.CreateIsNull(B.CreateAnd(Bits, B.CreateNot(Sign)));
    auto *Key = B.CreateSelect(B.CreateIsNeg(Bits), B.CreateNot(Bits),
                               B.CreateXor(Bits, Sign));
    return B.CreateSelect(Zero, Sign, Key);
  };
  auto *Ordered = B.CreateNot(B.CreateOr(X.IsNaN, Y.IsNaN));
  auto *A = OrderedKey(X.Bits), *D = OrderedKey(Y.Bits);
  switch (P) {
  case llvm::CmpInst::FCMP_OEQ:
    return B.CreateAnd(Ordered, B.CreateICmpEQ(A, D));
  case llvm::CmpInst::FCMP_UNE:
    return B.CreateOr(B.CreateNot(Ordered), B.CreateICmpNE(A, D));
  case llvm::CmpInst::FCMP_OLT:
    return B.CreateAnd(Ordered, B.CreateICmpULT(A, D));
  case llvm::CmpInst::FCMP_OLE:
    return B.CreateAnd(Ordered, B.CreateICmpULE(A, D));
  case llvm::CmpInst::FCMP_OGT:
    return B.CreateAnd(Ordered, B.CreateICmpUGT(A, D));
  case llvm::CmpInst::FCMP_OGE:
    return B.CreateAnd(Ordered, B.CreateICmpUGE(A, D));
  default:
    llvm_unreachable("invalid predicate comparison");
  }
}

struct BinaryFormat {
  unsigned Width, Fraction;
  int Bias;
  uint64_t ExponentMask;
};

BinaryFormat binaryFormat(llvm::StringRef Type) {
  return Type == "f32" ? BinaryFormat{32, 23, 127, 0xff}
                       : BinaryFormat{64, 52, 1023, 0x7ff};
}

// A finite source is (-1)^Negative * Magnitude * 2^Scale. Nonfinite
// encodings keep legal shift operands on paths discarded by classification.
struct BinaryCastSource {
  llvm::Value *Magnitude, *Scale, *Negative, *NonFinite, *NaN;
};

BinaryCastSource binaryCastSource(Frame &F, const Value &Source) {
  auto &B = F.B;
  if (integer(Source.Type)) {
    auto *Negative =
        signedType(Source.Type) ? B.CreateIsNeg(Source.IR) : B.getFalse();
    auto *Magnitude =
        B.CreateSelect(Negative, B.CreateNeg(Source.IR), Source.IR);
    if (Magnitude->getType()->getIntegerBitWidth() < 64)
      Magnitude = B.CreateZExt(Magnitude, B.getInt64Ty());
    return {Magnitude, B.getInt32(0), Negative, B.getFalse(), B.getFalse()};
  }
  const auto Format = binaryFormat(Source.Type);
  auto *Bits = B.CreateBitCast(Source.IR, B.getIntNTy(Format.Width));
  auto *Negative = B.CreateIsNeg(Bits);
  Bits = B.CreateZExtOrTrunc(Bits, B.getInt64Ty());
  const uint64_t Hidden = uint64_t(1) << Format.Fraction;
  auto *Exponent = B.CreateTrunc(
      B.CreateAnd(B.CreateLShr(Bits, Format.Fraction), Format.ExponentMask),
      B.getInt32Ty());
  auto *Fraction = B.CreateAnd(Bits, Hidden - 1);
  auto *Subnormal = B.CreateIsNull(Exponent);
  auto *Magnitude =
      B.CreateSelect(Subnormal, Fraction, B.CreateOr(Fraction, Hidden));
  auto *Scale = B.CreateSub(B.CreateSelect(Subnormal, B.getInt32(1), Exponent),
                            B.getInt32(Format.Bias + Format.Fraction));
  auto *NonFinite = B.CreateICmpEQ(Exponent, B.getInt32(Format.ExponentMask));
  return {Magnitude, Scale, Negative, NonFinite,
          B.CreateAnd(NonFinite, B.CreateIsNotNull(Fraction))};
}

struct ShiftCount {
  llvm::Value *InRange, *Count;
};

ShiftCount shiftCount(llvm::IRBuilder<> &B, llvm::Value *Distance,
                      llvm::IntegerType *Word) {
  auto *InRange = B.CreateICmpULT(Distance, B.getInt32(Word->getBitWidth()));
  return {InRange,
          B.CreateIntCast(B.CreateSelect(InRange, Distance, B.getInt32(0)),
                          Word, false)};
}

struct MagnitudeProjection {
  llvm::Value *Whole, *Increase, *Inexact, *LostHighBits;
};

MagnitudeProjection roundMagnitude(llvm::IRBuilder<> &B, llvm::Value *Mag,
                                   llvm::Value *Delta, llvm::Value *Negative,
                                   llvm::Value *Mode) {
  if (auto *D = llvm::dyn_cast<llvm::ConstantInt>(Delta); D && D->isZero())
    return {Mag, B.getFalse(), B.getFalse(), B.getFalse()};

  auto *Word = llvm::cast<llvm::IntegerType>(Mag->getType());
  auto *Zero = llvm::ConstantInt::get(Word, 0);
  auto *ShiftRight = B.CreateICmpSGT(Delta, B.getInt32(0));
  auto Right = shiftCount(B, Delta, Word);
  auto Left = shiftCount(B, B.CreateNeg(Delta), Word);
  auto *High = B.CreateSelect(Left.InRange, B.CreateShl(Mag, Left.Count), Zero);
  auto *Lost = B.CreateAnd(B.CreateNot(ShiftRight),
                           B.CreateICmpNE(B.CreateLShr(High, Left.Count), Mag));
  auto *Whole =
      B.CreateSelect(Right.InRange, B.CreateLShr(Mag, Right.Count), Zero);
  auto *Rest = B.CreateSub(Mag, B.CreateShl(Whole, Right.Count));
  auto HalfShift = shiftCount(B, B.CreateSub(Delta, B.getInt32(1)), Word);
  auto *Half = B.CreateShl(llvm::ConstantInt::get(Word, 1), HalfShift.Count);
  auto *Tie = B.CreateAnd(HalfShift.InRange, B.CreateICmpEQ(Rest, Half));
  auto *Above = B.CreateAnd(HalfShift.InRange, B.CreateICmpUGT(Rest, Half));
  auto *Odd = B.CreateTrunc(Whole, B.getInt1Ty());
  auto *Inexact = B.CreateAnd(ShiftRight, B.CreateIsNotNull(Rest));
  auto Is = [&](llvm::RoundingMode R) {
    return B.CreateICmpEQ(Mode, B.getInt8(unsigned(R)));
  };
  auto *NearestEven = B.CreateOr(Above, B.CreateAnd(Tie, Odd));
  auto *NearestAway = B.CreateOr(Above, Tie);
  auto *Increase = B.CreateSelect(Is(llvm::RoundingMode::NearestTiesToEven),
                                  NearestEven, B.getFalse());
  Increase = B.CreateSelect(Is(llvm::RoundingMode::NearestTiesToAway),
                            NearestAway, Increase);
  Increase = B.CreateSelect(Is(llvm::RoundingMode::TowardPositive),
                            B.CreateNot(Negative), Increase);
  Increase = B.CreateSelect(Is(llvm::RoundingMode::TowardNegative), Negative,
                            Increase);
  return {B.CreateSelect(ShiftRight, Whole, High),
          B.CreateAnd(Inexact, Increase), Inexact, Lost};
}

ScalarCastProjection integerCast(Frame &F, const BinaryCastSource &Source,
                                 unsigned Width, bool Signed,
                                 NumericProjection Policy, llvm::Value *Mode) {
  auto &B = F.B;
  const auto P = roundMagnitude(B, Source.Magnitude, B.CreateNeg(Source.Scale),
                                Source.Negative, Mode);
  auto *Word = llvm::cast<llvm::IntegerType>(P.Whole->getType());
  auto *Magnitude = B.CreateAdd(P.Whole, B.CreateZExt(P.Increase, Word));
  auto PositiveMax = Signed ? llvm::APInt::getSignedMaxValue(Width)
                            : llvm::APInt::getMaxValue(Width);
  auto NegativeMax =
      Signed ? llvm::APInt::getSignMask(Width) : llvm::APInt::getZero(Width);
  const unsigned WordWidth = Word->getBitWidth();
  auto *Maximum =
      B.CreateSelect(Source.Negative,
                     llvm::ConstantInt::get(Word, NegativeMax.zext(WordWidth)),
                     llvm::ConstantInt::get(Word, PositiveMax.zext(WordWidth)));
  auto *Outside =
      B.CreateOr(P.LostHighBits, B.CreateICmpUGT(Magnitude, Maximum));
  auto *Finite = B.CreateNot(Source.NonFinite);
  auto *Inexact = B.CreateAnd(Finite, P.Inexact);
  if (Policy == NumericProjection::Exact)
    Outside = B.CreateOr(
        Outside, B.CreateAnd(Inexact, B.CreateICmpEQ(P.Whole, Maximum)));
  Outside = B.CreateAnd(Finite, Outside);

  auto *Ty = B.getIntNTy(Width);
  auto *Bits = B.CreateZExtOrTrunc(Magnitude, Ty);
  auto *Number = B.CreateSelect(Source.Negative, B.CreateNeg(Bits), Bits);
  if (Policy == NumericProjection::Wrapping)
    return {Number,           B.getFalse(),
            Source.NonFinite, B.CreateOr(Inexact, Outside),
            B.getFalse(),     Outside};
  if (Policy == NumericProjection::Saturating) {
    auto *Clamp = B.CreateOr(
        Outside, B.CreateAnd(Source.NonFinite, B.CreateNot(Source.NaN)));
    auto *Bound =
        B.CreateSelect(Source.Negative, llvm::ConstantInt::get(Ty, NegativeMax),
                       llvm::ConstantInt::get(Ty, PositiveMax));
    return {B.CreateSelect(Clamp, Bound, Number), B.getFalse(), Source.NaN,
            B.CreateOr(Inexact, Outside),         Clamp,        B.getFalse()};
  }
  return {Number,  Outside,      Source.NonFinite,
          Inexact, B.getFalse(), B.getFalse()};
}

llvm::Value *bitLength(Frame &F, llvm::Value *V) {
  auto *Ty = V->getType();
  unsigned Width = Ty->getIntegerBitWidth();
  if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(V))
    return F.B.getInt32(C->getValue().getActiveBits());
  auto *Leading =
      F.B.CreateIntrinsic(llvm::Intrinsic::ctlz, {Ty}, {V, F.B.getFalse()});
  return F.B.CreateSub(F.B.getInt32(Width),
                       F.B.CreateIntCast(Leading, F.B.getInt32Ty(), false));
}

llvm::Value *roundedSignificand(llvm::IRBuilder<> &B,
                                const MagnitudeProjection &P) {
  return B.CreateAdd(B.CreateZExtOrTrunc(P.Whole, B.getInt64Ty()),
                     B.CreateZExt(P.Increase, B.getInt64Ty()));
}

llvm::Value *projectionEvents(llvm::IRBuilder<> &B, llvm::Value *Inexact,
                              llvm::Value *Overflow, llvm::Value *Underflow) {
  return B.CreateOr(
      B.CreateSelect(Inexact, B.getInt8(16), B.getInt8(0)),
      B.CreateOr(B.CreateSelect(Overflow, B.getInt8(4), B.getInt8(0)),
                 B.CreateSelect(Underflow, B.getInt8(8), B.getInt8(0))));
}

ScalarCastProjection floatingCast(Frame &F, const BinaryCastSource &Source,
                                  const std::string &Type,
                                  NumericProjection Policy, llvm::Value *Mode) {
  const auto Format = binaryFormat(Type);
  auto &B = F.B;
  auto *Length = bitLength(F, Source.Magnitude);
  auto *Zero = B.CreateIsNull(Length);
  auto *Exponent =
      B.CreateAdd(B.CreateSub(Length, B.getInt32(1)), Source.Scale);
  auto *PrecisionDelta = B.CreateSub(Length, B.getInt32(Format.Fraction + 1));

  // Chapter 04 checks range and tininess on the unbounded-exponent rounding.
  // The delivered representation rounds the original value at its final
  // binary quantum, including gradual subnormals.
  const auto Unbounded = roundMagnitude(B, Source.Magnitude, PrecisionDelta,
                                        Source.Negative, Mode);
  const uint64_t Leading = uint64_t(1) << Format.Fraction;
  auto *Rounded = roundedSignificand(B, Unbounded);
  auto *Carry = B.CreateICmpEQ(Rounded, B.getInt64(2 * Leading));
  auto *RoundedExponent =
      B.CreateAdd(Exponent, B.CreateZExt(Carry, B.getInt32Ty()));
  auto *Ordinary =
      B.CreateAnd(B.CreateNot(Zero), B.CreateNot(Source.NonFinite));
  auto *Outside = B.CreateICmpSGT(RoundedExponent, B.getInt32(Format.Bias));
  const bool Exact = Policy == NumericProjection::Exact;
  if (Exact) {
    auto *AboveMaximum =
        B.CreateAnd(Unbounded.Inexact,
                    B.CreateICmpEQ(Rounded, B.getInt64(2 * Leading - 1)));
    Outside = B.CreateOr(
        Outside, B.CreateAnd(B.CreateICmpEQ(Exponent, B.getInt32(Format.Bias)),
                             AboveMaximum));
  }
  Outside = B.CreateAnd(Ordinary, Outside);

  const int MinNormal = 1 - Format.Bias;
  auto *Subnormal = B.CreateICmpSLT(Exponent, B.getInt32(MinNormal));
  auto *SubnormalDelta =
      B.CreateSub(B.getInt32(MinNormal - int(Format.Fraction)), Source.Scale);
  const auto Delivered =
      roundMagnitude(B, Source.Magnitude,
                     B.CreateSelect(Subnormal, SubnormalDelta, PrecisionDelta),
                     Source.Negative, Mode);
  auto *Significand = roundedSignificand(B, Delivered);
  auto *Base =
      B.CreateSelect(Subnormal, B.getInt32(0),
                     B.CreateAdd(Exponent, B.getInt32(Format.Bias - 1)));
  auto *Bits = B.CreateAdd(
      B.CreateShl(B.CreateZExt(Base, B.getInt64Ty()), Format.Fraction),
      Significand);
  Bits = B.CreateSelect(Zero, B.getInt64(0), Bits);
  auto *Sign = B.CreateSelect(Source.Negative,
                              B.getInt64(uint64_t(1) << (Format.Width - 1)),
                              B.getInt64(0));
  auto *Ty = F.U.ir(Type);
  auto *Number = B.CreateBitCast(
      B.CreateZExtOrTrunc(B.CreateOr(Sign, Bits), B.getIntNTy(Format.Width)),
      Ty);
  auto *Inexact = B.CreateAnd(Ordinary, Delivered.Inexact);
  if (Exact)
    return {Number,  Outside,      Source.NonFinite,
            Inexact, B.getFalse(), B.getFalse()};
  Inexact = B.CreateOr(Inexact, Outside);
  auto *Underflow = B.CreateAnd(
      Inexact, B.CreateICmpSLT(RoundedExponent, B.getInt32(MinNormal)));
  return {Number,
          Outside,
          Source.NonFinite,
          Inexact,
          B.getFalse(),
          B.getFalse(),
          projectionEvents(B, Inexact, Outside, Underflow)};
}

ScalarCastProjection realLiteralCast(Frame &F, const Value &Source,
                                     const std::string &Type,
                                     NumericProjection Policy,
                                     llvm::Value *Mode, const Token &At) {
  auto &B = F.B;
  const bool IsFloat = floating(Type);
  const bool Exact = Policy == NumericProjection::Exact;
  const bool Signed = signedType(Type);
  const unsigned Width = width(Type);
  auto Project = [&](llvm::RoundingMode R) -> ScalarCastProjection {
    const auto P = projectRealLiteral(Source.RealText, Width, Signed, IsFloat,
                                      Exact, R, At);
    auto *Ty = B.getIntNTy(Width);
    llvm::Value *Number = llvm::ConstantInt::get(Ty, P.Bits);
    if (IsFloat)
      Number = B.CreateBitCast(Number, F.U.ir(Type));
    auto *FPFlags =
        IsFloat && !Exact
            ? projectionEvents(B, B.getInt1(P.Inexact), B.getInt1(P.FPOverflow),
                               B.getInt1(P.FPUnderflow))
            : B.getInt8(0);
    bool Outside = P.OutOfRange, Clamped = false, Wrapped = false;
    if (Policy == NumericProjection::Saturating && Outside) {
      const bool Negative = llvm::StringRef(Source.RealText).starts_with("-");
      llvm::APInt Bound = Negative
                              ? (Signed ? llvm::APInt::getSignedMinValue(Width)
                                        : llvm::APInt::getZero(Width))
                              : (Signed ? llvm::APInt::getSignedMaxValue(Width)
                                        : llvm::APInt::getMaxValue(Width));
      Number = llvm::ConstantInt::get(Ty, Bound);
      Clamped = true;
      Outside = false;
    } else if (Policy == NumericProjection::Wrapping && Outside) {
      Wrapped = true;
      Outside = false;
    }
    return {Number,
            B.getInt1(Outside),
            B.getFalse(),
            B.getInt1(P.Inexact || Wrapped || Clamped),
            B.getInt1(Clamped),
            B.getInt1(Wrapped),
            FPFlags};
  };
  if (auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Mode))
    return Project(llvm::RoundingMode(Known->getZExtValue()));

  // Preserve the token as an exact value even when a call computes its
  // rounding policy at runtime. Each arm is a compile-time projection.
  auto P = Project(llvm::RoundingMode::TowardZero);
  for (auto R : {llvm::RoundingMode::NearestTiesToEven,
                 llvm::RoundingMode::NearestTiesToAway,
                 llvm::RoundingMode::TowardPositive,
                 llvm::RoundingMode::TowardNegative}) {
    const auto Candidate = Project(R);
    auto *Selected = B.CreateICmpEQ(Mode, B.getInt8(unsigned(R)));
    P.Number = B.CreateSelect(Selected, Candidate.Number, P.Number);
    P.Outside = B.CreateSelect(Selected, Candidate.Outside, P.Outside);
    P.Inexact = B.CreateSelect(Selected, Candidate.Inexact, P.Inexact);
    P.Clamped = B.CreateSelect(Selected, Candidate.Clamped, P.Clamped);
    P.Wrapped = B.CreateSelect(Selected, Candidate.Wrapped, P.Wrapped);
    P.FPFlags = B.CreateSelect(Selected, Candidate.FPFlags, P.FPFlags);
  }
  return P;
}

llvm::Value *castRounding(Frame &F, bool Integer, bool Exact,
                          llvm::Value *Mode) {
  if (Mode)
    return Mode;
  auto &B = F.B;
  if (Integer || Exact)
    return B.getInt8(unsigned(llvm::RoundingMode::TowardZero));
  auto Name = F.Opt.FPRounding;
  if (Name.empty())
    Name = F.Opt.FPProfile == "strict" ? "current" : "nearest_ties_even";
  if (Name == "current" && !F.Opt.InitialRounding.empty())
    Name = F.Opt.InitialRounding;
  if (Name != "current" || !F.IR)
    return B.getInt8(unsigned(rounding(Name)));
  auto *Current = readMXCSR(F, mxcsrSlot(F));
  auto *RC = B.CreateTrunc(B.CreateLShr(Current, 13), B.getIntNTy(2));
  // MXCSR rounds to nearest, negative, positive, zero in this order.
  auto *Modes = B.getInt32(1 | (3 << 8) | (2 << 16));
  return B.CreateTrunc(
      B.CreateLShr(Modes, B.CreateShl(B.CreateZExt(RC, B.getInt32Ty()), 3)),
      B.getInt8Ty());
}

void mergeCastEvents(Frame &F, llvm::Value *Flags) {
  if (!F.IR || !Flags)
    return;
  if (auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Flags);
      Known && Known->isZero())
    return;
  auto *Cell = mxcsrSlot(F);
  auto *Current = readMXCSR(F, Cell);
  // Named floating destination casts raise only Overflow, Underflow and
  // Inexact. Set their sticky bits without activating any trap outlet.
  auto *Events = F.B.CreateShl(F.B.CreateZExt(Flags, F.B.getInt32Ty()), 1);
  writeMXCSR(F, Cell, F.B.CreateOr(Current, Events));
}
} // namespace

ScalarCastProjection Frame::projectScalarCast(Value Source,
                                              const std::string &Type,
                                              NumericProjection Policy,
                                              llvm::Value *Mode,
                                              const Token &At) {
  const bool IsFloat = floating(Type);
  const bool Exact = Policy == NumericProjection::Exact;
  if (IsFloat && !Opt.FloatFormats.count(Type))
    fail(At, "floating format is disabled");
  if (IsFloat && !Exact && InPredicate)
    fail(At, "contract predicate cannot update floating status");
  if (Policy == NumericProjection::Wrapping)
    Mode = nullptr;
  Mode = castRounding(*this, !IsFloat, Exact, Mode);
  auto Projection =
      Source.Type == "real"
          ? realLiteralCast(*this, Source, Type, Policy, Mode, At)
      : IsFloat ? floatingCast(*this, binaryCastSource(*this, Source), Type,
                               Policy, Mode)
                : integerCast(*this, binaryCastSource(*this, Source),
                              width(Type), signedType(Type), Policy, Mode);
  if (IsFloat && !Exact)
    mergeCastEvents(*this, Projection.FPFlags);
  return Projection;
}

Value Frame::floatingConvert(Value V, const std::string &T, const Token &At,
                             bool Explicit) {
  if (!Opt.FloatFormats.count(T))
    fail(At, "floating format is disabled");
  if (V.Type == T)
    return V;
  auto &Sem =
      T == "f32" ? llvm::APFloat::IEEEsingle() : llvm::APFloat::IEEEdouble();
  if (V.Type == "real") {
    auto Projection =
        projectRealLiteral(V.RealText, width(T), false, true, false,
                           rounding(Opt.LiteralRounding), At);
    if (Projection.FPOverflow)
      fail(At, "floating literal overflows " + T);
    return {T, llvm::ConstantFP::get(U.C, llvm::APFloat(Sem, Projection.Bits))};
  }
  if (V.Type == "integer") {
    auto Projection = floatingCast(
        *this, binaryCastSource(*this, V), T, NumericProjection::Checked,
        B.getInt8(unsigned(rounding(Opt.LiteralRounding))));
    if (!llvm::cast<llvm::ConstantInt>(Projection.Outside)->isZero())
      fail(At, "floating literal overflows " + T);
    return {T, Projection.Number};
  }
  if (InPredicate)
    fail(At, "contract predicate requires a nonraising floating conversion");
  if (!floating(V.Type)) {
    if (!Explicit || !integer(V.Type))
      fail(At, "cannot implicitly convert " + V.Type + " to " + T);
    FloatingOperation Policy(*this);
    if (!IR) {
      llvm::APFloat Result(Sem);
      Policy.check(Result.convertFromAPInt(
                       llvm::cast<llvm::ConstantInt>(V.IR)->getValue(),
                       signedType(V.Type), Policy.Mode),
                   At);
      return {T, llvm::ConstantFP::get(U.C, Result)};
    }
    return {T, signedType(V.Type) ? B.CreateSIToFP(V.IR, U.ir(T))
                                  : B.CreateUIToFP(V.IR, U.ir(T))};
  }
  if (T == "f32" && !Explicit) {
    auto *C = llvm::dyn_cast<llvm::ConstantFP>(V.IR);
    bool Lost = true;
    if (C) {
      auto Exact = C->getValueAPF();
      Exact.convert(Sem, llvm::RoundingMode::NearestTiesToEven, &Lost);
    }
    if (Lost)
      fail(At, "no implicit lossless floating conversion");
  }
  FloatingOperation Policy(*this);
  llvm::Value *Out;
  if (!IR) {
    auto Result = llvm::cast<llvm::ConstantFP>(V.IR)->getValueAPF();
    bool Loss;
    Policy.check(Result.convert(Sem, Policy.Mode, &Loss), At);
    Out = llvm::ConstantFP::get(U.C, Result);
  } else
    Out = T == "f64" ? B.CreateFPExt(V.IR, U.ir(T))
                     : B.CreateFPTrunc(V.IR, U.ir(T));
  return {T, Opt.FPProfile == "strict" ? strictCast(B, Out, V.IR) : Out};
}
Value Frame::floatingBinary(const Node &N, Value L, Value R,
                            const std::string &Expected,
                            llvm::Value **LocalFlags) {
  auto T = L.Type == "f64" || R.Type == "f64"   ? std::string("f64")
           : L.Type == "f32" || R.Type == "f32" ? "f32"
           : floating(Expected)                 ? Expected
                                                : Opt.DefaultReal;
  L = floatingConvert(L, T, N.At);
  R = floatingConvert(R, T, N.At);
  auto *X = L.IR, *Y = R.IR;
  auto &Op = N.Text;
  if (Op == "+" || Op == "-" || Op == "*" || Op == "/") {
    if (InPredicate)
      fail(N.At, "contract predicate cannot perform floating arithmetic");
    FloatingOperation Policy(*this, LocalFlags != nullptr);
    llvm::Value *Out;
    if (!IR) {
      auto Result = llvm::cast<llvm::ConstantFP>(X)->getValueAPF();
      auto &Right = llvm::cast<llvm::ConstantFP>(Y)->getValueAPF();
      auto Status = Op == "+"   ? Result.add(Right, Policy.Mode)
                    : Op == "-" ? Result.subtract(Right, Policy.Mode)
                    : Op == "*" ? Result.multiply(Right, Policy.Mode)
                                : Result.divide(Right, Policy.Mode);
      if (LocalFlags)
        *LocalFlags = B.getInt32(FloatingOperation::eventBits(Status));
      else
        Policy.check(Status, N.At);
      Out = llvm::ConstantFP::get(U.C, Result);
    } else if (Op == "+")
      Out = B.CreateFAdd(X, Y);
    else if (Op == "-")
      Out = B.CreateFSub(X, Y);
    else if (Op == "*")
      Out = B.CreateFMul(X, Y);
    else
      Out = B.CreateFDiv(X, Y);
    if (LocalFlags && IR)
      *LocalFlags = Policy.finish();
    return {T, LocalFlags || Opt.FPProfile == "strict"
                   ? strictBinary(B, Out, X, Y)
                   : Out};
  }
  llvm::CmpInst::Predicate P;
  if (Op == "==")
    P = llvm::CmpInst::FCMP_OEQ;
  else if (Op == "!=")
    P = llvm::CmpInst::FCMP_UNE;
  else if (Op == "<")
    P = llvm::CmpInst::FCMP_OLT;
  else if (Op == "<=")
    P = llvm::CmpInst::FCMP_OLE;
  else if (Op == ">")
    P = llvm::CmpInst::FCMP_OGT;
  else if (Op == ">=")
    P = llvm::CmpInst::FCMP_OGE;
  else
    fail(N.At, "unavailable floating operator '" + Op + "'");
  if (InPredicate)
    return {"bool", nonraisingCompare(B, P, X, Y)};
  FloatingOperation Policy(*this);
  return {"bool", B.CreateFCmp(P, X, Y)};
}
