#include "NumericLiteral.h"
#include "Frontend.h"

using namespace cpn;
using llvm::APInt;
using llvm::RoundingMode;
using llvm::StringRef;

namespace {
struct Quotient {
  APInt Magnitude;
  bool Inexact;
};

// The parsed magnitude is Numerator / Denominator * 2^Scale. In particular,
// a decimal exponent only requires constructing a power of five here.
struct BinaryRational {
  APInt Numerator, Denominator;
  int64_t Scale;
  bool Negative;

  int64_t exponent() const;
  Quotient project(int64_t Quantum, RoundingMode Mode) const;
};

int64_t decimalExponent(StringRef Text) {
  // The scanner has validated the exponent digits. Saturating the exponent
  // above any supported significand length or destination range is enough
  // to classify finite magnitudes and compute their destination encoding.
  constexpr int64_t Limit = 1000000;
  bool Negative = Text.consume_front("-");
  Text.consume_front("+");
  int64_t Number = 0;
  for (char C : Text) {
    Number = std::min(Limit, Number * 10 + (C - '0'));
    if (Number == Limit)
      break;
  }
  return Negative ? -Number : Number;
}

APInt powerOfFive(unsigned Exponent) {
  const unsigned Width = 3 * Exponent + 1;
  APInt Accumulator(Width, 1), Power(Width, 5);
  while (Exponent) {
    if (Exponent & 1)
      Accumulator *= Power;
    Exponent >>= 1;
    if (Exponent)
      Power *= Power;
  }
  return Accumulator;
}

bool directedAwayFromZero(RoundingMode Mode, bool Negative) {
  return Mode == (Negative ? RoundingMode::TowardNegative
                           : RoundingMode::TowardPositive);
}

int64_t BinaryRational::exponent() const {
  const unsigned A = Numerator.getActiveBits(), D = Denominator.getActiveBits();
  const unsigned Width = std::max(A, D);
  const int64_t Difference = int64_t(A) - D;
  auto N = Numerator.zextOrTrunc(Width), B = Denominator.zextOrTrunc(Width);
  const bool Below =
      Difference < 0 ? N.shl(-Difference).ult(B) : N.ult(B.shl(Difference));
  return Scale + Difference - Below;
}

Quotient BinaryRational::project(int64_t Quantum, RoundingMode Mode) const {
  const auto Shift = Scale - Quantum;
  const auto Left = unsigned(std::max<int64_t>(Shift, 0));
  const auto Right = unsigned(std::max<int64_t>(-Shift, 0));
  const unsigned Width = 1 + std::max(Numerator.getActiveBits() + Left,
                                      Denominator.getActiveBits() + Right);
  const auto N = Numerator.zextOrTrunc(Width).shl(Left);
  const auto D = Denominator.zextOrTrunc(Width).shl(Right);
  APInt Value, Remainder;
  APInt::udivrem(N, D, Value, Remainder);
  if (Remainder.isZero())
    return {std::move(Value), false};

  bool Increment = directedAwayFromZero(Mode, Negative);
  if (Mode == RoundingMode::NearestTiesToEven ||
      Mode == RoundingMode::NearestTiesToAway) {
    const auto Twice = Remainder.shl(1);
    Increment =
        Twice.ugt(D) ||
        (Twice == D && (Mode == RoundingMode::NearestTiesToAway || Value[0]));
  }
  if (Increment)
    ++Value;
  return {std::move(Value), true};
}

RealLiteralProjection projectInteger(Quotient Q, unsigned Width, bool Signed,
                                     bool Negative, bool Exact) {
  const auto Limit =
      !Signed    ? (Negative ? APInt(Width, 0) : APInt::getMaxValue(Width))
      : Negative ? APInt::getSignMask(Width)
                 : APInt::getSignedMaxValue(Width);
  const unsigned CompareWidth = std::max(Width, Q.Magnitude.getBitWidth());
  const auto Wide = Q.Magnitude.zext(CompareWidth);
  const auto Bound = Limit.zext(CompareWidth);
  const bool Outside = Wide.ugt(Bound) || (Exact && Q.Inexact && Wide == Bound);
  auto Bits = Q.Magnitude.zextOrTrunc(Width);
  if (Negative)
    Bits.negate();
  return {std::move(Bits), Q.Inexact, Outside};
}

struct BinaryFormat {
  unsigned Width, Fraction;
  int64_t MaxExponent;

  explicit BinaryFormat(unsigned Width)
      : Width(Width), Fraction(Width == 32 ? 23 : 52),
        MaxExponent(Width == 32 ? 127 : 1023) {}
  int64_t MinExponent() const { return 1 - MaxExponent; }
  uint64_t fractionMask() const { return (uint64_t(1) << Fraction) - 1; }
  uint64_t infinityBits() const { return (2 * MaxExponent + 1) << Fraction; }
  APInt encode(uint64_t Magnitude, bool Negative) const {
    uint64_t Sign = uint64_t(Negative) << (Width - 1);
    return APInt(Width, Sign | Magnitude);
  }
  RealLiteralProjection tiny(bool Negative, bool Exact,
                             RoundingMode Mode) const {
    return {encode(directedAwayFromZero(Mode, Negative), Negative), true, false,
            false, !Exact};
  }
  RealLiteralProjection overflow(bool Negative, bool Exact, bool Inexact,
                                 RoundingMode Mode) const {
    const bool Infinite = Mode == RoundingMode::NearestTiesToEven ||
                          Mode == RoundingMode::NearestTiesToAway ||
                          directedAwayFromZero(Mode, Negative);
    return {encode(infinityBits() - !Infinite, Negative), Inexact || !Exact,
            true, !Exact, false};
  }
};

RealLiteralProjection projectFloat(const BinaryRational &Source,
                                   const BinaryFormat &Format, bool Exact,
                                   RoundingMode Mode) {
  const int64_t Exponent = Source.exponent();
  const int64_t Min = Format.MinExponent();
  // Below half the minimum subnormal, only a directed rounding away from
  // zero can produce a nonzero encoding. The precision-rounded exponent
  // still lies below the minimum normal exponent.
  if (Exponent < Min - Format.Fraction - 1)
    return Format.tiny(Source.Negative, Exact, Mode);

  auto Rounded = Source.project(Exponent - Format.Fraction, Mode);
  auto Coefficient = Rounded.Magnitude.getZExtValue();
  const bool Carry = Coefficient == (uint64_t(2) << Format.Fraction);
  const auto RoundedExponent = Exponent + Carry;
  if (RoundedExponent > Format.MaxExponent)
    return Format.overflow(Source.Negative, Exact, Rounded.Inexact, Mode);

  // The Exact range test uses the actual input rather than its projection.
  // Exact probes always truncate the coefficient for this comparison.
  const bool Outside = Exact && Exponent == Format.MaxExponent &&
                       Coefficient == 2 * Format.fractionMask() + 1 &&
                       Rounded.Inexact;
  if (Exponent < Min) {
    // The delivered subnormal is rounded once from the exact source, while
    // the unbounded-exponent result controls the tininess classification.
    auto Direct = Source.project(Min - Format.Fraction, Mode);
    const bool Underflow = !Exact && Direct.Inexact && RoundedExponent < Min;
    return {Format.encode(Direct.Magnitude.getZExtValue(), Source.Negative),
            Direct.Inexact, Outside, false, Underflow};
  }

  if (Carry)
    Coefficient >>= 1;
  auto ExponentBits = uint64_t(RoundedExponent + Format.MaxExponent);
  auto Magnitude =
      (ExponentBits << Format.Fraction) | (Coefficient & Format.fractionMask());
  return {Format.encode(Magnitude, Source.Negative), Rounded.Inexact, Outside};
}
} // namespace

RealLiteralProjection cpn::projectRealLiteral(StringRef Text, unsigned Width,
                                              bool Signed, bool IsFloat,
                                              bool Exact, RoundingMode Mode,
                                              const Token &At) {
  if (Text.size() > 65536)
    fail(At, "real literal exceeds compiler resource limit");
  if (Exact)
    Mode = RoundingMode::TowardZero;

  const bool Negative = Text.consume_front("-");
  Text.consume_front("+");
  const bool Hex = Text.consume_front_insensitive("0x");
  const auto ExponentMark = Text.find_first_of(Hex ? "pP" : "eE");
  const auto [Whole, Fraction] = Text.take_front(ExponentMark).split('.');
  const auto ExponentText = ExponentMark == StringRef::npos
                                ? StringRef()
                                : Text.drop_front(ExponentMark + 1);
  const int Unit = Hex ? 4 : 1;
  auto Scale = decimalExponent(ExponentText) - Unit * int64_t(Fraction.size());
  const auto Mantissa = Whole.str() + Fraction.str();
  auto Digits = StringRef(Mantissa).ltrim('0');
  const auto Trimmed = Digits.rtrim('0');
  Scale += Unit * int64_t(Digits.size() - Trimmed.size());
  Digits = Trimmed;

  const BinaryFormat Format(Width);
  if (Digits.empty())
    return {IsFloat ? Format.encode(0, Negative) : APInt(Width, 0)};
  if (!IsFloat && Scale >= Width)
    return {APInt(Width, 0), false, true};
  // In the decimal case these bounds avoid materializing a huge power of
  // five for values well outside either destination's transition range.
  if (!Hex && IsFloat && Scale >= 400)
    return Format.overflow(Negative, Exact, true, Mode);
  if (!Hex && Scale + int64_t(Digits.size()) <= -400) {
    if (IsFloat)
      return Format.tiny(Negative, Exact, Mode);
    return projectInteger(
        {APInt(1, directedAwayFromZero(Mode, Negative)), true}, Width, Signed,
        Negative, Exact);
  }

  const unsigned Radix = Hex ? 16 : 10;
  APInt Numerator(APInt::getSufficientBitsNeeded(Digits, Radix), Digits, Radix);
  APInt Denominator(1, 1);
  if (!Hex && Scale > 0) {
    const auto Power = powerOfFive(Scale);
    const auto ProductWidth = Numerator.getActiveBits() + Power.getActiveBits();
    Numerator =
        Numerator.zextOrTrunc(ProductWidth) * Power.zextOrTrunc(ProductWidth);
  } else if (!Hex && Scale < 0)
    Denominator = powerOfFive(-Scale);
  const BinaryRational Source{std::move(Numerator), std::move(Denominator),
                              Scale, Negative};
  if (IsFloat)
    return projectFloat(Source, Format, Exact, Mode);
  if (Source.exponent() < -1)
    return projectInteger(
        {APInt(1, directedAwayFromZero(Mode, Negative)), true}, Width, Signed,
        Negative, Exact);
  return projectInteger(Source.project(0, Mode), Width, Signed, Negative,
                        Exact);
}
