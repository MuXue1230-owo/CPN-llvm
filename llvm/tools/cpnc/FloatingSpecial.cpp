#include "Sema.h"
#include "llvm/ADT/StringSwitch.h"

using namespace cpn;
using llvm::StringRef;

namespace {
enum class Kind { Infinity, Quiet, Signaling, TryQuiet, TrySignaling };

std::optional<Kind> specialValue(StringRef Name) {
  Name.consume_front("::");
  Name.consume_front("std::numeric::");
  return llvm::StringSwitch<std::optional<Kind>>(Name)
      .Case("infinity", Kind::Infinity)
      .Case("quiet_nan", Kind::Quiet)
      .Case("signaling_nan", Kind::Signaling)
      .Case("try_quiet_nan", Kind::TryQuiet)
      .Case("try_signaling_nan", Kind::TrySignaling)
      .Default(std::nullopt);
}

std::optional<bool> negativeSign(const Node &Sign) {
  if (Sign.K != Node::Name || !Sign.TemplateArgs.empty())
    return std::nullopt;
  if (Sign.Text == "Positive")
    return false;
  if (Sign.Text == "Negative")
    return true;
  return std::nullopt;
}
} // namespace

bool cpn::floatingSpecialName(StringRef Name) {
  return specialValue(Name).has_value();
}

bool cpn::floatingSpecialSignArgument(const Node &Call, unsigned Child) {
  if (Call.K != Node::Call || !Child || Call.Children.front().K != Node::Name)
    return false;
  auto Spec = specialValue(Call.Children.front().Text);
  return Spec && Child == (*Spec == Kind::Infinity ? 1u : 2u) &&
         negativeSign(Call.Children[Child]).has_value();
}

std::optional<Value> Frame::floatingSpecial(const Node &Call, StringRef Name,
                                            const std::vector<Node> &Args) {
  if (Call.K != Node::Name)
    return std::nullopt;
  auto Spec = specialValue(Name);
  if (!Spec)
    return std::nullopt;
  const bool Infinity = *Spec == Kind::Infinity;
  const unsigned Required = Infinity ? 0 : 1;
  if (Call.TemplateArgs.size() != 1 || Args.size() < Required ||
      Args.size() > Required + 1)
    fail(Call.At, "floating special value requires one format and its "
                  "prescribed arguments");
  auto Type = resolve(Call.TemplateArgs.front().Type, Call.At);
  if (!floating(Type))
    fail(Call.At, "floating special value requires an enabled binary format");

  Value Payload;
  if (!Infinity) {
    Payload = load(eval(Args.front()));
    if (Payload.Type == "never")
      return Payload;
    if (!integer(Payload.Type))
      fail(Args.front().At, "NaN payload requires an exact integer");
  }
  bool Negative = false;
  if (Args.size() != Required) {
    auto Sign = negativeSign(Args.back());
    if (!Sign)
      fail(Args.back().At,
           "floating special-value sign must be Positive or Negative");
    Negative = *Sign;
  }

  const unsigned Width = Type == "f32" ? 32 : 64;
  const unsigned QuietIndex = Type == "f32" ? 22 : 51;
  auto *BitsType = B.getIntNTy(Width);
  const uint64_t Exponent =
      Type == "f32" ? 0x7f800000ULL : 0x7ff0000000000000ULL;
  uint64_t Encoding = Exponent;
  if (Negative)
    Encoding |= uint64_t(1) << (Width - 1);
  const bool Signaling =
      *Spec == Kind::Signaling || *Spec == Kind::TrySignaling;
  const uint64_t Quiet = uint64_t(1) << QuietIndex;
  if (!Infinity && !Signaling)
    Encoding |= Quiet;
  auto *EncodingBits = llvm::ConstantInt::get(BitsType, Encoding);
  if (Infinity)
    return Value{Type, B.CreateBitCast(EncodingBits, U.ir(Type))};

  unsigned InputWidth = Payload.IR->getType()->getIntegerBitWidth();
  auto *CheckType = B.getIntNTy(std::max(InputWidth, QuietIndex + 1));
  auto *Exact =
      B.CreateIntCast(Payload.IR, CheckType, signedType(Payload.Type));
  // An unsigned comparison also rejects sign-extended negative inputs.
  auto *Invalid =
      B.CreateICmpUGE(Exact, llvm::ConstantInt::get(CheckType, Quiet));
  if (Signaling)
    Invalid = B.CreateOr(Invalid, B.CreateIsNull(Exact));
  auto *Field = B.CreateIntCast(B.CreateAnd(Exact, Quiet - 1), BitsType, false);
  Value Number{Type,
               B.CreateBitCast(B.CreateOr(EncodingBits, Field), U.ir(Type))};
  if (*Spec == Kind::TryQuiet || *Spec == Kind::TrySignaling)
    return numericRepresentationResult(Call.At, Number, Invalid);
  if (!IR && !llvm::cast<llvm::ConstantInt>(Invalid)->isZero())
    fail(Call.At,
         "NaN payload is out of range in required constant evaluation");
  guard(Invalid, "numeric");
  return Number;
}
