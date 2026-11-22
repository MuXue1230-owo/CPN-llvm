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
  llvm::Value *read() {
    F.B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
                       &F.U.M, llvm::Intrinsic::x86_sse_stmxcsr),
                   {Cell});
    return F.B.CreateLoad(F.B.getInt32Ty(), Cell);
  }
  void write(llvm::Value *V) {
    F.B.CreateStore(V, Cell);
    F.B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
                       &F.U.M, llvm::Intrinsic::x86_sse_ldmxcsr),
                   {Cell});
  }

public:
  llvm::RoundingMode Mode;
  explicit FloatingOperation(Frame &F) : F(F) {
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
                    ((F.Opt.FPSubnormal == "current" ||
                      (Strict && F.Opt.FPSubnormal.empty())) &&
                     F.Opt.InitialSubnormal == "preserve");
    if (!Strict && !F.Opt.FPTrapMask && Name == "current" && !Preserve)
      return;
    llvm::IRBuilder<> Entry(F.IR->getEntryBlock().begin());
    Cell = Entry.CreateAlloca(F.B.getInt32Ty(), nullptr, "fp.control");
    Saved = read();
    auto *Controls = Saved;
    if (Strict || F.Opt.FPTrapMask) {
      if (F.Opt.FPTrapMask || F.Opt.FPInitialTraps)
        Traps = F.B.getInt32(
            F.Opt.FPTrapMask.value_or(F.Opt.FPInitialTraps.value_or(0)));
      else
        Traps = F.B.CreateAnd(F.B.CreateNot(F.B.CreateLShr(Saved, 7)), Events);
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
    write(Controls);
  }
  ~FloatingOperation() {
    if (!Saved)
      return;
    auto *Local = F.B.CreateAnd(read(), Flags);
    write(F.B.CreateOr(Saved, Local));
    if (Traps)
      F.guard(F.B.CreateIsNotNull(F.B.CreateAnd(Local, Traps)), "numeric");
  }
  void check(llvm::APFloat::opStatus Status, const Token &At) const {
    unsigned IEEE = unsigned(Status);
    // APFloat has contiguous event bits. MXCSR reserves bit 1 for denormal
    // inputs.
    unsigned Raised = (IEEE & 1) | ((IEEE & ~1u) << 1);
    if (Raised & F.Opt.FPTrapMask.value_or(F.Opt.FPInitialTraps.value_or(0)))
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
} // namespace
Value Frame::floatingConvert(Value V, const std::string &T, const Token &At,
                             bool Explicit) {
  if (!Opt.FloatFormats.count(T))
    fail(At, "floating format is disabled");
  if (V.Type == T)
    return V;
  auto &Sem =
      T == "f32" ? llvm::APFloat::IEEEsingle() : llvm::APFloat::IEEEdouble();
  if (V.Type == "real" || V.Type == "integer") {
    llvm::APFloat Number(Sem);
    llvm::APFloat::opStatus Status;
    if (V.Type == "integer")
      Status = Number.convertFromAPInt(
          llvm::cast<llvm::ConstantInt>(V.IR)->getValue(), true,
          rounding(Opt.LiteralRounding));
    else {
      auto Outcome =
          Number.convertFromString(V.RealText, rounding(Opt.LiteralRounding));
      if (!Outcome) {
        std::string Detail;
        llvm::raw_string_ostream Message(Detail);
        llvm::logAllUnhandledErrors(Outcome.takeError(), Message);
        fail(At, "malformed real literal: " + Detail);
      }
      Status = *Outcome;
    }
    if (Status & llvm::APFloat::opOverflow)
      fail(At, "floating literal overflows " + T);
    return {T, llvm::ConstantFP::get(U.C, Number)};
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
                            const std::string &Expected) {
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
    FloatingOperation Policy(*this);
    llvm::Value *Out;
    if (!IR) {
      auto Result = llvm::cast<llvm::ConstantFP>(X)->getValueAPF();
      auto &Right = llvm::cast<llvm::ConstantFP>(Y)->getValueAPF();
      auto Status = Op == "+"   ? Result.add(Right, Policy.Mode)
                    : Op == "-" ? Result.subtract(Right, Policy.Mode)
                    : Op == "*" ? Result.multiply(Right, Policy.Mode)
                                : Result.divide(Right, Policy.Mode);
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
    return {T, Opt.FPProfile == "strict" ? strictBinary(B, Out, X, Y) : Out};
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
