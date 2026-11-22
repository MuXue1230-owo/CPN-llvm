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
// SSE scalar arithmetic observes MXCSR. Change only its rounding bits and
// preserve events raised by the operation when restoring the caller's mode.
class OperationRounding {
  Frame &F;
  llvm::AllocaInst *Cell = nullptr;
  llvm::Value *Saved = nullptr;
  static constexpr unsigned Mask = 3u << 13;
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
  explicit OperationRounding(Frame &F) : F(F) {
    auto Name = F.Opt.FPRounding;
    if (Name.empty())
      Name = F.Opt.FPProfile == "strict" ? "current" : "nearest_ties_even";
    Mode = Name == "current" ? llvm::RoundingMode::NearestTiesToEven
                             : rounding(Name);
    F.B.setIsFPConstrained(F.IR != nullptr);
    F.B.setDefaultConstrainedExcept(llvm::fp::ebStrict);
    F.B.setDefaultConstrainedRounding(llvm::RoundingMode::Dynamic);
    if (!F.IR || Name == "current")
      return;
    unsigned RC = Mode == llvm::RoundingMode::TowardNegative   ? 1
                  : Mode == llvm::RoundingMode::TowardPositive ? 2
                  : Mode == llvm::RoundingMode::TowardZero     ? 3
                                                               : 0;
    llvm::IRBuilder<> Entry(F.IR->getEntryBlock().begin());
    Cell = Entry.CreateAlloca(F.B.getInt32Ty(), nullptr, "fp.control");
    auto *Old = read();
    Saved = F.B.CreateAnd(Old, F.B.getInt32(Mask));
    write(F.B.CreateOr(F.B.CreateAnd(Old, F.B.getInt32(~Mask)),
                       F.B.getInt32(RC << 13)));
  }
  ~OperationRounding() {
    if (Saved)
      write(F.B.CreateOr(F.B.CreateAnd(read(), F.B.getInt32(~Mask)), Saved));
  }
};
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
  if (!floating(V.Type)) {
    if (!Explicit || !integer(V.Type))
      fail(At, "cannot implicitly convert " + V.Type + " to " + T);
    OperationRounding Policy(*this);
    if (!IR) {
      llvm::APFloat Result(Sem);
      Result.convertFromAPInt(llvm::cast<llvm::ConstantInt>(V.IR)->getValue(),
                              signedType(V.Type), Policy.Mode);
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
  OperationRounding Policy(*this);
  if (!IR) {
    auto Result = llvm::cast<llvm::ConstantFP>(V.IR)->getValueAPF();
    bool Loss;
    Result.convert(Sem, Policy.Mode, &Loss);
    return {T, llvm::ConstantFP::get(U.C, Result)};
  }
  return {T, T == "f64" ? B.CreateFPExt(V.IR, U.ir(T))
                        : B.CreateFPTrunc(V.IR, U.ir(T))};
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
  OperationRounding Policy(*this);
  if (!IR && (Op == "+" || Op == "-" || Op == "*" || Op == "/")) {
    auto Result = llvm::cast<llvm::ConstantFP>(X)->getValueAPF();
    auto &Right = llvm::cast<llvm::ConstantFP>(Y)->getValueAPF();
    if (Op == "+")
      Result.add(Right, Policy.Mode);
    else if (Op == "-")
      Result.subtract(Right, Policy.Mode);
    else if (Op == "*")
      Result.multiply(Right, Policy.Mode);
    else
      Result.divide(Right, Policy.Mode);
    return {T, llvm::ConstantFP::get(U.C, Result)};
  }
  if (Op == "+")
    return {T, B.CreateFAdd(X, Y)};
  if (Op == "-")
    return {T, B.CreateFSub(X, Y)};
  if (Op == "*")
    return {T, B.CreateFMul(X, Y)};
  if (Op == "/")
    return {T, B.CreateFDiv(X, Y)};
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
  return {"bool", B.CreateFCmp(P, X, Y)};
}
