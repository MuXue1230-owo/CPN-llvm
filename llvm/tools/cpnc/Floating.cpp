#include "Sema.h"
#include "llvm/ADT/APFloat.h"
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
void constrain(Frame &F) {
  F.B.setIsFPConstrained(F.IR && F.Opt.FPProfile == "strict");
  F.B.setDefaultConstrainedExcept(llvm::fp::ebStrict);
  F.B.setDefaultConstrainedRounding(llvm::RoundingMode::Dynamic);
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
  if (!floating(V.Type)) {
    if (!Explicit || !integer(V.Type))
      fail(At, "cannot implicitly convert " + V.Type + " to " + T);
    constrain(*this);
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
  constrain(*this);
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
  constrain(*this);
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
