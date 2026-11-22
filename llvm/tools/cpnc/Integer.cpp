#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Intrinsics.h"
using namespace cpn;
using namespace llvm;
bool cpn::integer(const std::string &T) {
  return T == "integer" ||
         ((StringRef(T).starts_with("i") || StringRef(T).starts_with("u")) &&
          builtin(T));
}
bool cpn::signedType(const std::string &T) {
  return T == "integer" || (!T.empty() && T[0] == 'i');
}
unsigned cpn::width(const std::string &T) {
  if (T == "bool")
    return 1;
  if (T == "char")
    return 32;
  if (T == "isize" || T == "usize")
    return 64;
  unsigned N = 0;
  StringRef(T).drop_front().getAsInteger(10, N);
  return N;
}
cpn::Value Frame::constant(APInt N, std::string T) {
  return {T, ConstantInt::get(U.C, N)};
}
cpn::Value Frame::literal(int64_t N, const std::string &T) {
  return constant(APInt(T == "integer" ? 65 : width(T), N, signedType(T)), T);
}
namespace {
APInt math(cpn::Value V) {
  auto N = cast<ConstantInt>(V.IR)->getValue();
  return signedType(V.Type) ? N.sext(N.getBitWidth() + 1)
                            : N.zext(N.getBitWidth() + 1);
}
bool fits(const APInt &N, const std::string &T) {
  return signedType(T) ? N.isSignedIntN(width(T))
                       : !N.isNegative() && N.isIntN(width(T));
}
} // namespace
bool cpn::implicitInteger(cpn::Value V, const std::string &T) {
  if (isa<ConstantInt>(V.IR))
    return fits(math(V), T);
  return StringRef(V.Type).ends_with("size") ==
             StringRef(T).ends_with("size") &&
         !(signedType(V.Type) && !signedType(T)) &&
         width(V.Type) + (signedType(T) && !signedType(V.Type)) <= width(T);
}
cpn::Value Frame::convert(cpn::Value V, const std::string &T, const Token &At) {
  if (V.Type == T)
    return V;
  if (floating(T))
    return floatingConvert(V, T, At);
  if (StringRef(V.Type).ends_with("*") && StringRef(T).ends_with("*")) {
    auto A = element(V.Type), D = element(T);
    auto unqualified = [](const std::string &S) {
      return StringRef(S).starts_with("const<") && StringRef(S).ends_with(">")
                 ? S.substr(6, S.size() - 7)
                 : S;
    };
    cpn::Value View{unqualified(A), nullptr, V.IR};
    if ((A == unqualified(A) || D != unqualified(D)) &&
        adjust(View, unqualified(D), At)) {
      auto *Null = ConstantPointerNull::get(B.getPtrTy());
      V.BaseView |= unqualified(A) != unqualified(D);
      V.IR = B.CreateSelect(B.CreateICmpEQ(V.IR, Null), Null, View.Address);
      V.Type = T;
      V.Address = nullptr;
      return V;
    }
    if (U.Signatures.count(A) && U.Signatures.count(D) &&
        U.Signatures.at(A) == U.Signatures.at(D) &&
        (!StringRef(D).ends_with(" noexcept>") ||
         StringRef(A).ends_with(" noexcept>"))) {
      V.Type = T;
      return V;
    }
  }
  if (V.Type == "nullptr_t" && StringRef(T).ends_with("*"))
    return {T, ConstantPointerNull::get(B.getPtrTy())};
  if (!integer(T) || !integer(V.Type) || T == "integer")
    fail(At, "cannot convert " + V.Type + " to " + T);
  if (isa<ConstantInt>(V.IR)) {
    auto N = math(V);
    if (!fits(N, T))
      fail(At, "integer constant is outside the range of " + T);
    return constant(N.sextOrTrunc(width(T)), T);
  }
  if (!implicitInteger(V, T))
    fail(At, "no implicit lossless conversion from " + V.Type + " to " + T);
  return {T, B.CreateIntCast(V.IR, U.ir(T), signedType(V.Type))};
}
void Frame::guard(llvm::Value *Bad) {
  if (auto *C = dyn_cast<ConstantInt>(Bad); C && C->isZero())
    return;
  if (!IR)
    fail({}, "operation requires runtime evaluation");
  auto *Trap = block("trap"), *OK = block("valid");
  B.CreateCondBr(Bad, Trap, OK);
  B.SetInsertPoint(Trap);
  B.CreateCall(Intrinsic::getOrInsertDeclaration(&U.M, Intrinsic::trap));
  B.CreateUnreachable();
  B.SetInsertPoint(OK);
}
cpn::Value Frame::binary(const Node &N, cpn::Value A, cpn::Value D) {
  if (floating(A.Type) || floating(D.Type) || A.Type == "real" ||
      D.Type == "real")
    return floatingBinary(N, A, D);
  auto Op = N.Text;
  const Token &At = N.At;
  bool Cmp = Op == "==" || Op == "!=" || Op == "<" || Op == "<=" || Op == ">" ||
             Op == ">=";
  if (!integer(A.Type) || !integer(D.Type)) {
    if (Cmp && (Op == "==" || Op == "!=") &&
        (A.Type == D.Type || A.Type == "nullptr_t" || D.Type == "nullptr_t") &&
        A.IR->getType() == D.IR->getType())
      return {"bool", Op == "==" ? B.CreateICmpEQ(A.IR, D.IR)
                                 : B.CreateICmpNE(A.IR, D.IR)};
    fail(At, "unsupported operand types for '" + Op + "'");
  }
  unsigned WA = A.IR->getType()->getIntegerBitWidth(),
           WB = D.IR->getType()->getIntegerBitWidth();
  if (Cmp) {
    if (A.Type != "integer" && D.Type != "integer" &&
        StringRef(A.Type).ends_with("size") !=
            StringRef(D.Type).ends_with("size"))
      fail(At, "comparison requires the same integer family");
    auto *Ty = B.getIntNTy(std::max(WA, WB) + 1);
    auto *L = B.CreateIntCast(A.IR, Ty, signedType(A.Type)),
         *R = B.CreateIntCast(D.IR, Ty, signedType(D.Type));
    auto Pred = Op == "=="   ? CmpInst::ICMP_EQ
                : Op == "!=" ? CmpInst::ICMP_NE
                : Op == "<"  ? CmpInst::ICMP_SLT
                : Op == ">"  ? CmpInst::ICMP_SGT
                : Op == "<=" ? CmpInst::ICMP_SLE
                             : CmpInst::ICMP_SGE;
    return {"bool", B.CreateICmp(Pred, L, R)};
  }
  bool Exact = A.Type == "integer" && D.Type == "integer";
  bool Shift = Op == "<<" || Op == ">>";
  std::string T = A.Type == "integer" ? D.Type : A.Type;
  if (Shift && A.Type == "integer" && !Exact)
    T = Opt.DefaultInt;
  if (!Exact && A.Type != "integer" && D.Type != "integer" &&
      A.Type != D.Type && !Shift) {
    if (StringRef(A.Type).ends_with("size") ||
        StringRef(D.Type).ends_with("size"))
      fail(At, "incompatible integer families");
    unsigned W = std::max(WA, WB);
    bool Signed = signedType(A.Type) || signedType(D.Type);
    if (Signed &&
        ((!signedType(A.Type) && WA == W) || (!signedType(D.Type) && WB == W)))
      W *= 2;
    if (W > 64)
      fail(At, "i128 is unavailable as a common integer type");
    T = (Signed ? "i" : "u") + std::to_string(W);
  }
  unsigned W = Exact ? std::max(WA, WB) + 2 : width(T);
  unsigned Distance = 0;
  if (Shift && isa<ConstantInt>(D.IR)) {
    auto Count = math(D);
    if (Count.isNegative() || Count.ugt(Exact ? 65535 : W - 1))
      fail(At, "invalid shift count");
    Distance = Count.getZExtValue();
  }
  if (Exact) {
    if (Op == "*")
      W = WA + WB;
    if (Op == "<<")
      W = WA + Distance + 1;
  }
  auto *Ty = B.getIntNTy(W);
  if (!Exact) {
    A = convert(A, T, At);
    if (!Shift)
      D = convert(D, T, At);
  }
  auto *L = B.CreateIntCast(A.IR, Ty, signedType(A.Type)),
       *R = B.CreateIntCast(D.IR, Ty, signedType(D.Type));
  bool Signed = Exact || signedType(T);
  if (Shift && !isa<ConstantInt>(D.IR)) {
    unsigned Bits = std::max(8u, WB);
    auto *Count = B.CreateIntCast(D.IR, B.getIntNTy(Bits), signedType(D.Type));
    guard(B.CreateICmpUGE(Count, ConstantInt::get(Count->getType(), W)));
  }
  llvm::Value *V = nullptr;
  if (Op == "&")
    V = B.CreateAnd(L, R);
  else if (Op == "|")
    V = B.CreateOr(L, R);
  else if (Op == "^")
    V = B.CreateXor(L, R);
  else if (Op == ">>")
    V = Signed ? B.CreateAShr(L, R) : B.CreateLShr(L, R);
  else if (Op == "/" || Op == "%") {
    if (auto *C = dyn_cast<ConstantInt>(R); C && C->isZero())
      fail(At, "division by zero");
    guard(B.CreateICmpEQ(R, ConstantInt::get(Ty, 0)));
    auto *Big = B.getIntNTy(W + 1);
    auto *X = B.CreateIntCast(L, Big, Signed),
         *Y = B.CreateIntCast(R, Big, Signed);
    auto *Q = Op == "/" ? B.CreateSDiv(X, Y) : B.CreateSRem(X, Y);
    if (Signed && !Exact && Op == "/") {
      auto *Max =
          ConstantInt::get(Big, APInt::getSignedMaxValue(W).sext(W + 1));
      auto *Overflow = B.CreateICmpSGT(Q, Max);
      if (Opt.Overflow == "saturating")
        Q = B.CreateSelect(Overflow, Max, Q);
      else if (Opt.Overflow != "wrapping")
        guard(Overflow);
    }
    V = B.CreateTrunc(Q, Ty);
  } else if (Op == "+" || Op == "-" || Op == "*" || Op == "<<") {
    if (Exact || Opt.Overflow == "wrapping" || Opt.Overflow == "native") {
      V = Op == "+"   ? B.CreateAdd(L, R)
          : Op == "-" ? B.CreateSub(L, R)
          : Op == "*" ? B.CreateMul(L, R)
                      : B.CreateShl(L, R);
    } else {
      auto *Big = B.getIntNTy(2 * W + 1);
      auto *X = B.CreateIntCast(L, Big, Signed),
           *Y = B.CreateIntCast(R, Big, Signed);
      auto *Z = Op == "+"   ? B.CreateAdd(X, Y)
                : Op == "-" ? B.CreateSub(X, Y)
                : Op == "*" ? B.CreateMul(X, Y)
                            : B.CreateShl(X, Y);
      auto Lo = Signed ? APInt::getSignedMinValue(W).sext(2 * W + 1)
                       : APInt(2 * W + 1, 0);
      auto Hi = Signed ? APInt::getSignedMaxValue(W).sext(2 * W + 1)
                       : APInt::getMaxValue(W).zext(2 * W + 1);
      auto *Min = ConstantInt::get(Big, Lo), *Max = ConstantInt::get(Big, Hi);
      auto *Low = B.CreateICmpSLT(Z, Min), *High = B.CreateICmpSGT(Z, Max);
      if (Opt.Overflow == "checked")
        guard(B.CreateOr(Low, High));
      else
        Z = B.CreateSelect(Low, Min, B.CreateSelect(High, Max, Z));
      V = B.CreateTrunc(Z, Ty);
    }
  } else
    fail(At, "unsupported integer operator");
  return {T, V};
}
