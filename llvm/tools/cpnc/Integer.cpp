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
APInt cpn::integerLiteral(const Token &T) {
  std::string Digits;
  for (char C : T.Text)
    if (C != '_')
      Digits += C;
  StringRef S(Digits);
  unsigned Radix = 10;
  if (S.consume_front_insensitive("0x"))
    Radix = 16;
  else if (S.consume_front_insensitive("0b"))
    Radix = 2;
  else if (S.consume_front_insensitive("0o"))
    Radix = 8;
  if (S.size() > 65536)
    fail(T, "integer literal exceeds compiler resource limit");
  return APInt(std::max(2u, APInt::getSufficientBitsNeeded(S, Radix) + 1), S,
               Radix);
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
  if (auto Mutable = unconst(T); Mutable != T) {
    auto View = convert(V, Mutable, At);
    View.Readonly = true;
    return View;
  }
  if (V.Type == T)
    return V;
  if (StringRef(T).ends_with("]") &&
      (qualifyConst(T) == V.Type || qualifyConst(V.Type) == T)) {
    // Array value conversion constructs fresh elements. Keep the source
    // read-only for selecting their copy versus move operations.
    V.Readonly |= qualifyConst(T) == V.Type;
    V.Type = T;
    return V;
  }
  if (V.Type == "never") {
    if (T == "void")
      return {"void"};
    return {T, llvm::PoisonValue::get(U.ir(T, At)),
            U.aggregate(T) ? llvm::PoisonValue::get(B.getPtrTy()) : nullptr};
  }
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
    auto Target = unqualified(D);
    if ((A == unqualified(A) || D != Target) &&
        adjust(View, Target, At, false)) {
      bool Base = View.Type != Target;
      V.Type = T;
      V.Address = nullptr;
      if (!Base || llvm::isa<llvm::ConstantPointerNull>(V.IR))
        return V;
      V.BaseView = true;
      if (!IR)
        fail(At, "base adjustment requires runtime storage");
      // Virtual offsets reside in the object and are readable only on the
      // nonnull path, even when the converted pointer is never dereferenced.
      auto *Entry = B.GetInsertBlock(), *NonNull = block("pointer.base"),
           *End = block("pointer.end");
      B.CreateCondBr(B.CreateIsNotNull(V.IR), NonNull, End);
      B.SetInsertPoint(NonNull);
      adjust(View, Target, At);
      auto *Adjusted = B.GetInsertBlock();
      branch(End);
      B.SetInsertPoint(End);
      auto *P = B.CreatePHI(B.getPtrTy(), 2);
      P->addIncoming(llvm::ConstantPointerNull::get(B.getPtrTy()), Entry);
      P->addIncoming(View.Address, Adjusted);
      V.IR = P;
      return V;
    }
    if (U.compatibleCallable(A, D)) {
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
  if ((StringRef(A.Type).ends_with("*") || StringRef(D.Type).ends_with("*")) &&
      (Op == "+" || Op == "-" || (Cmp && Op != "==" && Op != "!=")))
    return pointerBinary(N, A, D);
  if (!integer(A.Type) || !integer(D.Type)) {
    if ((Op == "==" || Op == "!=") && A.Type != D.Type &&
        StringRef(A.Type).ends_with("*") && StringRef(D.Type).ends_with("*")) {
      if (conversionRank(A, D.Type, At))
        A = convert(A, D.Type, At);
      else if (conversionRank(D, A.Type, At))
        D = convert(D, A.Type, At);
    }
    if (Op == "==" || Op == "!=") {
      if (A.Type == "nullptr_t" && StringRef(D.Type).ends_with("*"))
        A = convert(A, D.Type, At);
      if (D.Type == "nullptr_t" && StringRef(A.Type).ends_with("*"))
        D = convert(D, A.Type, At);
    }
    if (Cmp && (Op == "==" || Op == "!=") && A.Type == D.Type &&
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
    if (Op == "&" || Op == "|" || Op == "^")
      fail(At,
           "bitwise operands require identical integer width and signedness");
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
    if (!Opt.IntegerWidths.count(W))
      fail(At, "CFG002: " + T + " is unavailable as a common integer type");
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

cpn::Value Frame::pointerBinary(const Node &N, cpn::Value P, cpn::Value Other) {
  if (N.Text == "+" && integer(P.Type))
    std::swap(P, Other);
  if (!StringRef(P.Type).ends_with("*"))
    fail(N.At, "object pointer required");
  auto T = element(P.Type);
  if (StringRef(T).starts_with("const<") && T.back() == '>')
    T = T.substr(6, T.size() - 7);
  if (T == "void" || U.Signatures.count(T) || !U.ir(T)->isSized())
    fail(N.At, "pointer arithmetic requires a complete object element");
  if (!IR)
    return constantPointerOffset(N, P, Other, T);
  auto *Long = B.getIntNTy(128);
  auto address = [&](llvm::Value *V) {
    return B.CreateZExt(B.CreatePtrToInt(V, B.getInt64Ty()), Long);
  };
  auto base = address(P.IR);
  auto stride = ConstantInt::get(
      Long, U.M.getDataLayout().getTypeAllocSize(U.ir(T)).getFixedValue());
  guard(B.CreateIsNull(P.IR));
  if (StringRef(Other.Type).ends_with("*")) {
    if (element(P.Type) != element(Other.Type) || N.Text == "+")
      fail(N.At,
           "pointer difference or order requires compatible element types");
    guard(B.CreateIsNull(Other.IR));
    if (P.Lower && Other.Lower)
      guard(B.CreateAnd(B.CreateAnd(B.CreateIsNotNull(P.Lower),
                                    B.CreateIsNotNull(Other.Lower)),
                        B.CreateICmpNE(P.Lower, Other.Lower)));
    if (P.ArraySlot && Other.ArraySlot && P.ArrayGeneration &&
        Other.ArrayGeneration)
      guard(B.CreateAnd(B.CreateAnd(B.CreateIsNotNull(P.ArraySlot),
                                    B.CreateIsNotNull(Other.ArraySlot)),
                        B.CreateOr(B.CreateICmpNE(P.ArraySlot, Other.ArraySlot),
                                   B.CreateICmpNE(P.ArrayGeneration,
                                                  Other.ArrayGeneration))));
    auto right = address(Other.IR);
    if (N.Text != "-") {
      auto Pred = N.Text == "<"    ? CmpInst::ICMP_ULT
                  : N.Text == "<=" ? CmpInst::ICMP_ULE
                  : N.Text == ">"  ? CmpInst::ICMP_UGT
                                   : CmpInst::ICMP_UGE;
      return {"bool", B.CreateICmp(Pred, base, right)};
    }
    auto Diff = B.CreateSub(base, right);
    guard(B.CreateIsNotNull(B.CreateSRem(Diff, stride)));
    auto Count = B.CreateSDiv(Diff, stride);
    auto Result = B.CreateTrunc(Count, B.getInt64Ty());
    guard(B.CreateICmpNE(B.CreateSExt(Result, Long), Count));
    return {"isize", Result};
  }
  if (!integer(Other.Type) || (N.Text != "+" && N.Text != "-"))
    fail(N.At, "pointer offset must be an integer");
  if (Other.Type == "integer")
    Other = convert(Other, "isize", N.At);
  auto Offset = B.CreateMul(
      B.CreateIntCast(Other.IR, Long, signedType(Other.Type)), stride);
  auto Target =
      N.Text == "+" ? B.CreateAdd(base, Offset) : B.CreateSub(base, Offset);
  auto Raw = B.CreateTrunc(Target, B.getInt64Ty());
  guard(B.CreateICmpNE(B.CreateZExt(Raw, Long), Target));
  if (P.Lower && P.Upper)
    guard(B.CreateAnd(B.CreateIsNotNull(P.Lower),
                      B.CreateOr(B.CreateICmpULT(Target, address(P.Lower)),
                                 B.CreateICmpUGT(Target, address(P.Upper)))));
  auto *Result = B.CreateIntToPtr(Raw, B.getPtrTy());
  offsetRegistration(P, Result, T, N.At);
  P.IR = Result;
  P.Address = nullptr;
  P.BoundsCell = nullptr;
  P.Prvalue = P.Expiring = true;
  return P;
}
