#ifndef CPNC_NUMERIC_LITERAL_H
#define CPNC_NUMERIC_LITERAL_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/FloatingPointMode.h"

namespace cpn {
struct Token;

struct RealLiteralProjection {
  llvm::APInt Bits;
  bool Inexact = false;
  bool OutOfRange = false;
  bool FPOverflow = false;
  bool FPUnderflow = false;
};

RealLiteralProjection projectRealLiteral(llvm::StringRef Text, unsigned Width,
                                         bool Signed, bool IsFloat, bool Exact,
                                         llvm::RoundingMode Mode,
                                         const Token &At);
} // namespace cpn

#endif
