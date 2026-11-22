#include "Frontend.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cstdint>

using namespace cpn;
using llvm::StringRef;
namespace {
struct Entry {
  uint64_t Key;
  uint32_t A, B = 0;
};
#include "UnicodeData.inc"

template <size_t N> bool contains(const uint32_t (&Edges)[N], uint32_t C) {
  return (std::upper_bound(Edges, Edges + N, C) - Edges) % 2;
}
template <size_t N> const Entry *find(const Entry (&Table)[N], uint64_t Key) {
  auto *It =
      std::lower_bound(Table, Table + N, Key,
                       [](const Entry &E, uint64_t K) { return E.Key < K; });
  return It != Table + N && It->Key == Key ? It : nullptr;
}
unsigned rank(uint32_t C) {
  auto *E = find(Ranks, C);
  return E ? E->A : 0;
}
void decompose(uint32_t C, std::vector<uint32_t> &Out) {
  if (C >= 0xac00 && C < 0xac00 + 11172) {
    unsigned S = C - 0xac00;
    Out.insert(Out.end(), {0x1100 + S / 588, 0x1161 + S % 588 / 28});
    if (S % 28)
      Out.push_back(0x11a7 + S % 28);
  } else if (auto *E = find(Decomp, C)) {
    decompose(E->A, Out);
    if (E->B)
      decompose(E->B, Out);
  } else
    Out.push_back(C);
}
uint32_t compose(uint32_t A, uint32_t B) {
  if (A >= 0x1100 && A < 0x1113 && B >= 0x1161 && B < 0x1176)
    return 0xac00 + (A - 0x1100) * 588 + (B - 0x1161) * 28;
  if (A >= 0xac00 && A < 0xac00 + 11172 && (A - 0xac00) % 28 == 0 &&
      B > 0x11a7 && B < 0x11c3)
    return A + B - 0x11a7;
  auto *E = find(Compositions, (uint64_t(A) << 21) | B);
  return E ? E->A : 0;
}
uint32_t decode(StringRef S, size_t &I, const Token &At) {
  unsigned C = uint8_t(S[I++]);
  if (C < 128)
    return C;
  unsigned N = C >= 0xf0 ? 3 : C >= 0xe0 ? 2 : 1;
  if (C < 0xc2 || C > 0xf4 || I + N > S.size())
    fail(At, "invalid UTF-8");
  C &= 0x7f >> (N + 1);
  for (unsigned J = 0; J < N; ++J) {
    unsigned B = uint8_t(S[I++]);
    if ((B & 0xc0) != 0x80)
      fail(At, "invalid UTF-8");
    C = (C << 6) | (B & 63);
  }
  if ((N == 2 && C < 0x800) || (N == 3 && C < 0x10000) || C > 0x10ffff ||
      (C >= 0xd800 && C <= 0xdfff))
    fail(At, "invalid UTF-8");
  return C;
}
void encode(uint32_t C, std::string &Out) {
  if (C < 128) {
    Out += char(C);
    return;
  }
  unsigned N = C < 0x800 ? 1 : C < 0x10000 ? 2 : 3;
  Out += char((0xff << (7 - N)) | (C >> (N * 6)));
  while (N--)
    Out += char(0x80 | ((C >> (6 * N)) & 63));
}
std::string normalize(StringRef S, Token At) {
  if (llvm::all_of(S, [](unsigned char C) { return C < 128; }))
    return S.str();
  std::vector<uint32_t> V, Result;
  for (size_t I = 0; I < S.size();)
    decompose(decode(S, I, At), V);
  size_t Marks = 0;
  for (size_t I = 0; I <= V.size(); ++I)
    if (I == V.size() || !rank(V[I])) {
      std::stable_sort(
          V.begin() + Marks, V.begin() + I,
          [](uint32_t A, uint32_t B) { return rank(A) < rank(B); });
      Marks = I + 1;
    }
  size_t Starter = 0;
  unsigned Last = 0;
  for (uint32_t C : V) {
    unsigned R = rank(C);
    if (!Result.empty() && (!Last || Last < R))
      if (auto Combined = compose(Result[Starter], C)) {
        Result[Starter] = Combined;
        continue;
      }
    if (!R)
      Starter = Result.size();
    Result.push_back(C);
    Last = R;
  }
  std::string Out;
  for (auto C : Result)
    encode(C, Out);
  return Out;
}
bool xid(uint32_t C, bool First) {
  return C == '_' || (!contains(Ignorable, C) &&
                      (First ? contains(Start, C) : contains(Continue, C)));
}
} // namespace

void Options::diagnose(const Token &T, Severity Level, StringRef Code,
                       StringRef Message) const {
  std::string Category = Level == Severity::Warning ? "WARNING" : "ANOMALY";
  auto Text = Code.empty() ? Message.str() : (Code + ": " + Message).str();
  if (Promote.count(Category) || Promote.count(Code.str()))
    fail(T, Text);
  if (Level >= Minimum && !Suppress.count(Code.str()))
    llvm::errs() << Input << ":" << T.Line << ":" << T.Column << ": "
                 << Category << ": " << Text << "\n";
}
void Options::warn(const Token &T, StringRef Message) const {
  diagnose(T, Severity::Warning, "", Message);
}
bool cpn::identifier(StringRef S) {
  if (S.empty())
    return false;
  size_t I = 0;
  return xid(decode(S, I, {}), true);
}
bool cpn::floating(StringRef S) { return S == "f32" || S == "f64"; }
bool cpn::realToken(StringRef S) {
  return S.contains('.') ||
         (S.starts_with_insensitive("0x") ? S.contains_insensitive("p")
                                          : S.contains_insensitive("e"));
}
bool cpn::builtin(StringRef S) {
  return floating(S) || S == "void" || S == "bool" || S == "char" ||
         S == "byte" || S == "nullptr_t" || S == "isize" || S == "usize" ||
         S == "i8" || S == "i16" || S == "i32" || S == "i64" || S == "u8" ||
         S == "u16" || S == "u32" || S == "u64";
}
std::vector<Token> cpn::lex(StringRef S, const Options &Opt) {
  S.consume_front("\xef\xbb\xbf");
  std::vector<Token> Out;
  size_t I = 0;
  unsigned Line = 1, Col = 1;
  auto advance = [&]() {
    uint32_t C = decode(S, I, {"", Line, Col});
    if (C == '\r') {
      if (I < S.size() && S[I] == '\n')
        ++I;
      C = '\n';
    }
    if (C == '\n') {
      ++Line;
      Col = 1;
    } else
      ++Col;
    return C;
  };
  while (I < S.size()) {
    Token T{"", Line, Col};
    size_t Begin = I;
    StringRef Rest = S.drop_front(I);
    if (Rest.starts_with("//")) {
      while (I < S.size() && S[I] != '\r' && S[I] != '\n')
        advance();
      continue;
    }
    if (Rest.starts_with("/*")) {
      advance();
      advance();
      unsigned Depth = 1;
      while (Depth && I < S.size()) {
        StringRef R = S.drop_front(I);
        if (R.starts_with("/*")) {
          advance();
          advance();
          ++Depth;
        } else if (R.starts_with("*/")) {
          advance();
          advance();
          --Depth;
        } else
          advance();
      }
      if (Depth)
        fail(T, "unterminated block comment");
      continue;
    }
    uint32_t C = advance();
    if (C < 128 && llvm::isSpace(char(C)))
      continue;
    if (C >= '0' && C <= '9') {
      size_t End = Begin;
      unsigned Base = 10;
      if (Rest.starts_with_insensitive("0x")) {
        Base = 16;
        End += 2;
      } else if (Rest.starts_with_insensitive("0b")) {
        Base = 2;
        End += 2;
      } else if (Rest.starts_with_insensitive("0o")) {
        Base = 8;
        End += 2;
      }
      auto sequence = [&](unsigned Radix) {
        bool Digit = false;
        while (End < S.size()) {
          char D = S[End];
          if (llvm::hexDigitValue(D) < Radix) {
            Digit = true;
            ++End;
          } else if (D == '_' && Digit) {
            Digit = false;
            ++End;
          } else
            break;
        }
        if (!Digit)
          fail(T, "malformed numeric literal");
      };
      sequence(Base);
      bool Point = false;
      if ((Base == 10 || Base == 16) && End + 1 < S.size() && S[End] == '.' &&
          llvm::hexDigitValue(S[End + 1]) < Base) {
        Point = true;
        ++End;
        sequence(Base);
      }
      if (End < S.size() &&
          ((Base == 10 && (S[End] == 'e' || S[End] == 'E')) ||
           (Base == 16 && (S[End] == 'p' || S[End] == 'P')))) {
        ++End;
        if (End < S.size() && (S[End] == '+' || S[End] == '-'))
          ++End;
        sequence(10);
      } else if (Base == 16 && Point)
        fail(T, "hexadecimal real literal requires a binary exponent");
      if (End < S.size()) {
        size_t J = End;
        if (xid(decode(S, J, T), false))
          fail(T, "malformed numeric literal");
      }
      while (I < End)
        advance();
      T.Text = S.slice(Begin, End).str();
    } else if (xid(C, true)) {
      while (I < S.size()) {
        size_t J = I;
        if (!xid(decode(S, J, T), false))
          break;
        advance();
      }
      auto Word = S.slice(Begin, I);
      if (Opt.ASCII &&
          !llvm::all_of(Word, [](unsigned char D) { return D < 128; }))
        fail(T, "non-ASCII identifier in ASCII source profile");
      T.Text = normalize(Word, T);
      if (T.Text != Word)
        Opt.warn(T, "identifier spelling is not NFC");
    } else if (C == '"' || C == '\'') {
      bool Closed = false;
      while (I < S.size()) {
        auto D = advance();
        if (D == '\n')
          break;
        if (D == C) {
          Closed = true;
          break;
        }
        if (D == '\\' && I < S.size() && advance() == '\n')
          break;
      }
      if (!Closed)
        fail(T, "unterminated quoted literal");
      T.Text = S.slice(Begin, I).str();
      unquote(T);
    } else {
      for (StringRef Op : {"<<=", ">>=", "...", "::", "->", "++", "--", "&&",
                           "||",  "<<",  ">>",  "==", "!=", "<=", ">=", "+=",
                           "-=",  "*=",  "/=",  "%=", "&=", "^=", "|="})
        if (Rest.starts_with(Op)) {
          while (I < Begin + Op.size())
            advance();
          break;
        }
      T.Text = S.slice(Begin, I).str();
    }
    Out.push_back(std::move(T));
  }
  Out.push_back({"", Line, Col});
  return Out;
}
std::string cpn::unquote(const Token &T) {
  StringRef S(T.Text);
  S = S.drop_front().drop_back();
  std::string R;
  for (size_t I = 0; I < S.size();) {
    uint32_t C = decode(S, I, T);
    if (C == '\\') {
      if (I == S.size())
        fail(T, "invalid escape sequence");
      char E = S[I++];
      switch (E) {
      case 'n':
        C = 10;
        break;
      case 't':
        C = 9;
        break;
      case 'r':
        C = 13;
        break;
      case '0':
        C = 0;
        break;
      case '\'':
      case '"':
      case '\\':
        C = E;
        break;
      case 'u': {
        if (I == S.size() || S[I++] != '{')
          fail(T, "invalid escape sequence");
        size_t Begin = I;
        while (I < S.size() && S[I] != '}')
          ++I;
        if (I == S.size() || I - Begin > 6 ||
            S.slice(Begin, I).getAsInteger(16, C) || C > 0x10ffff ||
            (C >= 0xd800 && C <= 0xdfff))
          fail(T, "escape does not denote a Unicode scalar");
        ++I;
        break;
      }
      default:
        fail(T, "invalid escape sequence");
      }
    }
    encode(C, R);
  }
  if (T.Text.front() == '\'') {
    size_t I = 0;
    if (R.empty() || (decode(R, I, T), I != R.size()))
      fail(T, "character literal requires one Unicode scalar");
  }
  return R;
}
