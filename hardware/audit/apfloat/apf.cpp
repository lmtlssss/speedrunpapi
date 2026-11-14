// Every operand of a small llvm::APFloat format through one operation, results as text lines.
//
// usage: apf info SEM                  size, precision, exponent range
//        apf table SEM                 one line per bit pattern: pattern category sign value
//        apf bin SEM OP RM             OP add sub mul div rem mod; all pairs:   a b | result
//        apf fma SEM RM                all triples (a * b + c):                 a b c | result
//        apf rint SEM RM               roundToIntegral of every value:          a | result
//        apf next SEM DOWN             next(DOWN) of every value:               a | result
//        apf conv SEM TO RM            convert every value of SEM to TO:        a | result losesInfo
//        apf toint SEM WIDTH SIGNED RM convertToInteger of every value:         a | integer status isExact
//        apf fromint SEM WIDTH SIGNED RM   convertFromAPInt of every WIDTH-bit integer: n | result
//        apf cmp SEM                   compare of all pairs: a b | 0 less, 1 equal, 2 greater, 3 unordered
// SEM  E5M2 E5M2FNUZ E4M3 E4M3FN E4M3FNUZ E4M3B11FNUZ E3M4 E8M0FNU E3M2FN E2M3FN E2M1FN (E5M3FNU where the
//      library has it), half bfloat single double
// RM   ne (nearest, ties to even) tp (toward +inf) tn (toward -inf) tz (toward zero) na (nearest, ties away)
// A result is three fields: the category APFloat reports (i infinity, n NaN, f finite non-zero, z zero),
// the bit pattern in hex, and the opStatus bits (1 invalid, 2 divide by zero, 4 overflow, 8 underflow,
// 16 inexact). A case that ends in a signal (an assertion, a trap) prints "! SIGNAL" in place of the result.
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/APSInt.h"
#include <csetjmp>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>

using namespace llvm;

static const fltSemantics &sem(const char *n) {
  if (!strcmp(n, "E5M2")) return APFloat::Float8E5M2();
  if (!strcmp(n, "E5M2FNUZ")) return APFloat::Float8E5M2FNUZ();
  if (!strcmp(n, "E4M3")) return APFloat::Float8E4M3();
  if (!strcmp(n, "E4M3FN")) return APFloat::Float8E4M3FN();
  if (!strcmp(n, "E4M3FNUZ")) return APFloat::Float8E4M3FNUZ();
  if (!strcmp(n, "E4M3B11FNUZ")) return APFloat::Float8E4M3B11FNUZ();
  if (!strcmp(n, "E3M4")) return APFloat::Float8E3M4();
  if (!strcmp(n, "E8M0FNU")) return APFloat::Float8E8M0FNU();
#ifdef HAVE_E5M3FNU
  if (!strcmp(n, "E5M3FNU")) return APFloat::Float8E5M3FNU();
#endif
  if (!strcmp(n, "E3M2FN")) return APFloat::Float6E3M2FN();
  if (!strcmp(n, "E2M3FN")) return APFloat::Float6E2M3FN();
  if (!strcmp(n, "E2M1FN")) return APFloat::Float4E2M1FN();
  if (!strcmp(n, "half")) return APFloat::IEEEhalf();
  if (!strcmp(n, "bfloat")) return APFloat::BFloat();
  if (!strcmp(n, "single")) return APFloat::IEEEsingle();
  if (!strcmp(n, "double")) return APFloat::IEEEdouble();
  fprintf(stderr, "unknown format %s\n", n);
  exit(2);
}

static RoundingMode rm(const char *n) {
  if (!strcmp(n, "ne")) return RoundingMode::NearestTiesToEven;
  if (!strcmp(n, "tp")) return RoundingMode::TowardPositive;
  if (!strcmp(n, "tn")) return RoundingMode::TowardNegative;
  if (!strcmp(n, "tz")) return RoundingMode::TowardZero;
  if (!strcmp(n, "na")) return RoundingMode::NearestTiesToAway;
  fprintf(stderr, "unknown rounding mode %s\n", n);
  exit(2);
}

static sigjmp_buf jump;
static void on_signal(int sig) { siglongjmp(jump, sig); }

static void catch_signals() {
  static const int sigs[] = {SIGABRT, SIGILL, SIGTRAP, SIGSEGV, SIGBUS, SIGFPE};
  for (int s : sigs) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sa.sa_flags = SA_NODEFER;
    sigaction(s, &sa, nullptr);
  }
}

static char cat(const APFloat &x) {
  switch (x.getCategory()) {
  case APFloat::fcInfinity: return 'i';
  case APFloat::fcNaN: return 'n';
  case APFloat::fcNormal: return 'f';
  case APFloat::fcZero: return 'z';
  }
  return '?';
}

// The category is read before the bit pattern, so that a value the format cannot encode is still named.
static void result(const APFloat &x, int st) {
  char c = cat(x);
  printf("%c ", c);
  fflush(stdout);
  printf("%llx %d", (unsigned long long) x.bitcastToAPInt().getZExtValue(), st);
}

#define GUARDED(...)                                                                               \
  do {                                                                                             \
    int sig_ = sigsetjmp(jump, 1);                                                                 \
    if (sig_ == 0) { __VA_ARGS__; } else { printf("! %d", sig_); }                                        \
    printf("\n");                                                                                  \
  } while (0)

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: apf MODE SEM ...\n"); return 2; }
  const char *mode = argv[1];
  const fltSemantics &S = sem(argv[2]);
  const unsigned W = APFloat::semanticsSizeInBits(S);
  const unsigned long long N = 1ULL << W;
  if (!strcmp(mode, "info")) {
    printf("bits %u precision %u minexp %d maxexp %d\n", W, APFloat::semanticsPrecision(S),
           (int) APFloat::semanticsMinExponent(S), (int) APFloat::semanticsMaxExponent(S));
    return 0;
  }
  if (!strcmp(mode, "table")) {
    for (unsigned long long a = 0; a < N; a++) {
      APFloat x(S, APInt(W, a));
      const char *c = x.isZero() ? "zero" : x.isInfinity() ? "inf" : x.isNaN() ? "nan" : "fin";
      bool loses = false;
      APFloat d = x;
      d.convert(APFloat::IEEEdouble(), RoundingMode::NearestTiesToEven, &loses);
      if (x.isNaN()) printf("%llx nan %d nan\n", a, (int) x.isNegative());
      else if (x.isInfinity()) printf("%llx inf %d inf\n", a, (int) x.isNegative());
      else printf("%llx %s %d %a\n", a, c, (int) x.isNegative(), d.convertToDouble());
    }
    return 0;
  }
  catch_signals();
  if (!strcmp(mode, "bin")) {
    const char *op = argv[3];
    RoundingMode R = rm(argv[4]);
    for (unsigned long long a = 0; a < N; a++)
      for (unsigned long long b = 0; b < N; b++) {
        printf("%llx %llx | ", a, b);
        GUARDED({
          APFloat x(S, APInt(W, a)), y(S, APInt(W, b));
          APFloat::opStatus st;
          if (!strcmp(op, "add")) st = x.add(y, R);
          else if (!strcmp(op, "sub")) st = x.subtract(y, R);
          else if (!strcmp(op, "mul")) st = x.multiply(y, R);
          else if (!strcmp(op, "div")) st = x.divide(y, R);
          else if (!strcmp(op, "rem")) st = x.remainder(y);
          else st = x.mod(y);
          result(x, (int) st);
        });
      }
    return 0;
  }
  if (!strcmp(mode, "fma")) {
    RoundingMode R = rm(argv[3]);
    for (unsigned long long a = 0; a < N; a++)
      for (unsigned long long b = 0; b < N; b++)
        for (unsigned long long c = 0; c < N; c++) {
          printf("%llx %llx %llx | ", a, b, c);
          GUARDED({
            APFloat x(S, APInt(W, a)), y(S, APInt(W, b)), z(S, APInt(W, c));
            APFloat::opStatus st = x.fusedMultiplyAdd(y, z, R);
            result(x, (int) st);
          });
        }
    return 0;
  }
  if (!strcmp(mode, "rint")) {
    RoundingMode R = rm(argv[3]);
    for (unsigned long long a = 0; a < N; a++) {
      printf("%llx | ", a);
      GUARDED({
        APFloat x(S, APInt(W, a));
        APFloat::opStatus st = x.roundToIntegral(R);
        result(x, (int) st);
      });
    }
    return 0;
  }
  if (!strcmp(mode, "next")) {
    bool down = atoi(argv[3]) != 0;
    for (unsigned long long a = 0; a < N; a++) {
      printf("%llx | ", a);
      GUARDED({
        APFloat x(S, APInt(W, a));
        APFloat::opStatus st = x.next(down);
        result(x, (int) st);
      });
    }
    return 0;
  }
  if (!strcmp(mode, "conv")) {
    const fltSemantics &T = sem(argv[3]);
    RoundingMode R = rm(argv[4]);
    for (unsigned long long a = 0; a < N; a++) {
      printf("%llx | ", a);
      GUARDED({
        APFloat x(S, APInt(W, a));
        bool loses = false;
        APFloat::opStatus st = x.convert(T, R, &loses);
        result(x, (int) st);
        printf(" %d", (int) loses);
      });
    }
    return 0;
  }
  if (!strcmp(mode, "toint")) {
    unsigned width = atoi(argv[3]);
    bool isSigned = atoi(argv[4]) != 0;
    RoundingMode R = rm(argv[5]);
    for (unsigned long long a = 0; a < N; a++) {
      printf("%llx | ", a);
      GUARDED({
        APFloat x(S, APInt(W, a));
        APSInt v(width, !isSigned);
        bool exact = false;
        APFloat::opStatus st = x.convertToInteger(v, R, &exact);
        printf("%llx %d %d", (unsigned long long) v.getZExtValue(), (int) st, (int) exact);
      });
    }
    return 0;
  }
  if (!strcmp(mode, "fromint")) {
    unsigned width = atoi(argv[3]);
    bool isSigned = atoi(argv[4]) != 0;
    RoundingMode R = rm(argv[5]);
    for (unsigned long long n = 0; n < (1ULL << width); n++) {
      printf("%llx | ", n);
      GUARDED({
        APFloat x(S);
        APFloat::opStatus st = x.convertFromAPInt(APInt(width, n), isSigned, R);
        result(x, (int) st);
      });
    }
    return 0;
  }
  if (!strcmp(mode, "scalbn")) {
    // x * 2^n for every value and every n in -span..span; n is printed with 4096 added
    RoundingMode R = rm(argv[3]);
    int span = (int) APFloat::semanticsMaxExponent(S) - (int) APFloat::semanticsMinExponent(S) +
               (int) APFloat::semanticsPrecision(S) + 3;
    for (unsigned long long a = 0; a < N; a++)
      for (int n = -span; n <= span; n++) {
        printf("%llx %x | ", a, (unsigned) (n + 4096));
        GUARDED({
          APFloat x(S, APInt(W, a));
          APFloat y = scalbn(x, n, R);
          result(y, 0);
        });
      }
    return 0;
  }
  if (!strcmp(mode, "misc")) {
    // a | ilogb getExactLog2Abs isDenormal isSmallest isSmallestNormalized isLargest isNormal inverse
    // inverse is "-" when getExactInverse returns false, else the category and pattern it stored
    for (unsigned long long a = 0; a < N; a++) {
      printf("%llx | ", a);
      GUARDED({
        APFloat x(S, APInt(W, a));
        printf("%d %d %d %d %d %d %d ", ilogb(x), x.getExactLog2Abs(), (int) x.isDenormal(), (int) x.isSmallest(),
               (int) x.isSmallestNormalized(), (int) x.isLargest(), (int) x.isNormal());
        fflush(stdout);
        APFloat inv(S);
        if (x.getExactInverse(&inv)) {
          printf("%c ", cat(inv));
          fflush(stdout);
          printf("%llx", (unsigned long long) inv.bitcastToAPInt().getZExtValue());
        } else {
          printf("-");
        }
      });
    }
    return 0;
  }
  if (!strcmp(mode, "cmp")) {
    for (unsigned long long a = 0; a < N; a++)
      for (unsigned long long b = 0; b < N; b++) {
        printf("%llx %llx | ", a, b);
        GUARDED({
          APFloat x(S, APInt(W, a)), y(S, APInt(W, b));
          printf("%d", (int) x.compare(y));
        });
      }
    return 0;
  }
  fprintf(stderr, "unknown mode %s\n", mode);
  return 2;
}
