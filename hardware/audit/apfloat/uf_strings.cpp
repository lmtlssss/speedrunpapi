// The same boundary through the two string readers: hexadecimal goes through normalize with all its
// bits, decimal is cut to the least exponent first.
#include "llvm/ADT/APFloat.h"
#include "llvm/Support/Error.h"
#include <cstdio>

using namespace llvm;

static void one(const char *text, const char *note) {
  APFloat x(APFloat::IEEEdouble());
  auto st = x.convertFromString(text, APFloat::rmNearestTiesToEven);
  if (!st) {
    consumeError(st.takeError());
    printf("%-28s parse error\n", text);
    return;
  }
  printf("%-28s -> %-24a status %2d   %s\n", text, x.convertToDouble(), (int) *st, note);
}

int main() {
  one("0x1.fffffffffffff0p-1023", "f = 1/2, tiny: want 24");
  one("0x1.fffffffffffff4p-1023", "f = 5/8, tiny: want 24");
  one("0x1.fffffffffffff8p-1023", "f = 3/4, not tiny: want 16");
  one("0x1.fffffffffffffcp-1023", "f = 7/8, not tiny: want 16");
  // decimal: the largest subnormal is 2.2250738585072009e-308, 2^-1022 is 2.2250738585072014e-308
  one("2.22507385850720118e-308", "f near 0.55, tiny: want 24");
  one("2.2250738585072012e-308", "f near 0.6, tiny: want 24");
  one("2.22507385850720135e-308", "f near 0.9, not tiny: want 16");
  one("2.2250738585072010e-308", "stays subnormal: want 24");
  return 0;
}
