// The cases of the proposed unit test, as a program: a binary128 value just below the smallest normal
// double is converted to double. f is how far the value lies from the largest subnormal toward 2^-1022.
#include "llvm/ADT/APFloat.h"
#include <cstdio>

using namespace llvm;

int main() {
  struct Case {
    const char *value;
    const char *where;
    APFloat::roundingMode rm;
    const char *mode;
    int want;
  };
  const int UI = APFloat::opUnderflow | APFloat::opInexact, I = APFloat::opInexact;
  const Case cases[] = {
      {"0x1.fffffffffffff0p-1023", "f = 1/2", APFloat::rmNearestTiesToEven, "nearest even", UI},
      {"0x1.fffffffffffff4p-1023", "f = 5/8", APFloat::rmNearestTiesToEven, "nearest even", UI},
      {"0x1.fffffffffffff8p-1023", "f = 3/4", APFloat::rmNearestTiesToEven, "nearest even", I},
      {"0x1.fffffffffffff8p-1023", "f = 3/4", APFloat::rmNearestTiesToAway, "nearest away", I},
      {"0x1.fffffffffffffcp-1023", "f = 7/8", APFloat::rmNearestTiesToEven, "nearest even", I},
      {"0x1.fffffffffffff0p-1023", "f = 1/2", APFloat::rmNearestTiesToAway, "nearest away", UI},
      {"0x1.ffffffffffffe8p-1023", "f = 1/4", APFloat::rmTowardPositive, "toward +inf", UI},
      {"0x1.fffffffffffff0p-1023", "f = 1/2", APFloat::rmTowardPositive, "toward +inf", UI},
      {"0x1.fffffffffffff4p-1023", "f = 5/8", APFloat::rmTowardPositive, "toward +inf", I},
      {"-0x1.fffffffffffff0p-1023", "f = 1/2", APFloat::rmTowardNegative, "toward -inf", UI},
      {"-0x1.fffffffffffff4p-1023", "f = 5/8", APFloat::rmTowardNegative, "toward -inf", I},
      {"0x1.fffffffffffffcp-1023", "f = 7/8", APFloat::rmTowardZero, "toward zero", UI},
      {"0x1.fffffffffffffcp-1023", "f = 7/8", APFloat::rmTowardNegative, "toward -inf", UI},
  };
  int bad = 0;
  for (const Case &c : cases) {
    APFloat x(APFloat::IEEEquad(), c.value);
    bool loses = false;
    int st = (int) x.convert(APFloat::IEEEdouble(), c.rm, &loses);
    printf("%-26s %-8s %-13s -> %-24a status %2d  want %2d %s\n", c.value, c.where, c.mode, x.convertToDouble(), st,
           c.want, st == c.want ? "" : "DIFFERS");
    bad += st != c.want;
  }
  printf("%d differ\n", bad);
  return 0;
}
