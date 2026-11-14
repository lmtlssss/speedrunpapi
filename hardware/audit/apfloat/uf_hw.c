/* Two products just below DBL_MIN on the processor, with its exception flags.
   (1 - 2^-53) * 2^-1022                 exact in 53 bits: tiny before and after rounding
   (1 - 2^-52) * (1 + 2^-52) * 2^-1022   = (1 - 2^-104) * 2^-1022: rounds to 2^-1022 in 53 bits,
                                         tiny before rounding only */
#include <fenv.h>
#include <stdio.h>

#pragma STDC FENV_ACCESS ON

static void one(double a, double b, const char *what) {
  volatile double x = a, y = b, p;
  feclearexcept(FE_ALL_EXCEPT);
  p = x * y;
  printf("%-40s -> %a  inexact %d  underflow %d\n", what, (double) p, !!fetestexcept(FE_INEXACT),
         !!fetestexcept(FE_UNDERFLOW));
}

int main(void) {
#if defined(__x86_64__)
  printf("x86-64 (tininess after rounding)\n");
#elif defined(__aarch64__)
  printf("arm64 (tininess before rounding)\n");
#endif
  one(0x1.fffffffffffffp-1, 0x1p-1022, "(1 - 2^-53) * 2^-1022");
  one(0x1.ffffffffffffep-1, 0x1.0000000000001p-1022, "(1 - 2^-52) * (1 + 2^-52) * 2^-1022");
  return 0;
}
