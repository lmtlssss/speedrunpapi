// A product that is below the smallest normal number, inexact, and rounds up to the smallest normal.
// IEEE 754-2019 7.5: underflow is signaled when the result is tiny and inexact, with tininess detected
// either before or after rounding. Here both give "tiny": the exact product needs only 53 bits.
#include "llvm/ADT/APFloat.h"
#include <cfenv>
#include <cstdio>

using namespace llvm;

int main() {
  // (1 - 2^-53) * 2^-1022 = 0x1.fffffffffffffp-1023, halfway between the largest subnormal and DBL_MIN
  APFloat A(0x1.fffffffffffffp-1), B(0x1p-1022);
  APFloat P = A;
  APFloat::opStatus St = P.multiply(B, APFloat::rmNearestTiesToEven);
  printf("APFloat:  %a  status %d  (opInexact %d, opUnderflow %d)\n", P.convertToDouble(), (int) St,
         !!(St & APFloat::opInexact), !!(St & APFloat::opUnderflow));

  volatile double a = 0x1.fffffffffffffp-1, b = 0x1p-1022;
  std::feclearexcept(FE_ALL_EXCEPT);
  volatile double p = a * b;
  printf("hardware: %a  inexact %d  underflow %d\n", (double) p, !!std::fetestexcept(FE_INEXACT),
         !!std::fetestexcept(FE_UNDERFLOW));

  // the same shape in binary32 and binary16
  APFloat C(0x1.fffffep-1f), D(0x1p-126f);
  St = C.multiply(D, APFloat::rmNearestTiesToEven);
  printf("binary32: %a  status %d\n", (double) C.convertToFloat(), (int) St);
  bool Loses;
  APFloat E(0x1.ffcp-1), F(0x1p-14);
  E.convert(APFloat::IEEEhalf(), APFloat::rmNearestTiesToEven, &Loses);
  F.convert(APFloat::IEEEhalf(), APFloat::rmNearestTiesToEven, &Loses);
  St = E.multiply(F, APFloat::rmNearestTiesToEven);
  printf("binary16: bits %04llx  status %d\n", (unsigned long long) E.bitcastToAPInt().getZExtValue(), (int) St);
  return 0;
}
