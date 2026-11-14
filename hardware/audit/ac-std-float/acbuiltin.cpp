// ac_ieee_float<binary32>::ceil, trunc and round on -0.5 and -0.25, compiled twice: with and without
// AC_IEEE_FLOAT_USE_BUILTIN. Prints the bit patterns.
#include <ac_std_float.h>
#include <cstdio>

int main() {
  ac_ieee_float<binary32> a(-0.5f), b(-0.25f);
#ifdef AC_IEEE_FLOAT_USE_BUILTIN
  const char *mode = "builtin";
#else
  const char *mode = "ac_std_float";
#endif
  printf("%-13s ceil(-0.5) %08x  trunc(-0.5) %08x  round(-0.25) %08x\n", mode,
         (unsigned) a.ceil().data_ac_int().to_uint64(), (unsigned) a.trunc().data_ac_int().to_uint64(),
         (unsigned) b.round().data_ac_int().to_uint64());
  return 0;
}
