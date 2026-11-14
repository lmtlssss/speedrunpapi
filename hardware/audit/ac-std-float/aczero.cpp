// ceil, floor, trunc and round of ac_std_float<32,8> beside the C library's ceilf, floorf, truncf and roundf,
// on operands whose result is zero. The library's own ac_ieee_float<binary32> calls these same C functions when
// AC_IEEE_FLOAT_USE_BUILTIN is defined, so the two columns are the library's two modes.
#include <ac_std_float.h>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>

static float tof(uint32_t b) { float f; memcpy(&f, &b, 4); return f; }
static uint32_t fromf(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }

int main() {
  const uint32_t operands[5] = {0x80000000u, 0xBF000000u, 0xBE800000u, 0x80000001u, 0xBF7FFFFFu};
  const char *names[5] = {"-0", "-0.5", "-0.25", "-2^-149", "-(1 - 2^-24)"};
  int differ = 0;
  for (int i = 0; i < 5; i++) {
    ac_std_float<32, 8> x;
    x.d = operands[i];
    volatile float f = tof(operands[i]);
    uint32_t lib[4] = {(uint32_t) x.ceil().d.to_uint64(), (uint32_t) x.floor().d.to_uint64(),
                       (uint32_t) x.trunc().d.to_uint64(), (uint32_t) x.round().d.to_uint64()};
    uint32_t c[4] = {fromf(ceilf(f)), fromf(floorf(f)), fromf(truncf(f)), fromf(roundf(f))};
    const char *fn[4] = {"ceil", "floor", "trunc", "round"};
    for (int k = 0; k < 4; k++) {
      bool same = lib[k] == c[k];
      differ += !same;
      printf("%-5s(%-12s)  ac_std_float %08x   C library %08x%s\n", fn[k], names[i], lib[k], c[k], same ? "" : "   differ");
    }
  }
  printf("%d of 20 differ\n", differ);
  return 0;
}
