// ac_std_float<32,8> and ac_std_float<64,11> in round to nearest even beside the processor's own float and double.
// usage: achost SEED N        N operand sets per operation and format; prints counts and the first wrong cases
#include <ac_std_float.h>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

static uint64_t s[2];
static uint64_t rnd() {            // xorshift128+
  uint64_t x = s[0], y = s[1];
  s[0] = y;
  x ^= x << 23;
  s[1] = x ^ y ^ (x >> 17) ^ (y >> 26);
  return s[1] + y;
}

static uint64_t pattern(int bits) {
  uint64_t full = bits == 64 ? ~0ULL : ((1ULL << bits) - 1);
  switch (rnd() % 8) {
    case 0: return 0;
    case 1: return 1;
    case 2: return full;
    case 3: return full - 1;
    case 4: return 1ULL << (bits - 1);
    case 5: return rnd() & full & ~((1ULL << (rnd() % bits)) - 1);
    default: return rnd() & full;
  }
}

// a float whose exponent is near a base exponent, so that pairs sit at chosen distances
static uint32_t f32(int base) {
  uint32_t sign = (uint32_t)(rnd() & 1) << 31;
  int k = (int)(rnd() % 12);
  int e;
  if (k == 0) e = 0;
  else if (k == 1) e = 255;
  else if (k == 2) e = (int)(rnd() % 255);
  else e = base + (int)(rnd() % 70) - 35;
  if (e < 0) e = 0;
  if (e > 255) e = 255;
  return sign | ((uint32_t) e << 23) | (uint32_t) pattern(23);
}
static uint64_t f64(int base) {
  uint64_t sign = (rnd() & 1) << 63;
  int k = (int)(rnd() % 12);
  int e;
  if (k == 0) e = 0;
  else if (k == 1) e = 2047;
  else if (k == 2) e = (int)(rnd() % 2047);
  else e = base + (int)(rnd() % 140) - 70;
  if (e < 0) e = 0;
  if (e > 2047) e = 2047;
  return sign | ((uint64_t) e << 52) | pattern(52);
}

static float tof(uint32_t b) { float f; memcpy(&f, &b, 4); return f; }
static uint32_t fromf(float f) { uint32_t b; memcpy(&b, &f, 4); return b; }
static double tod(uint64_t b) { double f; memcpy(&f, &b, 8); return f; }
static uint64_t fromd(double f) { uint64_t b; memcpy(&b, &f, 8); return b; }
static bool nan32(uint32_t b) { return (b & 0x7F800000u) == 0x7F800000u && (b & 0x7FFFFFu); }
static bool nan64(uint64_t b) { return (b & 0x7FF0000000000000ULL) == 0x7FF0000000000000ULL && (b & 0xFFFFFFFFFFFFFULL); }

int main(int argc, char **argv) {
  s[0] = 0x9E3779B97F4A7C15ULL ^ (uint64_t) atoll(argc > 1 ? argv[1] : "1");
  s[1] = 0xD1B54A32D192ED03ULL;
  long n = argc > 2 ? atol(argv[2]) : 1000000;
  const char *names[6] = {"add", "sub", "mult", "div", "sqrt", "fma"};
  typedef ac_std_float<32, 8> F;
  typedef ac_std_float<64, 11> D;
  for (int op = 0; op < 6; op++) {
    long wrong32 = 0, wrong64 = 0;
    int shown = 0;
    for (long i = 0; i < n; i++) {
      int base = 64 + (int)(rnd() % 128);
      uint32_t a = f32(base), b = f32(base), c = f32(base);
      F x, y, z, r;
      x.d = a; y.d = b; z.d = c;
      float h;
      volatile float fa = tof(a), fb = tof(b), fc = tof(c);
      switch (op) {
        case 0: r = x.add<AC_RND_CONV, false>(y); h = fa + fb; break;
        case 1: r = x.sub<AC_RND_CONV, false>(y); h = fa - fb; break;
        case 2: r = x.mult<AC_RND_CONV, false>(y); h = fa * fb; break;
        case 3: r = x.div<AC_RND_CONV, false>(y); h = fa / fb; break;
        case 4: r = x.sqrt<AC_RND_CONV, false>(); h = sqrtf(fa); break;
        default: r = x.fma<AC_RND_CONV, false>(y, z); h = fmaf(fa, fb, fc); break;
      }
      uint32_t got = (uint32_t) r.d.to_uint64(), want = fromf(h);
      if (got != want && !(nan32(got) && nan32(want))) {
        wrong32++;
        if (shown < 4) { shown++; printf("  %s binary32: %08x %08x %08x -> %08x, processor %08x\n", names[op], a, b, c, got, want); }
      }
      int base2 = 600 + (int)(rnd() % 800);
      uint64_t a2 = f64(base2), b2 = f64(base2), c2 = f64(base2);
      D x2, y2, z2, r2;
      x2.d = (long long) a2; y2.d = (long long) b2; z2.d = (long long) c2;
      double h2;
      volatile double da = tod(a2), db = tod(b2), dc = tod(c2);
      switch (op) {
        case 0: r2 = x2.add<AC_RND_CONV, false>(y2); h2 = da + db; break;
        case 1: r2 = x2.sub<AC_RND_CONV, false>(y2); h2 = da - db; break;
        case 2: r2 = x2.mult<AC_RND_CONV, false>(y2); h2 = da * db; break;
        case 3: r2 = x2.div<AC_RND_CONV, false>(y2); h2 = da / db; break;
        case 4: r2 = x2.sqrt<AC_RND_CONV, false>(); h2 = sqrt(da); break;
        default: r2 = x2.fma<AC_RND_CONV, false>(y2, z2); h2 = fma(da, db, dc); break;
      }
      uint64_t got2 = (uint64_t) r2.d.to_uint64(), want2 = fromd(h2);
      if (got2 != want2 && !(nan64(got2) && nan64(want2))) {
        wrong64++;
        if (shown < 8) { shown++; printf("  %s binary64: %016llx %016llx %016llx -> %016llx, processor %016llx\n", names[op],
                                         (unsigned long long) a2, (unsigned long long) b2, (unsigned long long) c2,
                                         (unsigned long long) got2, (unsigned long long) want2); }
      }
    }
    printf("%-5s %ld operand sets: binary32 %ld wrong, binary64 %ld wrong\n", names[op], n, wrong32, wrong64);
  }
  return 0;
}
