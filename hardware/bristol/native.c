// The four large float circuits against the arithmetic of the host processor (IEEE 754 binary64, round to nearest
// even), with the NaN rules of the published circuits, on aimed operands.
// usage: native OP COUNT SEED      OP = add | mul | div | sqrt ; COUNT operands (rounded up to a multiple of 64)
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "c_add.h"
#include "c_mul.h"
#include "c_div.h"
#include "c_sqrt.h"

#define SIGN 0x8000000000000000ULL
#define INF 0x7ff0000000000000ULL
#define QUIET 0x0008000000000000ULL
#define DNAN 0x7fffffffffffffffULL
#define FRAC 0x000fffffffffffffULL
#define BIAS 1023

static uint64_t s[2];
static inline uint64_t rnd(void) {                 // xoroshiro128+
    uint64_t a = s[0], b = s[1], r = a + b;
    b ^= a;
    s[0] = ((a << 24) | (a >> 40)) ^ b ^ (b << 16);
    s[1] = (b << 37) | (b >> 27);
    return r;
}
static inline uint64_t below(uint64_t n) { return rnd() % n; }
static inline int range(int lo, int hi) { return lo + (int)below((uint64_t)(hi - lo)); }   // lo <= x < hi

static inline double val(uint64_t u) { double d; memcpy(&d, &u, 8); return d; }
static inline uint64_t bits(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static inline int is_nan(uint64_t u) { return (u & ~SIGN) > INF; }
static inline int is_snan(uint64_t u) { return ((u >> 51) & 0xfff) == 0xffe && (u & 0x0007ffffffffffffULL); }
static uint64_t propagate(uint64_t a, uint64_t b) {
    if (is_snan(b)) return b | QUIET;
    if (is_snan(a)) return a | QUIET;
    if (is_nan(b)) return b | QUIET;
    return a | QUIET;
}

static uint64_t r_add(uint64_t a, uint64_t b) {
    if (is_nan(a) || is_nan(b)) return propagate(a, b);
    int ai = (a & ~SIGN) == INF, bi = (b & ~SIGN) == INF;
    if (ai && bi) return ((a ^ b) & SIGN) ? DNAN : a;
    if (ai) return a;
    if (bi) return b;
    volatile double x = val(a), y = val(b);
    return bits(x + y);
}
static uint64_t r_mul(uint64_t a, uint64_t b) {
    if (is_nan(a) || is_nan(b)) return propagate(a, b);
    uint64_t sg = (a ^ b) & SIGN, am = a & ~SIGN, bm = b & ~SIGN;
    if (am == INF || bm == INF) return (am == 0 || bm == 0) ? DNAN : (sg | INF);
    volatile double x = val(a), y = val(b);
    return bits(x * y);
}
static uint64_t r_div(uint64_t a, uint64_t b) {
    if (is_nan(a) || is_nan(b)) return propagate(a, b);
    uint64_t sg = (a ^ b) & SIGN, am = a & ~SIGN, bm = b & ~SIGN;
    if (am == INF) return bm == INF ? DNAN : (sg | INF);
    if (bm == INF) return sg;
    if (bm == 0) return am == 0 ? DNAN : (sg | INF);
    volatile double x = val(a), y = val(b);
    return bits(x / y);
}
static uint64_t r_sqrt(uint64_t a) {
    if (is_nan(a)) return a | QUIET;
    if ((a & ~SIGN) == 0) return a;
    if (a & SIGN) return DNAN;
    if (a == INF) return a;
    volatile double x = val(a);
    return bits(sqrt(x));
}

static const uint64_t SPECIALS[] = {
    0x0000000000000000ULL, 0x8000000000000000ULL, 0x0000000000000001ULL, 0x8000000000000001ULL, 0x0000000000000002ULL,
    0x000fffffffffffffULL, 0x800fffffffffffffULL, 0x0010000000000000ULL, 0x8010000000000000ULL, 0x0010000000000001ULL,
    0x001fffffffffffffULL, 0x0008000000000000ULL, 0x3ff0000000000000ULL, 0xbff0000000000000ULL, 0x3ff0000000000001ULL,
    0x3fefffffffffffffULL, 0x4000000000000000ULL, 0x3fe0000000000000ULL, 0x7fefffffffffffffULL, 0xffefffffffffffffULL,
    0x7fe0000000000000ULL, 0x7ff0000000000000ULL, 0xfff0000000000000ULL, 0x7ff8000000000000ULL, 0xfff8000000000000ULL,
    0x7ff0000000000001ULL, 0xfff0000000000001ULL, 0x7ff7ffffffffffffULL, 0x7fffffffffffffffULL, 0xffffffffffffffffULL,
    0x7ff8000000000001ULL, 0xfff8000000000005ULL, 0x7ff4000000000000ULL, 0x4340000000000000ULL, 0x4330000000000000ULL,
    0x433fffffffffffffULL, 0x43e0000000000000ULL, 0xc3e0000000000000ULL, 0x43dfffffffffffffULL, 0xc3e0000000000001ULL,
    0x3fd0000000000000ULL, 0x3ff8000000000000ULL, 0x4004000000000000ULL, 0xc004000000000000ULL, 0x3fe0000000000001ULL,
    0x3fdfffffffffffffULL, 0x4008000000000000ULL, 0x4022000000000000ULL, 0x1e60000000000000ULL, 0x0020000000000000ULL,
};
#define NSPEC ((int)(sizeof(SPECIALS) / sizeof(SPECIALS[0])))

static uint64_t mantissa(void) {
    int k = (int)below(12), sh;
    switch (k) {
    case 0: return 0;
    case 1: return FRAC;
    case 2: return 1ULL << below(52);
    case 3: return FRAC ^ (1ULL << below(52));
    case 4: return rnd() & ((1ULL << range(1, 53)) - 1);
    case 5: sh = range(1, 52); return ((rnd() & FRAC) >> sh) << sh;
    case 6: return FRAC >> below(52);
    case 7: sh = (int)below(52); return ((FRAC >> sh) << sh) & FRAC;
    case 8: return rnd() & rnd() & rnd() & FRAC;
    default: return rnd() & FRAC;
    }
}
static int exponent(void) {
    static const int lo[] = {0, 0, 1, 2, 3}, hi[] = {0x7ff, 0x7fe, 0x7fd, 0x7fc};
    switch ((int)below(10)) {
    case 0: return lo[below(5)];
    case 1: return hi[below(4)];
    case 2: return BIAS + range(-3, 4);
    case 3: return BIAS + range(50, 66);
    case 4: return BIAS - range(50, 66);
    case 5: return range(1, 60);
    default: return (int)below(0x800);
    }
}
static inline int clampe(int e) { return e < 0 ? 0 : (e > 0x7ff ? 0x7ff : e); }
static inline uint64_t mk(uint64_t sg, int e, uint64_t m) { return (sg << 63) | ((uint64_t)clampe(e) << 52) | (m & FRAC); }
static uint64_t one(void) {
    int k = (int)below(20);
    if (k == 0) return SPECIALS[below(NSPEC)];
    if (k == 1) return rnd();
    return mk(rnd() & 1, exponent(), mantissa());
}
static uint64_t near_(uint64_t a) {
    uint64_t sg = a >> 63, m = a & FRAC;
    int e = (int)((a >> 52) & 0x7ff);
    switch ((int)below(8)) {
    case 0: return mk(rnd() & 1, e, m + (uint64_t)(int64_t)range(-3, 4));
    case 1: return mk(sg ^ 1, e + range(-1, 2), m + (uint64_t)(int64_t)range(-2, 3));
    case 2: return mk(rnd() & 1, e + range(-2, 3), mantissa());
    case 3: return mk(rnd() & 1, e - range(50, 58), mantissa());
    case 4: return mk(rnd() & 1, e + range(50, 58), mantissa());
    case 5: return a ^ ((rnd() & 1) << 63);
    default: return one();
    }
}
static inline int blen(uint64_t x) { return x ? 64 - __builtin_clzll(x) : 0; }

static void pair(int op, uint64_t *pa, uint64_t *pb) {
    uint64_t x = one();
    int k = (int)below(10);
    if (op == 0) { *pa = x; *pb = k < 7 ? near_(x) : one(); return; }
    if (op == 1) {
        if (k < 3) {
            static const int t[] = {BIAS - 54, BIAS - 53, BIAS - 52, BIAS - 51, BIAS - 1, BIAS, BIAS + 1, BIAS + 2,
                                    2 * BIAS + 1022, 2 * BIAS + 1023, 2 * BIAS + 1024, 2 * BIAS + 1025};
            int ex = range(1, 0x7ff), target = t[below(12)] + range(-2, 3);
            *pa = mk(rnd() & 1, ex, mantissa()); *pb = mk(rnd() & 1, target - ex, mantissa()); return;
        }
        if (k < 5) {
            static const int tot[] = {53, 54, 55, 56};
            int ka = range(1, 54), kb = tot[below(4)] - ka;
            if (kb < 1) kb = 1;
            if (kb > 53) kb = 53;
            uint64_t ma = ((rnd() & ((1ULL << ka) - 1)) | 1 | (1ULL << (ka - 1))) << (53 - ka);
            uint64_t mb = ((rnd() & ((1ULL << kb) - 1)) | 1 | (1ULL << (kb - 1))) << (53 - kb);
            int ex = exponent(), ey = exponent();
            ex = ex < 1 ? 1 : (ex > 0x7fe ? 0x7fe : ex);
            ey = ey < 1 ? 1 : (ey > 0x7fe ? 0x7fe : ey);
            *pa = mk(rnd() & 1, ex, ma); *pb = mk(rnd() & 1, ey, mb); return;
        }
        *pa = x; *pb = one(); return;
    }
    if (k < 3) {
        static const int t[] = {-BIAS - 54, -BIAS - 53, -BIAS - 52, -BIAS - 51, -BIAS - 1, -BIAS, -BIAS + 1, -BIAS + 2,
                                BIAS - 1, BIAS, BIAS + 1, BIAS + 2};
        int ey = range(1, 0x7ff), target = t[below(12)] + range(-2, 3);
        *pa = mk(rnd() & 1, target + ey, mantissa()); *pb = mk(rnd() & 1, ey, mantissa()); return;
    }
    if (k < 5) {                                    // exact quotients, also landing among the subnormals
        int kq = range(1, 30), ky = range(1, 54 - kq);
        uint64_t q = (rnd() & ((1ULL << kq) - 1)) | 1 | (1ULL << (kq - 1));
        uint64_t my = (rnd() & ((1ULL << ky) - 1)) | 1 | (1ULL << (ky - 1));
        uint64_t mx = q * my;
        mx <<= 53 - blen(mx);
        my <<= 53 - blen(my);
        int ey = range(1, 0x7ff), d;
        switch ((int)below(5)) {
        case 0: d = 0; break;
        case 1: d = 1; break;
        case 2: d = -1; break;
        case 3: d = range(-1080, -1010); break;
        default: d = range(-60, 60);
        }
        int ex = ey + d;
        ex = ex < 1 ? 1 : (ex > 0x7fe ? 0x7fe : ex);
        *pa = mk(rnd() & 1, ex, mx); *pb = mk(rnd() & 1, ey, my); return;
    }
    *pa = x; *pb = k < 7 ? near_(x) : one();
}
static uint64_t square(void) {
    int k = (int)below(8);
    if (k < 3) {
        int n = range(1, 54);
        unsigned __int128 r = (rnd() & ((1ULL << n) - 1)) | 1 | (1ULL << (n - 1));
        unsigned __int128 sq = r * r;
        int len = 0;
        for (unsigned __int128 t = sq; t; t >>= 1) len++;
        uint64_t m = len > 53 ? (uint64_t)(sq >> (len - 53)) : (uint64_t)sq << (53 - len);
        static const int64_t dd[] = {0, 0, 1, -1, 2, -2};
        uint64_t x = ((uint64_t)range(1, 0x7ff) << 52) | (m & FRAC);
        return (x + (uint64_t)dd[below(6)]) & 0x7fffffffffffffffULL;
    }
    if (k == 3) return rnd() & FRAC;
    if (k == 4) return rnd() & ((1ULL << range(1, 53)) - 1);
    uint64_t x = one();
    return below(4) ? (x & 0x7fffffffffffffffULL) : x;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: native add|mul|div|sqrt COUNT SEED\n"); return 2; }
    int op = !strcmp(argv[1], "add") ? 0 : !strcmp(argv[1], "mul") ? 1 : !strcmp(argv[1], "div") ? 2 : 3;
    uint64_t count = strtoull(argv[2], 0, 10), seed = strtoull(argv[3], 0, 10);
    s[0] = 0x9e3779b97f4a7c15ULL ^ (seed * 0xbf58476d1ce4e5b9ULL);
    s[1] = 0x94d049bb133111ebULL + seed;
    for (int i = 0; i < 20; i++) rnd();
    uint64_t in[128], out[64], a[64], b[64];
    uint64_t done = 0, bad = 0, spec = 0;
    while (done < count) {
        for (int t = 0; t < 64; t++) {
            if (op == 3) { a[t] = square(); b[t] = 0; }
            else if (spec < (uint64_t)NSPEC * NSPEC) { a[t] = SPECIALS[spec / NSPEC]; b[t] = SPECIALS[spec % NSPEC]; spec++; }
            else pair(op, &a[t], &b[t]);
        }
        memset(in, 0, sizeof in);
        for (int t = 0; t < 64; t++) {
            uint64_t x = a[t], y = b[t];
            for (int i = 0; i < 64; i++) {
                in[i] |= ((x >> i) & 1) << t;
                in[64 + i] |= ((y >> i) & 1) << t;
            }
        }
        if (op == 0) c_add(in, out);
        else if (op == 1) c_mul(in, out);
        else if (op == 2) c_div(in, out);
        else c_sqrt(in, out);
        for (int t = 0; t < 64; t++) {
            uint64_t got = 0;
            for (int i = 0; i < 64; i++) got |= ((out[i] >> t) & 1) << i;
            uint64_t want = op == 0 ? r_add(a[t], b[t]) : op == 1 ? r_mul(a[t], b[t]) : op == 2 ? r_div(a[t], b[t]) : r_sqrt(a[t]);
            if (got != want) {
                if (bad < 5) printf("  %016llx %016llx -> %016llx, the processor gives %016llx\n",
                                    (unsigned long long)a[t], (unsigned long long)b[t], (unsigned long long)got, (unsigned long long)want);
                bad++;
            }
        }
        done += 64;
    }
    printf("%s: %llu operands, %llu differ from the processor's arithmetic\n", argv[1], (unsigned long long)done, (unsigned long long)bad);
    return bad ? 1 : 0;
}
