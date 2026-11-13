# Bit-true model of fp_sqrt_core.sv (CVA5 at 2acf79f) beside the exact integer square root.
# usage: python3 sqrt_core_model.py [hex double ...]
import math
import sys

W = 57                                   # sqrt.DATA_WIDTH for double precision: hidden + 52 + 4
M = (1 << W) - 1


def radicand(x):
    """The 57-bit word fp_sqrt.sv hands to the core for a normal double."""
    e = (x >> 52) & 0x7FF
    f = x & ((1 << 52) - 1)
    norm_expo = e                        # normal operand: hidden bit set, no prenormalisation shift
    return ((1 << 55) | (f << 3)) if norm_expo & 1 else ((1 << 56) | (f << 4))


def core(rad_in, wide):
    """wide=False: the registers as written. wide=True: two more bits, sticky from the remainder of the step."""
    ww = W + 2 if wide else W
    keep = W if wide else W - 2          # bits of the kept remainder carried to the next step
    res = 0
    cur = rad_in >> (W - 2)
    rad = (rad_in << 2) & M
    rem = 0
    for _ in range(W):
        sub = (((res if wide else res & ((1 << (W - 2)) - 1)) << 2) | 1) & ((1 << ww) - 1)
        overflow = cur < sub
        kept = cur if overflow else cur - sub
        nxt = ((kept & ((1 << keep) - 1)) << 2) | (rad >> (W - 2))
        res = ((res << 1) | (0 if overflow else 1)) & M
        rem = (1 if kept else 0) if wide else nxt & M
        cur = nxt
        rad = (rad << 2) & M
    return res, rem


def exact(rad_in):
    n = rad_in << W                      # 57 result bits need 114 radicand bits
    r = math.isqrt(n)
    return r, n - r * r


if __name__ == "__main__":
    for h in sys.argv[1:] or ["400ffffff6000001", "41eb0d20db3380c2", "4000000000000000"]:
        rin = radicand(int(h, 16))
        a, ar = core(rin, False)
        b, br = core(rin, True)
        e, er = exact(rin)
        print(h, "as written: result %015x remainder_zero=%s | widened: result %015x remainder_zero=%s | exact: %015x remainder_zero=%s"
              % (a, ar == 0, b, br == 0, e, er == 0))
