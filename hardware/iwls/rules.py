"""The rules behind the IWLS contest functions ex280 to ex299, and a check against the contest truth tables.

usage: python3 rules.py DIR        DIR holds ex280.truth ... ex299.truth from
                                   https://github.com/alanminko/iwls2026-ls-contest (benchmarks/truth)

Each function has n inputs and n outputs, n = 12 ... 16 (ex280, ex285, ex290, ex295 have n = 12, the next n = 13, and so on).
x is the input word, bit 0 the first input.  a = x[3:0], t = x[n-1:n-4].
"""
import sys


def prefix_majority(x, n):
    """ex280 - ex284"""
    m = (1 << n) - 1
    g = p = 0
    for k in range(n):                      # g_k = x_0 ^ ... ^ x_k
        p ^= (x >> k) & 1
        g |= p << k
    rev = int(format(x, "0%db" % n)[::-1], 2)
    ror1 = ((x >> 1) | (x << (n - 1))) & m
    y = (g & rev) | (~g & ror1 & m)         # y_k = g_k ? x_{n-1-k} : x_{k+1}
    h = p = 0
    for k in range(n):                      # h_k = y_0 ^ ... ^ y_{k-1}
        h |= p << k
        p ^= (y >> k) & 1
    y2 = ((y >> 2) | (y << (n - 2))) & m
    return (h & y) | (h & y2) | (y & y2)    # majority(h_k, y_k, y_{k+2})


def swap_network(x, n):
    """ex285 - ex289"""
    s = (x & 15) ^ (x >> (n - 4))
    b = [(x >> i) & 1 for i in range(n)]
    for i in range(0, n - 1, 2):            # sort each pair; s_0 picks the direction
        lo, hi = min(b[i], b[i + 1]), max(b[i], b[i + 1])
        b[i], b[i + 1] = (hi, lo) if s & 1 else (lo, hi)
    for k in (1, 2, 3):                     # exchange b[i], b[i+D] when b[i^1] equals s_k
        d, sk, old = 1 << k, (s >> k) & 1, b[:]
        for i in range(n - d):
            if not i & d and old[i ^ 1] == sk:
                b[i], b[i + d] = old[i + d], old[i]
    return sum(v << i for i, v in enumerate(b))


def rotate_chi(x, n):
    """ex290 - ex294"""
    m = (1 << n) - 1
    xx = (x << n) | x                       # rotations are shifts of the double word {x, x}
    left = lambda s: ((xx << s) >> n) & m
    right = lambda s: (xx >> s) & m
    a, t = x & 15, x >> (n - 4)
    g = left(a ^ t) | (left(a) ^ right(t))
    g1 = ((g >> 1) | (g << (n - 1))) & m
    g2 = ((g >> 2) | (g << (n - 2))) & m
    return g ^ (~g1 & g2 & m)               # f_i = g_i ^ (~g_{i+1} & g_{i+2})


def ring_of_pairs(x, n):
    """ex295 - ex299"""
    m = (1 << n) - 1
    y = x
    for _ in range(n):                      # n rounds
        y1 = ((y >> 1) | (y << (n - 1))) & m
        y2 = ((y >> 2) | (y << (n - 2))) & m
        z = y ^ (y1 & y2)                   # z_i = y_i ^ (y_{i+1} & y_{i+2})
        y = 0
        for j in range(n // 2):             # sort each pair; x_{2j} ^ z_{2j+2} picks the direction
            a, b = (z >> (2 * j)) & 1, (z >> (2 * j + 1)) & 1
            d = ((x >> (2 * j)) ^ (z >> ((2 * j + 2) % n))) & 1
            lo, hi = a & b, a | b
            y |= (hi if d else lo) << (2 * j) | (lo if d else hi) << (2 * j + 1)
    return y                                # at odd n the last bit has no pair and stays 0


RULES = [(280, prefix_majority), (285, swap_network), (290, rotate_chi), (295, ring_of_pairs)]


def load(path):
    """A .truth file: one line per output, minterm 2^n - 1 first."""
    rows = [r.strip() for r in open(path) if r.strip()]
    n = len(rows[0]).bit_length() - 1
    return n, [sum(int(rows[o][(1 << n) - 1 - x]) << o for o in range(len(rows))) for x in range(1 << n)]


if __name__ == "__main__":
    for first, rule in RULES:
        for e in range(first, first + 5):
            n, table = load("%s/ex%d.truth" % (sys.argv[1], e))
            bad = sum(1 for x in range(1 << n) if rule(x, n) != table[x])
            print("ex%d  n = %d  %s  %d of %d inputs differ" % (e, n, rule.__name__, bad, 1 << n))
