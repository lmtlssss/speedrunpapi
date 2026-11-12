"""Word-level model of fold division.

d is normalised (dn = d * 2^s, top bit set) and multiplied by a table value M chosen from its top t bits
so that D = M * dn lies just below 2^P:  eps = 2^P - D,  0 <= eps < 2^(P - g).
Then  T * 2^P = T * D + T * eps,  so the top T of the running value W is folded:
    W = T * 2^p + L   ->   W' = L + T * eps * 2^(p - P),      W - W' = T * D * 2^(p - P).
W is kept as two words (S, C); T = top(S) + top(C).  After k folds  M * a * 2^s = Q * D + W, W < 3 * 2^P,
so a = Q * d + R0 with 0 <= R0 < 3 d, and the answer is Q + j, R0 - j d for the j in {0, 1, 2} with 0 <= R0 - j d < d.
"""
import random


def params(n, b):
    g = b + 2
    t = m = g + 2
    k = -(-n // b)
    return dict(n=n, b=b, g=g, t=t, m=m, k=k, P=n - 1 + m, npad=k * b)


def table(pr):
    n, t, P = pr["n"], pr["t"], pr["P"]
    out = {}
    for idx in range(1 << (t - 1), 1 << t):
        hi = ((idx + 1) << (n - t)) - 1 if n >= t else None
        out[idx] = (1 << P) // hi
    return out


def split(w, rng):
    if rng is None:
        return w, 0
    s = rng.randrange(w + 1)
    return s, w - s


def divide(a, d, pr, tab, rng=None, stats=None):
    n, b, g, t, m, k, P, npad = (pr[x] for x in ("n", "b", "g", "t", "m", "k", "P", "npad"))
    assert d
    s = n - d.bit_length()
    dn, x = d << s, a << s
    M = tab[dn >> (n - t)]
    eps = (1 << P) - M * dn
    assert 0 <= eps < 1 << (P - g), (eps, P, g)
    S, C = split(M * x, rng)
    Q = 0
    for i in range(k):
        p = P + npad - (i + 1) * b
        TS, LS = divmod(S, 1 << p)
        TC, LC = divmod(C, 1 << p)
        T = TS + TC
        assert TS < 3 << b and TC < 3 << b
        if stats is not None:
            stats["T"] = max(stats.get("T", 0), TS, TC)
        W = LS + LC + ((T * eps) << (p - P))
        Q += T << (p - P)
        S, C = split(W, rng)
    R0 = a - Q * d
    assert 0 <= R0 < 3 * d, (a, d, R0)
    j = R0 // d
    return Q + j, R0 - j * d


if __name__ == "__main__":
    rng = random.Random(1)
    for n, b in ((8, 2), (9, 3), (10, 2), (12, 4)):
        pr = params(n, b)
        if pr["t"] > n:
            continue
        tab = table(pr)
        st = {}
        for a in range(1 << n):
            for d in range(1, 1 << n):
                assert divide(a, d, pr, tab, rng if (a ^ d) & 1 else None, st) == (a // d, a % d)
        print("exhaustive", n, b, pr, "max top", st["T"], "limit", 3 << b)
    pr = params(64, 8)
    tab = table(pr)
    st = {}
    for _ in range(200000):
        a = rng.getrandbits(rng.randrange(1, 65))
        d = rng.getrandbits(rng.randrange(1, 65)) or 1
        assert divide(a, d, pr, tab, rng, st) == (a // d, a % d)
    print("random 64/8", pr, "table", len(tab), "max top", st["T"], "limit", 3 << 8)
