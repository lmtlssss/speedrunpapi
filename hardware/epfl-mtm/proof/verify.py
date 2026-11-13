#!/usr/bin/env python3
"""verify.py NAME ORIGINAL.aig NETLIST.blif

Proves that NETLIST.blif computes the same function as the EPFL original, without a solver.

The original
  A. sop multiplies ORIGINAL.aig out into a sum of products, exactly. For these three circuits each
     output (or its complement) is a sum of products that read only inputs 0..16 (x) and products
     that read only the other inputs (A, B), so the output is  X(x) OR Y(A,B)  with
       Y = the listed y products: a table of input points, each with a word of output bits
       X = read off by simulating all 131072 x at a (A,B) that is not in the table.
The netlist
  1. Every output LUT is p(fanins that depend only on x) OR q(fanins that depend only on A,B),
     so the netlist output is  X'(x) OR Y'(A,B)  as well.
  2. All 131072 x at the same (A,B): the netlist gives X.
  3. With x fixed outside the x table and the 18 index wires cut open, every one of their 2^18
     values is enumerated with A and B symbolic: wherever an output is on, (A,B) is a table point
     with that bit set. The netlist drives those wires from (A,B), so this covers it.
  4. At every table point the netlist gives the table word.
2 gives X' = X. 3 and 4 give Y' = Y.
"""
import os, re, struct, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
NX, NCUT, X0 = 17, 18, 131071
RULE_N = {"sixteen": 100000, "twenty": 90000, "twentythree": 94000}


def run(*a):
    r = subprocess.run([str(x) for x in a], capture_output=True, text=True)
    if r.returncode not in (0, 2):
        sys.exit(f"{a[0]} failed:\n{r.stdout}\n{r.stderr}")
    return r


def main():
    name, orig, blif = sys.argv[1], sys.argv[2], sys.argv[3]
    T = os.path.join(HERE, "tmp_" + name)
    ok = True

    # ---- A. the original as tables ---------------------------------------------------------
    run(os.path.join(HERE, "sop"), orig, T + "_sop.bin")
    f = open(T + "_sop.bin", "rb")
    assert f.read(4) == b"SOP1"
    I, O = struct.unpack("<II", f.read(8))
    n = (I - NX) // 2
    assert I == NX + 2 * n and O == n
    XM = (1 << NX) - 1
    YM = ((1 << I) - 1) ^ XM
    WM = (1 << n) - 1
    ytab, pols, nxp, nyp, npart, nmixed = {}, set(), 0, 0, 0, 0
    for o in range(O):
        pol, cnt = struct.unpack("<II", f.read(8))
        pols.add(pol)
        for r in struct.iter_unpack("<6Q", f.read(48 * cnt)):
            m = r[0] | (r[1] << 64) | (r[2] << 128)
            v = r[3] | (r[4] << 64) | (r[5] << 128)
            if m & ~XM == 0:
                nxp += 1
            elif m & XM:
                nmixed += 1
            else:
                nyp += 1
                free = [b for b in range(NX, I) if not (m >> b) & 1]
                if free:
                    npart += 1
                    assert len(free) <= 12
                for comb in range(1 << len(free)):
                    y = v
                    for z, b in enumerate(free):
                        y |= ((comb >> z) & 1) << b
                    y >>= NX
                    key = (y & WM, y >> n)
                    ytab[key] = ytab.get(key, 0) | (1 << o)
    assert len(pols) == 1 and nmixed == 0, "the original is not X(x) OR Y(A,B)"
    pol = pols.pop()
    assert (WM, WM) not in ytab
    print(f"{name}: original = {'NOT ' if pol else ''}( X(x) OR Y(A,B) ); {nxp} x products, {nyp} y products ({npart} not a single point), {len(ytab)} table points")

    def xtable(aig, tag):
        run(os.path.join(HERE, "xsim"), aig, NX, T + tag)
        d = open(T + tag, "rb").read()
        nb = len(d) // (8 * O)
        xt = [0] * (nb * 64)
        words = struct.unpack(f"<{nb * O}Q", d)
        for b in range(nb):
            for o in range(O):
                wv = words[b * O + o]
                if pol:
                    wv ^= (1 << 64) - 1
                base = 64 * b
                while wv:
                    lb = wv & -wv
                    xt[base + lb.bit_length() - 1] |= 1 << o
                    wv ^= lb
        return xt

    xtab = xtable(orig, "_xo.bin")

    N = RULE_N.get(name)
    if N:
        M64 = (1 << 64) - 1
        F = {-1: 1, 0: 0}
        for i in range(1, N + 2):
            F[i] = (F[i - 1] + F[i - 2]) & M64
        s = lambda v: v if v < (1 << 63) else 0
        rx = [(s(F[x]) & WM) if x <= N - 2 else 0 for x in range(1 << NX)]
        ry = {}
        for i in range(0, N - 2):
            p = s(F[i + 1]) & WM
            if p:
                k = (s(F[i]) & WM, s(F[i - 1]) & WM)
                ry[k] = ry.get(k, 0) | p
        print(f"   the Fibonacci rule (N = {N}, n = {n}) gives the same two tables: {rx == xtab and ry == ytab}")

    # ---- 1. form of the output LUTs ------------------------------------------------------
    txt = open(blif).read()
    ins = re.search(r"(?m)^\.inputs (.*)$", txt).group(1).split()
    outs = re.search(r"(?m)^\.outputs (.*)$", txt).group(1).split()
    assert len(ins) == I and len(outs) == O
    cls = {nm: (1 if i < NX else 2) for i, nm in enumerate(ins)}
    lut = {}
    blocks = re.split(r"(?m)^(?=\.names )", txt)
    for blk in blocks[1:]:
        lines = blk.split(".end")[0].strip().split("\n")
        names = lines[0].split()[1:]
        fan, out = names[:-1], names[-1]
        k = len(fan)
        tt = 0
        for ln in lines[1:]:
            ln = ln.split()
            if not ln:
                continue
            pat = ln[0] if len(ln) == 2 else ""
            for m in range(1 << k):
                if all(ch == "-" or int(ch) == (m >> j) & 1 for j, ch in enumerate(pat)):
                    tt |= 1 << m
        c = 0
        for u in fan:
            c |= cls[u]
        cls[out] = c
        lut[out] = (fan, tt)
    nlut = sum(1 for fan, tt in lut.values() if fan)
    ncon = sum(1 for fan, tt in lut.values() if not fan)
    bad = const = 0
    for o in outs:
        fan, tt = lut[o]
        k = len(fan)
        if k == 0:
            const += 1
            continue
        if any(cls[u] == 3 for u in fan):
            bad += 1
            continue
        xm = sum(1 << j for j in range(k) if cls[fan[j]] != 2)
        ym = sum(1 << j for j in range(k) if cls[fan[j]] == 2)
        fn = lambda m: ((tt >> m) & 1) ^ pol
        off = [m for m in range(1 << k) if not fn(m)]
        if not off or not all(fn(m) == (fn((m & xm) | (off[0] & ym)) | fn((off[0] & xm) | (m & ym))) for m in range(1 << k)):
            bad += 1
    print(f"   netlist: {nlut} LUTs" + (f" and {ncon} constant outputs" if ncon else ""))
    print(f"1. output LUTs of the form p(x side) OR q(y side): {O - bad - const} of {O}, {const} constant")
    ok &= bad == 0

    # ---- 2. the x table ------------------------------------------------------------------
    py = sys.executable
    run(py, os.path.join(HERE, "blif2aig.py"), blif, T + "_full.aig", 0, 0, 0)
    e2 = xtable(T + "_full.aig", "_xn.bin") == xtab
    print(f"2. all {1 << NX} x patterns equal the original: {e2}")
    ok &= e2

    # ---- 3. on only at table points ------------------------------------------------------
    cut = [f"cut_t{i}" for i in range(14)] + [f"cut_r{i}" for i in range(4)]
    kept = [b for b in blocks[1:] if b.split("\n")[0].split()[-1] not in cut]
    ncut = len(blocks) - 1 - len(kept)
    assert ncut in (0, NCUT)                 # a table-form netlist has no index wires: one case, nothing cut
    head = re.sub(r"(?m)^(\.inputs .*)$", lambda mm: mm.group(1) + (" " + " ".join(cut) if ncut else ""), blocks[0])
    open(T + "_cut.blif", "w").write(head + "".join(kept))
    run(py, os.path.join(HERE, "blif2aig.py"), T + "_cut.blif", T + "_cut.aig", NX, 2 * n, pol)
    M = (1 << 64) - 1
    with open(T + "_pts.bin", "wb") as g:
        for (a, b), wv in ytab.items():
            g.write(struct.pack("<6Q", a & M, a >> 64, b & M, b >> 64, wv & M, wv >> 64))
    r = run(os.path.join(HERE, "cutprove"), T + "_cut.aig", NX, n, ncut, X0, 0, T + "_pts.bin")
    print("3. " + "; ".join(r.stdout.strip().splitlines()) + (" " + r.stderr.strip()[:300] if r.stderr.strip() else ""))
    ok &= r.returncode == 0

    # ---- 4. the table word at every table point ------------------------------------------
    pts = list(ytab.items())
    with open(T + "_pat.txt", "w") as g:
        for (a, b), wv in pts:
            g.write(format(X0 | (a << NX) | (b << (NX + n)), "x") + "\n")
    run(os.path.join(HERE, "psim"), T + "_full.aig", T + "_pat.txt", T + "_out.txt")
    got = [int(l, 16) for l in open(T + "_out.txt").read().split()]
    full = (1 << n) - 1
    same = sum(1 for (k, wv), g in zip(pts, got) if g == (wv ^ (full if pol else 0)))
    assert xtab[X0] == 0
    print(f"4. table word at the table points: {same} of {len(pts)} equal")
    ok &= same == len(pts) == len(got)
    print("RESULT:", "equivalent to the original" if ok else "NOT PROVEN")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
