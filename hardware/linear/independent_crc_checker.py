"""Independent check for colony.lut-crc.v1.  Shares no code with the generator.

Claim: for every e in 0 .. bytes-1 and every s, d with the last e bytes of d zero, the outputs are the CRC
register after shifting in the first 8 * (bytes - e) bits of d:  fb = s[width-1] ^ bit;  s' = (s << 1) ^ (fb ? poly : 0).

For each e the inputs e[] are fixed, the dead data bits are fixed to zero, and every wire is carried as a
GF(2) linear form (a bit mask) over s and the live data bits.  A LUT is accepted only if, once its constant
inputs are fixed, its table is the parity of a subset of the remaining inputs.  The output masks are compared
with the masks from running the recurrence on symbolic inputs.  Equal masks are equal functions.
"""
import argparse
import hashlib
import json
from pathlib import Path


def parse(raw):
    ins, outs, luts, cur = [], [], [], None
    for line in raw.decode("ascii").replace("\\\n", " ").splitlines():
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] == ".inputs":
            ins += t[1:]
        elif t[0] == ".outputs":
            outs += t[1:]
        elif t[0] == ".names":
            cur = (t[-1], t[1:-1], set())
            luts.append(cur)
        elif t[0] in (".model", ".end"):
            cur = None
        elif t[0].startswith("."):
            raise ValueError("unsupported construct " + t[0])
        else:
            if cur is None or len(t) != 2 or t[1] != "1" or len(t[0]) != len(cur[1]) or set(t[0]) - {"0", "1"}:
                raise ValueError("row format")
            cur[2].add(t[0])
    return ins, outs, luts


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-crc.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        poly, width, nbytes, k = cert["poly"], cert["width"], cert["bytes"], cert["k"]
        nbits = 8 * nbytes
        ebits = (nbytes - 1).bit_length() if nbytes > 1 else 0
        ins, outs, luts = parse(raw)
        want = ["s[%d]" % i for i in range(width)] + ["d[%d]" % i for i in range(nbits)] + ["e[%d]" % j for j in range(ebits)]
        if ins != want or outs != ["o[%d]" % i for i in range(width)]:
            return {"ok": False, "reason": "interface"}
        seen, level, count = set(ins), {v: 0 for v in ins}, 0
        for name, src, rows in luts:
            if name in seen or any(v not in seen for v in src) or len(src) > k or len(set(src)) != len(src):
                return {"ok": False, "reason": "netlist structure at " + name}
            seen.add(name)
            buf = name in outs and len(src) == 1 and rows == {"1"}
            level[name] = level[src[0]] if buf else 1 + max([level[v] for v in src] + [0])
            count += 0 if buf else 1
        if count != cert["lut_count"] or max(level[o] for o in outs) != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        for e in range(nbytes):
            live = 8 * (nbytes - e)
            const = {"e[%d]" % j: (e >> j) & 1 for j in range(ebits)}
            form = {"s[%d]" % i: 1 << i for i in range(width)}
            for i in range(nbits):
                if i < live:
                    form["d[%d]" % i] = 1 << (width + i)
                else:
                    const["d[%d]" % i] = 0
            for name, src, rows in luts:
                free = [q for q, v in enumerate(src) if v not in const]
                # a wire with form 0 is the constant zero as well
                fixed = {q: const[v] for q, v in enumerate(src) if v in const}
                table = {}
                for r in range(1 << len(free)):
                    bits = dict(fixed)
                    for t, q in enumerate(free):
                        bits[q] = (r >> t) & 1
                    table[r] = "".join(str(bits[q]) for q in range(len(src))) in rows
                if table[0]:
                    return {"ok": False, "reason": "constant term at %s for e = %d" % (name, e)}
                subset = [t for t in range(len(free)) if table[1 << t]]
                for r in range(1 << len(free)):
                    if table[r] != (sum((r >> t) & 1 for t in subset) & 1 == 1):
                        return {"ok": False, "reason": "%s is not linear for e = %d" % (name, e)}
                v = 0
                for t in subset:
                    v ^= form[src[free[t]]]
                form[name] = v
            state = [1 << i for i in range(width)]
            for t in range(live):
                fb = state[width - 1] ^ (1 << (width + t))
                state = [(state[i - 1] if i else 0) ^ (fb if (poly >> i) & 1 else 0) for i in range(width)]
            for i in range(width):
                if form["o[%d]" % i] != state[i]:
                    return {"ok": False, "reason": "output %d differs for e = %d" % (i, e)}
        return {"ok": True, "poly": hex(poly), "width": width, "bytes": nbytes, "lut_count": count, "levels": cert["levels"],
                "netlist_digest": cert["netlist_digest"], "proof": "GF(2) forms of the outputs equal the recurrence for every number of valid bytes"}
    except Exception as exc:
        return {"ok": False, "reason": "replay exception: " + type(exc).__name__ + ": " + str(exc)[:160]}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--netlist", type=Path, required=True)
    ap.add_argument("--derivation", type=Path, required=True)
    a = ap.parse_args()
    res = verify(a.netlist.read_bytes(), json.loads(a.derivation.read_text()))
    print(json.dumps(res, sort_keys=True))
    raise SystemExit(0 if res["ok"] else 1)
