"""Independent proof replay for colony.lut-mul-depth.v1 (depth builds of the multiplier and the squarer).

Claim: sum 2^c out[c] = a*b (or a*a).

The derivation names the LUTs of the counter heap and the two rows the heap ends in.
  1. Heap: the polynomial of sum 2^c (row atoms in column c), rebuilt from the netlist by replacing every
     heap LUT with its truth-table polynomial (coefficients mod 2^width), must equal a*b expanded over the
     input bits.  So rows U, V satisfy U + V = a*b (mod 2^width) on every input.
  2. Adder: the remaining LUTs, with the row wires as free inputs, are proved equal to a ripple adder of
     the same two rows by ABC `cec`.  So out = U + V (mod 2^width) for every value of the row wires.
a*b < 2^width, so out = a*b.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

from independent_mul_checker import parse_blif, lut_poly, atom_poly, BitPoly


def write_blif(path, ins, outs, luts):
    L = [".model m", ".inputs " + " ".join(ins), ".outputs " + " ".join(outs)]
    for o, vs, rows in luts:
        if not rows:
            L.append(".names " + o)                        # constant 0
            continue
        L.append(".names " + " ".join(vs + [o]))
        L += [r + " 1" if vs else "1" for r in rows]
    L.append(".end")
    open(path, "w").write("\n".join(L) + "\n")


def verify(raw, cert, abc="yosys-abc"):
    try:
        if cert.get("schema") != "colony.lut-mul-depth.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        n, square, width = cert["n"], bool(cert["square"]), cert["width"]
        if width != 2 * n:
            return {"ok": False, "reason": "width"}
        inputs, outputs, tables = parse_blif(raw)
        oname = "asquared" if square else "f"
        if inputs != ["a[%d]" % i for i in range(n)] + ([] if square else ["b[%d]" % i for i in range(n)]) or \
                outputs != ["%s[%d]" % (oname, c) for c in range(width)]:
            return {"ok": False, "reason": "interface"}
        heap, rows = cert["heap"], cert["rows"]
        if len(set(heap)) != len(heap) or any(h not in tables for h in heap) or len(rows) != width or any(len(r) > 2 for r in rows):
            return {"ok": False, "reason": "heap or rows"}
        mod = 1 << width
        r = BitPoly(mod)
        for c, atoms in enumerate(rows):
            for a in atoms:
                for mono, k in atom_poly(a).items():
                    r.add(mono, k << c)
        for name in reversed(heap):
            r.substitute(name, lut_poly(*tables[name]))
            if len(r.terms) > 64 * (len(heap) + width * width):
                return {"ok": False, "reason": "heap polynomial does not close"}
        expect = {}
        for i in range(n):
            for j in range(n):
                mono = frozenset(["a[%d]" % i, ("a[%d]" if square else "b[%d]") % j])
                expect[mono] = (expect.get(mono, 0) + (1 << (i + j))) % mod
        expect = {m: k for m, k in expect.items() if k}
        if r.terms != expect:
            return {"ok": False, "reason": "rows do not sum to the product"}
        heapset = set(heap)
        adder = [o for o in tables if o not in heapset]
        row_wires = []
        for atoms in rows:
            for a in atoms:
                if a != 1:
                    w = a.lstrip("!")
                    if w not in heapset and w not in inputs:
                        return {"ok": False, "reason": "row wire is not heap logic"}
                    if w not in row_wires:
                        row_wires.append(w)
        for o in adder:                                    # the adder may read only row wires and adder wires
            for v in tables[o][0]:
                if v not in row_wires and v not in adder:
                    return {"ok": False, "reason": "adder reads a wire outside the rows: " + v}
        safe = lambda v: re.sub(r"[\[\]]", "_", v)
        tmp = tempfile.mkdtemp(prefix="depthchk_")
        ins = [safe(w) for w in row_wires]
        ours = [(safe(o), [safe(v) for v in tables[o][0]], sorted(tables[o][1])) for o in adder]
        write_blif(os.path.join(tmp, "ours.blif"), ins, [safe(o) for o in outputs], ours)
        ref, carry = [], None
        for c, atoms in enumerate(rows):
            vs = [a.lstrip("!") for a in atoms if a != 1]
            allv = [safe(v) for v in vs] + ([carry] if carry else [])
            srows, crows = [], []
            for bits in range(1 << len(allv)):
                env = {v: (bits >> t) & 1 for t, v in enumerate(allv)}
                tot = (env[carry] if carry else 0)
                for a in atoms:
                    tot += 1 if a == 1 else (1 - env[safe(a[1:])] if a.startswith("!") else env[safe(a)])
                key = "".join("1" if env[v] else "0" for v in allv)
                if tot & 1:
                    srows.append(key)
                if tot >> 1:
                    crows.append(key)
            ref.append((safe(outputs[c]), allv, srows))
            nc = "rc%d" % c
            ref.append((nc, allv, crows))
            carry = nc
        write_blif(os.path.join(tmp, "ref.blif"), ins, [safe(o) for o in outputs], ref)
        p = subprocess.run([abc, "-c", "cec -n %s/ours.blif %s/ref.blif" % (tmp, tmp)], capture_output=True, text=True, timeout=3000)
        if "Networks are equivalent" not in p.stdout:
            return {"ok": False, "reason": "adder not proved equal to the ripple adder"}
        lev = {v: 0 for v in inputs}
        for o, (vs, _) in tables.items():
            if any(v not in lev for v in vs):
                return {"ok": False, "reason": "netlist order"}
            lev[o] = 1 + max([lev[v] for v in vs] + [0])
        if len(tables) != cert["lut_count"] or max(lev.values()) != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "n": n, "square": square, "lut_count": len(tables), "levels": max(lev.values()),
                "netlist_digest": cert["netlist_digest"],
                "proof": "heap polynomial identity mod 2^width from the netlist + ABC cec of the final adder against a ripple adder"}
    except Exception as exc:
        return {"ok": False, "reason": "replay exception: " + type(exc).__name__ + ": " + str(exc)[:160]}


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--netlist", type=Path, required=True)
    p.add_argument("--derivation", type=Path, required=True)
    p.add_argument("--abc", default="yosys-abc")
    a = p.parse_args()
    res = verify(a.netlist.read_bytes(), json.loads(a.derivation.read_text()), a.abc)
    print(json.dumps(res, sort_keys=True))
    raise SystemExit(0 if res["ok"] else 1)
