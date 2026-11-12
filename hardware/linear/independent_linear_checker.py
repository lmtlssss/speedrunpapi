"""Independent check for colony.lut-linear.v1.  Shares no code with the compiler.

Claim (kind crc): the netlist maps (s, d) to the CRC register after shifting in d[0], d[1], ... d[data-1],
for the register recurrence  fb = s[width-1] ^ d;  s' = (s << 1) ^ (fb ? poly : 0).
Claim (kind matrix): output y[i] is the XOR of the inputs x[j] named by row i of the derivation.

Every LUT must be the parity of its inputs.  Each wire then carries one GF(2) linear form over the inputs,
held as a bit mask; the masks of the outputs are compared with the masks obtained by running the recurrence
on symbolic inputs.  Two linear forms with equal masks are equal on every input.
"""
import argparse
import hashlib
import json
from pathlib import Path


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-linear.v1" or cert.get("kind") not in ("crc", "matrix"):
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        k = cert["k"]
        if cert["kind"] == "matrix":
            target = [int(t, 16) for t in cert["rows"]]
            want_in = ["x[%d]" % i for i in range(cert["inputs"])]
            want_out = ["y[%d]" % i for i in range(len(target))]
            if any(m >> len(want_in) for m in target):
                return {"ok": False, "reason": "row reads past the inputs"}
        else:
            poly, width, data = cert["poly"], cert["width"], cert["data"]
            want_in = ["s[%d]" % i for i in range(width)] + ["d[%d]" % i for i in range(data)]
            want_out = ["o[%d]" % i for i in range(width)]
        form = {name: 1 << i for i, name in enumerate(want_in)}
        level = {name: 0 for name in want_in}
        ins, outs, cur, luts = [], [], None, 0
        pending = None

        def close():
            nonlocal pending, luts
            if pending is None:
                return None
            name, src, rows = pending
            pending = None
            if name in form:
                return "wire driven twice: " + name
            if any(v not in form for v in src):
                return "netlist order at " + name
            n = len(src)
            if n == 0:
                if rows:
                    return "constant one at " + name
                form[name], level[name] = 0, 0
                return None
            if n == 1 and rows == {"1"}:                      # output buffer
                form[name], level[name] = form[src[0]], level[src[0]]
                return None
            if n > k or len(set(src)) != n:
                return "fan-in at " + name
            if rows != {format(r, "0%db" % n) for r in range(1 << n) if bin(r).count("1") & 1}:
                return "not a parity LUT: " + name
            v = 0
            for s_ in src:
                v ^= form[s_]
            form[name], level[name] = v, 1 + max(level[s_] for s_ in src)
            luts += 1
            return None
        for line in raw.decode("ascii").replace("\\\n", " ").splitlines():
            t = line.split()
            if not t or t[0].startswith("#"):
                continue
            if t[0] == ".inputs":
                ins += t[1:]
            elif t[0] == ".outputs":
                outs += t[1:]
            elif t[0] == ".names":
                err = close()
                if err:
                    return {"ok": False, "reason": err}
                pending = (t[-1], t[1:-1], set())
            elif t[0] in (".model", ".end"):
                err = close()
                if err:
                    return {"ok": False, "reason": err}
            elif t[0].startswith("."):
                return {"ok": False, "reason": "unsupported construct " + t[0]}
            else:
                if pending is None or len(t) != 2 or t[1] != "1" or len(t[0]) != len(pending[1]) or set(t[0]) - {"0", "1"}:
                    return {"ok": False, "reason": "row format"}
                pending[2].add(t[0])
        if ins != want_in or outs != want_out:
            return {"ok": False, "reason": "interface"}
        if cert["kind"] == "matrix":
            state = target
        else:
            state = [1 << i for i in range(width)]            # the recurrence on symbolic inputs
            for t in range(data):
                fb = state[width - 1] ^ (1 << (width + t))
                state = [(state[i - 1] if i else 0) ^ (fb if (poly >> i) & 1 else 0) for i in range(width)]
        for i, name in enumerate(want_out):
            if name not in form or form[name] != state[i]:
                return {"ok": False, "reason": "output %d differs" % i}
        lev = max(level[o] for o in want_out)
        if luts != cert["lut_count"] or lev != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "kind": cert["kind"], "outputs": len(want_out), "inputs": len(want_in), "lut_count": luts, "levels": lev,
                "netlist_digest": cert["netlist_digest"], "proof": "parity LUTs; GF(2) forms of the outputs equal the claim"}
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
