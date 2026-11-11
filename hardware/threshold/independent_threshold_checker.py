"""Independent replay of a colony.lut-threshold.v1 derivation.

Shares no code with the compiler.  It parses the BLIF itself and proves
output = [popcount(A) >= T] for all 2^n inputs by integer bookkeeping:

  each node satisfies, for every row of its truth tables,
      sum(w_i * in_i) + add = r + sum(2^d * out_d),   0 <= r < 2^floor
  (checked exhaustively, at most 2^k rows).  Summing the node identities
  scaled by 2^unit gives  popcount + C = 2^u * X + R  with 0 <= R < 2^u,
  because each column below u contributes at most one residue.  The final
  node outputs [X >= 2^(m-u)], which is bit m of popcount + C = [popcount >= T].
"""
import argparse
import hashlib
import json
from pathlib import Path


def parse_blif(raw):
    text = raw.decode("ascii").replace("\\\n", " ")
    inputs, outputs, tables, cur = [], [], {}, None
    for line in text.splitlines():
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] == ".inputs":
            inputs += t[1:]
        elif t[0] == ".outputs":
            outputs += t[1:]
        elif t[0] == ".names":
            cur = t[-1]
            if cur in tables:
                raise ValueError("wire driven twice: " + cur)
            tables[cur] = (t[1:-1], set())
        elif t[0] in (".model", ".end"):
            cur = None if t[0] == ".end" else cur
        elif t[0].startswith("."):
            raise ValueError("unsupported BLIF construct " + t[0])
        else:
            if cur is None or len(t) != 2 or t[1] != "1" or len(t[0]) != len(tables[cur][0]) or set(t[0]) - {"0", "1"}:
                raise ValueError("only complete on-set minterm rows are accepted")
            tables[cur][1].add(t[0])
    return inputs, outputs, tables


def verify(raw, cert):
    try:
        if cert.get("schema") != "colony.lut-threshold.v1":
            return {"ok": False, "reason": "schema"}
        if cert.get("netlist_digest") != "sha256:" + hashlib.sha256(raw).hexdigest():
            return {"ok": False, "reason": "netlist digest"}
        n, T, k, m, C = (cert[x] for x in ("n", "threshold", "k", "result_column", "constant"))
        if not (1 <= T <= n) or C != (1 << m) - T or C < 0 or n + C >= (1 << (m + 1)):
            return {"ok": False, "reason": "threshold arithmetic"}
        inputs, outputs, tables = parse_blif(raw)
        if inputs != ["A[%d]" % i for i in range(n)] or len(set(inputs)) != n or outputs != ["maj"]:
            return {"ok": False, "reason": "interface"}
        column = {w: 0 for w in inputs}
        used, produced, residue_cols = set(), set(), {}
        add_total, final_unit, levels = 0, None, {w: 0 for w in inputs}
        for node in cert["nodes"]:
            unit, fl, add = node["unit"], node["floor"], node["add"]
            ins = [w for w, _ in node["in"]]
            wts = [w for _, w in node["in"]]
            if not ins or len(ins) > k or len(set(ins)) != len(ins) or add < 0:
                return {"ok": False, "reason": "node shape"}
            for w, wt in zip(ins, wts):
                if w not in column or w in used or wt < 1 or wt & (wt - 1) or column[w] != unit + wt.bit_length() - 1:
                    return {"ok": False, "reason": "input wire/column mismatch at " + w}
                used.add(w)
            is_final = bool(node.get("final"))
            if is_final:
                if len(node["out"]) != 1 or node["out"][0][1] != fl or unit + fl != m:
                    return {"ok": False, "reason": "final node shape"}
                if unit < m:
                    if final_unit is not None:
                        return {"ok": False, "reason": "two final nodes"}
                    final_unit = unit
                elif add:
                    return {"ok": False, "reason": "constant in result column"}
            else:
                if type(fl) is not int or fl < 0 or (fl == 0 and add) or add >= (1 << fl):
                    return {"ok": False, "reason": "floor/add"}
                if final_unit is not None:
                    return {"ok": False, "reason": "node after final"}
                for col in range(unit, unit + fl):
                    if col in residue_cols or col >= m:
                        return {"ok": False, "reason": "second residue in column %d" % col}
                    residue_cols[col] = "node"
            add_total += add << unit
            outs = node["out"]
            for o, d in outs:
                if o in column or o not in tables or tables[o][0] != ins:
                    return {"ok": False, "reason": "output wire " + o}
            digits = {d: o for o, d in outs}
            if len(digits) != len(outs):
                return {"ok": False, "reason": "duplicate digit"}
            for row in range(1 << len(ins)):
                bits = "".join("1" if (row >> i) & 1 else "0" for i in range(len(ins)))
                x = add + sum(wt for i, wt in enumerate(wts) if (row >> i) & 1)
                got = sum((1 << d) for d, o in digits.items() if bits in tables[o][1])
                if is_final:
                    if (got != 0) != (x >= (1 << fl)):
                        return {"ok": False, "reason": "final truth table"}
                    if unit == m and x > 1 and False:
                        pass
                else:
                    if x - got < 0 or x - got >= (1 << fl):
                        return {"ok": False, "reason": "counter identity fails"}
            for o, d in outs:
                column[o] = m if is_final else unit + d
                if column[o] > m + 8:
                    return {"ok": False, "reason": "overflow column"}
                produced.add(o)
                levels[o] = 1 + max(levels[w] for w in ins)
        if set(tables) != produced:
            return {"ok": False, "reason": "netlist has undeclared logic"}
        u = m if final_unit is None else final_unit
        for w, c in column.items():
            if w in used or w == "maj":
                continue
            if c >= u or c in residue_cols:
                return {"ok": False, "reason": "unaccounted wire " + w}
            residue_cols[c] = "dropped"
        missing = C - add_total
        if missing < 0:
            return {"ok": False, "reason": "constant"}
        for c in range(m + 1):
            if (missing >> c) & 1:
                if c >= u or c in residue_cols:
                    return {"ok": False, "reason": "constant bit unaccounted"}
                residue_cols[c] = "const"
        if missing >> (m + 1) or "maj" not in column or "maj" in used or column["maj"] != m:
            return {"ok": False, "reason": "result wire"}
        lut = len(tables)
        if lut != cert["lut_count"] or levels["maj"] != cert["levels"]:
            return {"ok": False, "reason": "declared cost differs"}
        return {"ok": True, "n": n, "threshold": T, "k": k, "lut_count": lut, "levels": levels["maj"],
                "max_fanin": max(len(v[0]) for v in tables.values()),
                "netlist_digest": cert["netlist_digest"], "proof": "exhaustive local identities + integer bookkeeping"}
    except Exception as exc:
        return {"ok": False, "reason": "replay exception: " + type(exc).__name__ + ": " + str(exc)[:160]}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--netlist", type=Path, required=True)
    p.add_argument("--derivation", type=Path, required=True)
    a = p.parse_args()
    res = verify(a.netlist.read_bytes(), json.loads(a.derivation.read_text()))
    print(json.dumps(res, sort_keys=True))
    raise SystemExit(0 if res["ok"] else 1)


if __name__ == "__main__":
    main()
