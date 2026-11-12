"""Linear-map compiler: y = M x over GF(2) as a network of k-input XOR LUTs.

Contract: output i is the XOR of the inputs in row i of M.
Method: a set of signals that occurs in several rows is built once.  The set is grown from the most frequent
pair, one signal at a time, while (size - 1) * (rows containing it) grows; it becomes one LUT and replaces
itself in those rows.  When nothing is shared any more each row is closed with a tree, earliest signals first.
`depth` limits the LUT levels: shared sets are then taken only from signals below a level cap.
"""
import argparse
import hashlib
import json
from pathlib import Path

try:
    (0).bit_count
    pc = int.bit_count
except AttributeError:                                       # Python < 3.10
    pc = lambda v: bin(v).count("1")


def build(rows, nin, k=6, cap=10 ** 9, tries=24, guard=False):
    """rows: list of int masks over the inputs.  Returns (nodes, outs, levels): nodes[j] = fan-in ids of
    signal nin + j; outs[i] = signal id of row i, or None for a zero row."""
    import heapq
    nrows = len(rows)
    col, members = {}, [set() for _ in range(nrows)]         # signal -> row mask; row -> signals
    for i, m in enumerate(rows):
        v = 0
        while m:
            if m & 1:
                col[v] = col.get(v, 0) | (1 << i)
                members[i].add(v)
            m >>= 1
            v += 1
    level = {v: 0 for v in col}
    nodes = []
    heap = []
    sig = sorted(col)
    for ai, a in enumerate(sig):
        ca = col[a]
        for b in sig[ai + 1:]:
            f = pc(ca & col[b])
            if f >= 2:
                heap.append((-f, a, b))
    heapq.heapify(heap)

    def rows_of(mask):
        out, i = [], 0
        while mask:
            low = mask & -mask
            out.append(low.bit_length() - 1)
            mask ^= low
        return out
    skip = set()
    while heap:
        cands, seen = [], set()
        while heap and len(cands) < tries:                    # the best pairs whose counts are current
            f, a, b = heapq.heappop(heap)
            if (a, b) in seen or (a, b) in skip:
                continue
            if a not in col or b not in col or level[a] >= cap or level[b] >= cap:
                continue
            now = pc(col[a] & col[b])
            if now < 2:
                continue
            if now != -f:
                heapq.heappush(heap, (-now, a, b))
                continue
            if cands and now < max(2, cands[0][0] - 3):
                heapq.heappush(heap, (f, a, b))
                break
            seen.add((a, b))
            cands.append((now, a, b))
        if not cands:
            break
        pick = None
        for f0, a, b in cands:
            g, rm, score = [a, b], col[a] & col[b], f0
            while len(g) < k:
                cnt = {}
                for i in rows_of(rm):
                    for v in members[i]:
                        cnt[v] = cnt.get(v, 0) + 1
                ext = (0, None)
                for v, f in cnt.items():
                    if v not in g and level[v] < cap and (f > ext[0] or (f == ext[0] and ext[1] is not None and v < ext[1])):
                        ext = (f, v)
                if ext[1] is None or ext[0] < 2 or ext[0] * len(g) <= score:
                    break
                g.append(ext[1])
                rm &= col[ext[1]]
                score = ext[0] * (len(g) - 1)
            if pick is None or score > pick[0]:
                pick = (score, g, rm)
        score, g, rm = pick
        if guard:                                             # keep the set only if it saves LUTs in its rows now
            need = lambda n: 0 if n <= 1 else -(-(n - 1) // (k - 1))
            saved = sum(need(len(members[i])) - need(len(members[i]) - len(g) + 1) for i in rows_of(rm))
            if saved <= 1:
                skip.add(tuple(sorted(g[:2])))
                for f0, a, b in cands:
                    if tuple(sorted((a, b))) not in skip:
                        heapq.heappush(heap, (-f0, a, b))
                continue
        for f0, a, b in cands:                                # return the candidates; stale counts are fixed on pop
            heapq.heappush(heap, (-f0, a, b))
        nid = nin + len(nodes)
        nodes.append(tuple(sorted(g)))
        level[nid] = 1 + max(level[v] for v in g)
        touched = rows_of(rm)
        for v in g:
            col[v] &= ~rm
            if not col[v]:
                del col[v]
        col[nid] = rm
        cnt = {}
        for i in touched:
            members[i].difference_update(g)
            for v in members[i]:
                cnt[v] = cnt.get(v, 0) + 1
            members[i].add(nid)
        for v, f in cnt.items():                              # pairs of the new signal
            if f >= 2:
                heapq.heappush(heap, (-f, v, nid))
    build.shared = len(nodes)                                 # nodes built before the rows are closed
    outs = []
    for i in range(nrows):
        cur = sorted(members[i], key=lambda v: (level[v], v))
        while len(cur) > 1:
            take, cur = cur[:k], cur[k:]
            nid = nin + len(nodes)
            nodes.append(tuple(take))
            level[nid] = 1 + max(level[v] for v in take)
            cur.append(nid)
            cur.sort(key=lambda v: (level[v], v))
        outs.append(cur[0] if cur else None)
    return nodes, outs, max([level[o] for o in outs if o is not None] + [0])


def compile_linear(rows, nin, k=6, depth=None, effort=(24, 60, 150)):
    """Smallest network over the candidate counts in `effort` and, with a depth limit, over the level caps."""
    best = None
    caps = [10 ** 9] if depth is None else list(range(depth, 0, -1))
    for cap in caps:
        for tries in effort:
            for guard in (False, True):
                res = build(rows, nin, k, cap, tries, guard)
                if depth is not None and res[2] > depth:
                    continue
                if best is None or (len(res[0]), res[2]) < (len(best[0]), best[2]):
                    best = res
    if best is None:
        raise ValueError("depth %d cannot be met" % depth)
    return best


def crc_rows(poly, width, nbits):
    """Next state of a width-bit CRC register after nbits data bits, first bit d[0], as masks over
    (state bits, then data bits)."""
    rows = [1 << i for i in range(width)]
    for t in range(nbits):
        fb = rows[width - 1] ^ (1 << (width + t))
        rows = [(rows[i - 1] if i else 0) ^ (fb if (poly >> i) & 1 else 0) for i in range(width)]
    return rows


def blif(nodes, outs, in_names, out_names, model="linear"):
    nin = len(in_names)
    nm = lambda v: in_names[v] if v < nin else "n%d" % (v - nin)
    L = [".model " + model, ".inputs " + " ".join(in_names), ".outputs " + " ".join(out_names)]
    for j, ins in enumerate(nodes):
        L.append(".names " + " ".join(nm(v) for v in ins) + " n%d" % j)
        for r in range(1 << len(ins)):
            if pc(r) & 1:
                L.append("".join("1" if (r >> q) & 1 else "0" for q in range(len(ins))) + " 1")
    for o, name in zip(outs, out_names):
        L.append(".names " + name if o is None else ".names %s %s\n1 1" % (nm(o), name))
    return ("\n".join(L) + "\n.end\n").encode()


def verilog(nodes, outs, in_names, out_names, module):
    nin = len(in_names)
    nm = lambda v: in_names[v] if v < nin else "n%d" % (v - nin)
    L = ["module %s (%s, %s);" % (module, ", ".join("input " + v for v in in_names), ", ".join("output " + v for v in out_names))]
    for j, ins in enumerate(nodes):
        L.append("  (* keep *) wire n%d = %s;" % (j, " ^ ".join(nm(v) for v in ins)))
    for o, name in zip(outs, out_names):
        L.append("  assign %s = %s;" % (name, "1'b0" if o is None else nm(o)))
    L.append("endmodule")
    return "\n".join(L) + "\n"


def primitives(nodes, outs, in_names, out_names, module, family):
    """LUT instances, so synthesis keeps the network as built.  family: xilinx (LUT1..LUT6) or ecp5 (LUT4)."""
    nin = len(in_names)
    nm = lambda v: in_names[v] if v < nin else "n%d" % (v - nin)
    L = ["module %s (%s, %s);" % (module, ", ".join("input " + v for v in in_names), ", ".join("output " + v for v in out_names))]
    for j, ins in enumerate(nodes):
        n = len(ins)
        if family == "xilinx":
            init = sum(1 << r for r in range(1 << n) if pc(r) & 1)
            L.append("  wire n%d; LUT%d #(.INIT(%d'h%x)) u%d (.O(n%d), %s);" % (j, n, 1 << n, init, j, j, ", ".join(".I%d(%s)" % (q, nm(v)) for q, v in enumerate(ins))))
        else:
            assert n <= 4
            init = sum(1 << r for r in range(16) if pc(r & ((1 << n) - 1)) & 1)
            pins = [nm(v) for v in ins] + ["1'b0"] * (4 - n)
            L.append("  wire n%d; LUT4 #(.INIT(16'h%04x)) u%d (.Z(n%d), .A(%s), .B(%s), .C(%s), .D(%s));" % ((j, init, j, j) + tuple(pins)))
    for o, name in zip(outs, out_names):
        L.append("  assign %s = %s;" % (name, "1'b0" if o is None else nm(o)))
    L.append("endmodule")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix", type=Path, help="one row per line, as a hex mask over the inputs x[0..]")
    ap.add_argument("--inputs", type=int, help="number of inputs, with --matrix")
    ap.add_argument("--crc", default="0x04C11DB7")
    ap.add_argument("--width", type=int, default=32)
    ap.add_argument("--data", type=int)
    ap.add_argument("--k", type=int, default=6)
    ap.add_argument("--depth", type=int)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    if a.matrix:
        rows = [int(t, 16) for t in a.matrix.read_text().split()]
        nin = a.inputs or max(m.bit_length() for m in rows)
        ins = ["x[%d]" % i for i in range(nin)]
        ons = ["y[%d]" % i for i in range(len(rows))]
        cert = {"schema": "colony.lut-linear.v1", "kind": "matrix", "inputs": nin, "rows": ["%x" % m for m in rows]}
        name = "linear"
    else:
        poly = int(a.crc, 0)
        rows = crc_rows(poly, a.width, a.data)
        nin = a.width + a.data
        ins = ["s[%d]" % i for i in range(a.width)] + ["d[%d]" % i for i in range(a.data)]
        ons = ["o[%d]" % i for i in range(a.width)]
        cert = {"schema": "colony.lut-linear.v1", "kind": "crc", "poly": poly, "width": a.width, "data": a.data}
        name = "crc"
    nodes, outs, lev = compile_linear(rows, nin, a.k, a.depth)
    data = blif(nodes, outs, ins, ons, name)
    if a.out:
        a.out.mkdir(parents=True, exist_ok=True)
        (a.out / (name + ".blif")).write_bytes(data)
        cert.update(k=a.k, lut_count=len(nodes), levels=lev, netlist_digest="sha256:" + hashlib.sha256(data).hexdigest())
        (a.out / (name + ".json")).write_text(json.dumps(cert, sort_keys=True) + "\n")
    print(json.dumps({"rows": len(rows), "inputs": nin, "k": a.k, "lut_count": len(nodes), "levels": lev, "terms": sum(pc(m) for m in rows)}))
