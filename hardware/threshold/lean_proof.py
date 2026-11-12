"""Emit a Lean 4 proof that a threshold netlist equals [popcount >= T] for every input.

Input: BLIF netlist and its colony.lut-threshold.v1 derivation.  Output: one self-contained .lean file
(core Lean only, no Mathlib).  The Lean kernel, not Colony code, is the judge:
  - each LUT is a definition by its truth-table constant;
  - each node identity is a lemma proved by exhaustive case split on its Boolean inputs;
  - node identities are summed in chunks by `omega`; the final theorem is
        theorem correct (x : Nat -> Bool) : maj x = decide (popcount x n >= T).
"""
import argparse
import json
from pathlib import Path

PRELUDE = '''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def lut (t i : Nat) : Bool := t.testBit i
def popcount (x : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => popcount x n + (x n).toNat
theorem popcount_le (x : Nat → Bool) : ∀ n, popcount x n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
      have h := popcount_le x n
      have b : (x n).toNat ≤ 1 := Bool.toNat_le _
      show popcount x n + (x n).toNat ≤ n + 1
      omega
def pc (x : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pc x a n + (x (a + n)).toNat
theorem pc_add (x : Nat → Bool) (a m : Nat) : ∀ n, pc x a (m + n) = pc x a m + pc x (a + m) n
  | 0 => rfl
  | n + 1 => by
      have ih := pc_add x a m n
      show pc x a (m + n) + (x (a + (m + n))).toNat = pc x a m + (pc x (a + m) n + (x (a + m + n)).toNat)
      rw [ih, Nat.add_assoc, Nat.add_assoc]
theorem popcount_eq_pc (x : Nat → Bool) : ∀ n, popcount x n = pc x 0 n
  | 0 => rfl
  | n + 1 => by
      have ih := popcount_eq_pc x n
      show popcount x n + (x n).toNat = pc x 0 n + (x (0 + n)).toNat
      rw [ih, Nat.zero_add]
theorem add_eq {a b c d : Nat} (h1 : a = b) (h2 : c = d) : a + c = b + d := by subst h1; subst h2; rfl
theorem of_iff (o : Bool) (p : Prop) [Decidable p] (h : o.toNat = 1 ↔ p) : o = decide p := by
  cases o <;> simp_all
theorem to_iff (o : Bool) (p : Prop) [Decidable p] (h : o = decide p) : o.toNat = 1 ↔ p := by
  subst h; by_cases hp : p <;> simp [hp]
'''


def parse_blif(raw):
    text = raw.decode().replace("\\\n", " ")
    tabs, cur = {}, None
    for line in text.splitlines():
        t = line.split()
        if not t or t[0] in (".model", ".end", ".inputs", ".outputs"):
            continue
        if t[0] == ".names":
            cur = t[-1]
            tabs[cur] = (t[1:-1], 0)
        else:
            fan, tt = tabs[cur]
            tabs[cur] = (fan, tt | (1 << sum(1 << i for i, ch in enumerate(t[0]) if ch == "1")))
    return tabs


def ref(w):
    if w.startswith("A["):
        return "(x %s)" % w[2:-1]
    return "(w_%s x)" % w


def term(pairs):
    """pairs: list of (coefficient, lean-expression)."""
    parts = [("%d * %s" % (c, e) if c != 1 else e) for c, e in pairs]
    return " + ".join(parts) if parts else "0"


def emit(raw, cert, chunk=12):
    n, T, m, C = cert["n"], cert["threshold"], cert["result_column"], cert["constant"]
    tabs = parse_blif(raw)
    nodes = cert["nodes"]
    trace = cert.get("tree_trace")
    L = [PRELUDE]
    generic = {}
    letters = "abcdef"

    def idx(args):
        return term([(1 << i, "%s.toNat" % a) for i, a in enumerate(args)])

    bundles = []

    def in_terms(e):
        """Raw inputs of a node equation, or the opaque bundle of a merged one."""
        if e.get("bundle"):
            return [(1, "%s x" % e["bundle"])]
        return [(1, "%s.toNat" % ref(w)) for w in e.get("raw", [])]

    def sides(e, extra=()):
        lp = in_terms(e) + [(1 << c, "%s.toNat" % ref(w)) for w, c in e["cons"].items()] + [(1, str(v)) for v in e["adds"]]
        rp = [(1 << c, "%s.toNat" % ref(w)) for w, c in e["prod"].items()] + [(1 << u, "%s x" % r) for u, r in e["res"]]
        ex = [(1 << c, "%s.toNat" % ref(w)) for w, c in extra]
        return lp, rp, ex

    def scaled(e):
        lp, rp, _ = sides(e)
        return term(lp), term(rp)

    def merge(group, name):
        cons, prod, adds, res, inner, ins_all = {}, {}, [], [], [], []
        for e in group:
            ins_all += in_terms(e)
            for w, c in e["cons"].items():
                if w in prod:
                    del prod[w]
                    inner.append((w, c))
                else:
                    cons[w] = c
            prod.update(e["prod"])
            adds += e["adds"]
            res += e["res"]
        out = {"cons": cons, "prod": prod, "adds": adds, "res": res, "lem": name, "bundle": None}
        unfold = ""
        if ins_all:
            out["bundle"] = "I_%s" % name
            bundles.append(out["bundle"])
            L.append("def %s (x : Nat → Bool) : Nat := %s" % (out["bundle"], term(ins_all)))
            unfold = "unfold %s; " % out["bundle"]
        lp, rp, ex = sides(out, inner)
        assert lp and rp
        P = ["theorem %s (x : Nat → Bool) : %s = %s := by" % (name, term(lp), term(rp))]
        acc = "(%s x)" % group[0]["lem"]
        suml, sumr = ["(%s)" % t for t in scaled(group[0])]
        for e in group[1:]:
            acc = "(add_eq %s (%s x))" % (acc, e["lem"])
            l, r = scaled(e)
            suml, sumr = "(%s + (%s))" % (suml, l), "(%s + (%s))" % (sumr, r)
        P.append("  have hs : %s = %s := %s" % (suml, sumr, acc))
        if ex:
            P.append("  have e1 : %s = (%s) + (%s) := by %sac_rfl" % (suml, term(lp), term(ex), unfold))
            P.append("  have e2 : %s = (%s) + (%s) := by ac_rfl" % (sumr, term(rp), term(ex)))
            P.append("  exact Nat.add_right_cancel (e1.symm.trans (hs.trans e2))")
        else:
            P.append("  have e1 : %s = %s := by %sac_rfl" % (suml, term(lp), unfold))
            P.append("  have e2 : %s = %s := by ac_rfl" % (sumr, term(rp)))
            P.append("  exact e1.symm.trans (hs.trans e2)")
        L.append("\n".join(P))
        return out

    column = {"A[%d]" % i: 0 for i in range(n)}
    consumed_inputs = set()
    eqs = []                      # per node: (consumed {wire:col}, produced {wire:col}, add_scaled, residue name or None, lemma name)
    finals = []
    for k, nd in enumerate(nodes):
        ins = [w for w, _ in nd["in"]]
        wts = [w for _, w in nd["in"]]
        outs = nd["out"]
        add, unit, fl = nd["add"], nd["unit"], nd["floor"]
        tts = [tabs[o][1] for o, _ in outs]
        for o, _ in outs:
            assert tabs[o][0] == ins
        key = (tuple(wts), add, fl, tuple(d for _, d in outs), tuple(tts), bool(nd.get("final")))
        K = len(ins)
        args = list(letters[:K])
        insum = term([(w, "%s.toNat" % a) for w, a in zip(wts, args)] + ([(1, str(add))] if add else []))
        if key not in generic:
            g = "g%d" % len(generic)
            generic[key] = g
            binder = "(%s : Bool)" % " ".join(args)
            cases = " <;> ".join("cases %s" % a for a in args) + " <;> rfl"
            if nd.get("final"):
                L.append("theorem %s %s : lut %d (%s) = decide (%s ≥ %d) := by\n  %s" % (g, binder, tts[0], idx(args), insum, 1 << fl, cases))
            else:
                rhs = term([(1 << d, "(lut %d (%s)).toNat" % (t, idx(args))) for (_, d), t in zip(outs, tts)])
                if fl:
                    rhs = "(%s) %% %d + %s" % (insum, 1 << fl, rhs) if outs else "(%s) %% %d" % (insum, 1 << fl)
                L.append("theorem %s %s : %s = %s := by\n  %s" % (g, binder, insum, rhs, cases))
        g = generic[key]
        actual = [ref(w) for w in ins]
        for (o, d), t in zip(outs, tts):
            L.append("def w_%s (x : Nat → Bool) : Bool := lut %d (%s)" % (o, t, idx(actual)))
        us = "_ " * K
        act_sum = term([(w, "%s.toNat" % a) for w, a in zip(wts, actual)] + ([(1, str(add))] if add else []))
        if nd.get("final"):
            o = outs[0][0]
            L.append("theorem e%d (x : Nat → Bool) : w_%s x = decide (%s ≥ %d) := %s %s" % (k, o, act_sum, 1 << fl, g, us))
            finals.append((k, o, ins, wts, add, unit, fl))
            for w in ins:
                column.setdefault(w, None)
            column[o] = m
            continue
        res = None
        rhs_pairs = [(1 << d, "(w_%s x).toNat" % o) for o, d in outs]
        if fl:
            res = "r%d" % k
            L.append("def %s (x : Nat → Bool) : Nat := (%s) %% %d" % (res, act_sum, 1 << fl))
            L.append("theorem %s_lt (x : Nat → Bool) : %s x < %d := Nat.mod_lt _ (by decide)" % (res, res, 1 << fl))
            rhs_pairs = [(1, "%s x" % res)] + rhs_pairs
        L.append("theorem u%d (x : Nat → Bool) : %s = %s := %s %s" % (k, act_sum, term(rhs_pairs), g, us))
        raw_in = [] if trace else [w for w in ins if w.startswith("A[") and column[w] == 0]
        cons = {w: column[w] for w in ins if w not in raw_in}
        consumed_inputs.update(raw_in)
        prod = {}
        for o, d in outs:
            column[o] = unit + d
            prod[o] = unit + d
        e = {"cons": cons, "prod": prod, "adds": [add << unit] if add else [], "res": [(unit, res)] if res else [],
             "lem": "e%d" % k, "raw": raw_in, "bundle": None, "k": k}
        lhs, rhs = scaled(e)
        L.append("theorem e%d (x : Nat → Bool) : %s = %s := by\n  have h := u%d x\n  omega" % (k, lhs, rhs, k))
        eqs.append(e)

    root_seg = None
    if trace:
        by_k = {e["k"]: e for e in eqs}
        blk, segs = [], []
        for i, t in enumerate(trace):
            own = [by_k[k] for k in range(t["nodes"][0], t["nodes"][1]) if k in by_k]
            if "inputs" in t:
                ins_ = sorted(t["inputs"])
                assert ins_ == list(range(ins_[0], ins_[0] + len(ins_))), "leaf blocks must be contiguous"
                body = " + ".join(["0"] + ["(x %d).toNat" % j for j in ins_])
                L.append("def I_b%d (x : Nat → Bool) : Nat := %s" % (i, body))
                bundles.append("I_b%d" % i)
                L.append("theorem b%d (x : Nat → Bool) : I_b%d x = %s := by\n  unfold I_b%d\n  omega" % (
                    i, i, " + ".join("(x %d).toNat" % j for j in ins_), i))
                base = {"cons": {}, "prod": {"A[%d]" % j: 0 for j in ins_}, "adds": [], "res": [], "lem": "b%d" % i,
                        "raw": [], "bundle": "I_b%d" % i}
                e = merge([base] + own, "t%d" % i)
                sg = [(ins_[0], len(ins_))]
                L.append("theorem s%d (x : Nat → Bool) : %s x = pc x %d %d := rfl" % (i, e["bundle"], sg[0][0], sg[0][1]))
            else:
                l, r = t["children"]
                e = merge([blk[l], blk[r]] + own, "t%d" % i)
                parts = sorted(segs[l] + segs[r])
                out, haves = [], ["  have hl := s%d x" % l, "  have hr := s%d x" % r]
                for a, m in parts:
                    if out and out[-1][0] + out[-1][1] == a:
                        a0, m0 = out[-1]
                        haves.append("  have : pc x %d %d = pc x %d %d + pc x %d %d := pc_add x %d %d %d" % (a0, m0 + m, a0, m0, a, m, a0, m0, m))
                        out[-1] = (a0, m0 + m)
                    else:
                        out.append((a, m))
                sg = out
                L.append("theorem s%d (x : Nat → Bool) : %s x = %s := by\n%s\n  unfold %s\n  omega" % (
                    i, e["bundle"], " + ".join("pc x %d %d" % p for p in sg), "\n".join(haves), e["bundle"]))
            blk.append(e)
            segs.append(sg)
        root = len(trace) - 1
        assert segs[root] == [(0, n)], segs[root]
        root_seg = (blk[root]["bundle"], "s%d" % root)
        end = trace[root]["nodes"][1]
        eqs = [blk[root]] + [e for e in eqs if e["k"] >= end]
    level, cnt = eqs, 0
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), chunk):
            nxt.append(merge(level[i:i + chunk], "c%d" % cnt) if len(level[i:i + chunk]) > 1 else level[i])
            cnt += 1
        level = nxt
    top = level[0] if level else None
    if top is not None and top["lem"].startswith("e"):
        top = merge(level, "top")
    explicit = " + ".join("(x %d).toNat" % i for i in range(n))
    dropped_in = [("A[%d]" % i, 0) for i in range(n) if "A[%d]" % i not in consumed_inputs]
    final_raw = [w for f in finals for w in f[2] if w.startswith("A[")]
    P = ["theorem correct (x : Nat → Bool) : w_maj x = decide (popcount x %d ≥ %d) := by" % (n, T),
         "  apply of_iff",
         "  have hp : popcount x %d = %s := by\n    show 0 + %s = _\n    rw [Nat.zero_add]" % (n, explicit, explicit),
         "  have hle := popcount_le x %d" % n]
    if top is not None and root_seg:
        chain = [b for b in bundles[bundles.index(root_seg[0]) + 1:]]
        P = ["theorem correct (x : Nat → Bool) : w_maj x = decide (popcount x %d ≥ %d) := by" % (n, T),
             "  apply of_iff",
             "  have hle := popcount_le x %d" % n,
             "  have ht := %s x" % top["lem"],
             "  have hI : %s x = popcount x %d := by\n%s    rw [%s x]\n    exact (popcount_eq_pc x %d).symm" % (
                 top["bundle"], n, ("    simp only [%s]\n" % ", ".join(chain)) if chain else "", root_seg[1], n),
             "  rw [hI] at ht"]
        dropped_in = []
    elif top is not None:
        lp, rp, _ = sides(top)
        dz = [(1, "%s.toNat" % ref(w)) for w, _ in dropped_in]
        rest = [(c, e) for c, e in lp if not e.startswith("I_")]
        P.append("  have ht := %s x" % top["lem"])
        if top["bundle"]:
            tgt = "(%s x) + (%s)" % (top["bundle"], term(dz)) if dz else "(%s x)" % top["bundle"]
            P.append("  have hI : %s = %s := by\n    simp only [%s]\n    all_goals ac_rfl" % (explicit, tgt, ", ".join(bundles)))
            P.append("  rw [hI] at hp")
            P.append("  clear hI")
    for u, r in (top["res"] if top else []):
        P.append("  have := %s_lt x" % r)
    seen = set()
    for w in (list(top["prod"]) if top else []) + [w for f in finals for w in f[2]] + [w for w, _ in dropped_in]:
        if w not in seen:
            seen.add(w)
            P.append("  have := Bool.toNat_le %s" % ref(w))
    for k, o, ins, wts, add, unit, fl in finals:
        P.append("  have := to_iff _ _ (e%d x)" % k)
        P.append("  have := Bool.toNat_le (w_%s x)" % o)
    P.append("  omega")
    L += P
    L.append("#print axioms correct")
    return "\n".join(L) + "\n"


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--netlist", type=Path, required=True)
    p.add_argument("--derivation", type=Path, required=True)
    p.add_argument("--chunk", type=int, default=12)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    a.out.write_text(emit(a.netlist.read_bytes(), json.loads(a.derivation.read_text()), a.chunk))
