"""Official-evaluator route: prove reference == delivered with ABC `cec`, one tree level at a time.

A direct `cec reference delivered` is undecided: the two netlists share no internal
functions and SAT cannot bridge two different 1001-input counters.  The chain inserts
hybrids H_h (tree blocks of height <= h in Colony's redundant form, converted to binary
at the cut; plain binary addition above).  Consecutive netlists differ by one local merge
rule, so ABC's SAT sweeping matches the block sums and each step is decided.
Equivalence is transitive, so the chain is a proof by the evaluator alone.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

from threshold_compiler import compile_threshold
from independent_threshold_checker import verify


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--threshold", type=int, required=True)
    p.add_argument("--tree", type=Path, required=True)
    p.add_argument("--reference", type=Path, required=True)
    p.add_argument("--policy", default="size")
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=1800)
    p.add_argument("--abc", default=os.environ.get("ABC_BIN", "yosys-abc"))
    a = p.parse_args()
    tree = json.loads(a.tree.read_text())
    pol = tuple([a.policy.split(":")[0]] + [int(x) for x in a.policy.split(":")[1:]])
    a.out.mkdir(parents=True, exist_ok=True)
    height = 0
    hmap = {}
    from threshold_compiler import load_tree
    t = load_tree(tree)
    split = {tuple(b): (tuple(l), tuple(r)) for b, l, r in t["split"]}

    def ht(b):
        if b not in hmap:
            hmap[b] = 0 if b not in split else 1 + max(ht(c) for c in split[b])
        return hmap[b]
    height = ht(tuple(t["root"]))
    names = []
    for cut in list(range(height + 1)) + [None]:
        raw, cert = compile_threshold(a.n, a.threshold, tree=tree, policy=pol, cut=cut)
        if not verify(raw, cert)["ok"]:
            raise SystemExit("derivation replay failed at cut %s" % cut)
        name = "delivered.blif" if cut is None else "hybrid_%02d.blif" % cut
        (a.out / name).write_bytes(raw)
        if cut is None:
            (a.out / "delivered.derivation.json").write_text(json.dumps(cert, sort_keys=True) + "\n")
        names.append((name, cert["lut_count"], cert["levels"], cert["netlist_digest"]))
    ver = subprocess.run([a.abc, "-c", "version"], capture_output=True, text=True).stdout.strip().splitlines()[-1:]
    steps, prev, prev_name = [], a.reference, "reference"
    ok = True
    for name, luts, levels, dig in names:
        t0 = time.time()
        try:
            out = subprocess.run([a.abc, "-c", "cec -n %s %s" % (prev, a.out / name)],
                                 capture_output=True, text=True, timeout=a.timeout).stdout
            m = re.search(r"Networks are [^\n]*", out)
            verdict = m.group(0).split("  ")[0].strip() if m else "no verdict"
        except subprocess.TimeoutExpired:
            verdict = "timeout"
        good = verdict.startswith("Networks are equivalent")
        ok = ok and good
        steps.append({"left": prev_name, "right": name, "right_digest": dig, "right_lut_count": luts,
                      "right_levels": levels, "abc_verdict": verdict, "seconds": round(time.time() - t0, 2)})
        print(json.dumps(steps[-1], sort_keys=True), flush=True)
        prev, prev_name = a.out / name, name
    log = {"schema": "colony.abc-chain.v1", "evaluator": "ABC cec -n", "abc": ver,
           "reference_digest": "sha256:" + hashlib.sha256(a.reference.read_bytes()).hexdigest(),
           "all_steps_equivalent": ok, "steps": steps}
    (a.out / "abc_chain.json").write_text(json.dumps(log, indent=1, sort_keys=True) + "\n")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
