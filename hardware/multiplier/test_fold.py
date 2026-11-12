"""Fold divider tests: exhaustive truth at small widths, checker acceptance, and tamper rejection.
A tampered netlist is accepted only if it still computes the division on every input."""
import hashlib
import json
import random
import sys

import blif_sim
import div_compiler as DC
import div_fold
import independent_fold_checker as CK


def truth_ok(raw, n, path):
    open(path, "wb").write(raw)
    ins, outs, nodes = blif_sim.load(path)
    N = 1 << (2 * n)
    env = {}
    for i in range(n):
        env["a[%d]" % i] = sum(1 << s for s in range(N) if (s >> i) & 1)
        env["b[%d]" % i] = sum(1 << s for s in range(N) if (s >> (n + i)) & 1)
    blif_sim.run(ins, outs, nodes, env, N)
    for s in range(N):
        a, b = s & ((1 << n) - 1), s >> n
        want = (a // b, a % b) if b else ((1 << n) - 1, a)
        q = sum(((env["quotient[%d]" % i] >> s) & 1) << i for i in range(n))
        r = sum(((env["remainder[%d]" % i] >> s) & 1) << i for i in range(n))
        if (q, r) != want:
            return False
    return True


def main(tmp, trials=120):
    rnd = random.Random(7)
    for n, b in ((8, 2), (9, 3)):
        net = div_fold.compile_div(n, b)
        raw = DC.blif(net, n)
        cert = div_fold.certificate(net, n, b, raw)
        cert = json.loads(json.dumps(cert))
        assert truth_ok(raw, n, tmp + "/t.blif"), "truth"
        res = CK.verify(raw, cert)
        assert res["ok"], res
        print("n=%d fold=%d: %d LUT, %d levels, exhaustive truth and checker ok" % (n, b, res["lut_count"], res["levels"]))
        if n != 8:
            continue
        lines = raw.decode().split("\n")
        rows = [i for i, l in enumerate(lines) if l and l[0] in "01" and l.endswith(" 1")]
        rejected = accepted_correct = 0
        for _ in range(trials):
            i = rnd.choice(rows)
            mutated = lines[:i] + lines[i + 1:]                 # remove one minterm
            data = ("\n".join(mutated)).encode()
            c2 = dict(cert, netlist_digest="sha256:" + hashlib.sha256(data).hexdigest())
            res = CK.verify(data, c2)
            if res["ok"]:
                assert truth_ok(data, n, tmp + "/t.blif"), "FALSE ACCEPTANCE at line %d" % i
                accepted_correct += 1
            else:
                rejected += 1
        print("tamper: %d rejected, %d accepted and still correct, 0 false acceptances" % (rejected, accepted_correct))
        # derivation tampers: swap two wires of a word
        bad = json.loads(json.dumps(cert))
        st = bad["dn"]["stages"][-1]
        st[0], st[1] = st[1], st[0]
        assert not CK.verify(raw, bad)["ok"]
        bad = json.loads(json.dumps(cert))
        bad["table"]["M"][0], bad["table"]["M"][1] = bad["table"]["M"][1], bad["table"]["M"][0]
        assert not CK.verify(raw, bad)["ok"]
        print("derivation tampers rejected")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "/tmp")
