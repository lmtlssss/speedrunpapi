"""Threshold-count compiler: ground truth, proof replay, tamper rejection, pinned EPFL voter result."""
import copy
import hashlib
import itertools
import json
import random
import unittest
from pathlib import Path

from threshold_compiler import compile_threshold
from independent_threshold_checker import parse_blif, verify

HERE = Path(__file__).resolve().parent


def simulate(raw, x):
    ins, _, tables = parse_blif(raw)
    val = dict(zip(ins, x))

    def ev(w):
        if w not in val:
            fan, on = tables[w]
            val[w] = int("".join(str(ev(a)) for a in fan) in on)
        return val[w]
    return ev("maj")


class TestThreshold(unittest.TestCase):
    def test_exhaustive_ground_truth(self):
        rows = 0
        for n in range(1, 13):
            for T in range(1, n + 1):
                for kw in ({"k": 6}, {"k": 4}, {"k": 6, "objective": "depth", "wallace": 1}):
                    raw, cert = compile_threshold(n, T, **kw)
                    self.assertTrue(verify(raw, cert)["ok"], (n, T, kw))
                    for x in itertools.product((0, 1), repeat=n):
                        rows += 1
                        self.assertEqual(simulate(raw, x), int(sum(x) >= T), (n, T, kw, x))
        self.assertGreater(rows, 250000)

    def test_tampered_derivations_and_netlists_rejected(self):
        raw, cert = compile_threshold(201, 101)
        self.assertTrue(verify(raw, cert)["ok"])
        rng = random.Random(1)
        for _ in range(150):
            c = copy.deepcopy(cert)
            node = rng.choice(c["nodes"])
            kind = rng.choice(("weight", "add", "unit", "floor"))
            if kind == "weight":
                node["in"][0][1] *= 2
            elif kind == "add":
                node["add"] += 1
            elif kind == "unit":
                node["unit"] += 1
            else:
                node["floor"] ^= 1
            self.assertFalse(verify(raw, c)["ok"], kind)
        lines = raw.decode().splitlines()
        rowsidx = [i for i, s in enumerate(lines) if s.endswith(" 1")]
        for _ in range(150):
            l = lines[:]
            del l[rng.choice(rowsidx)]
            bad = ("\n".join(l) + "\n").encode()
            c = dict(cert, netlist_digest="sha256:" + hashlib.sha256(bad).hexdigest())
            self.assertFalse(verify(bad, c)["ok"])
        self.assertFalse(verify(raw, dict(cert, threshold=102))["ok"])
        self.assertFalse(verify(raw + b"\n", cert)["ok"])

    def test_epfl_voter_pinned_results(self):
        tree = json.loads((HERE / "epfl_voter_tree.json").read_text())
        raw, cert = compile_threshold(1001, 501, tree=tree)
        self.assertEqual(cert["netlist_digest"],
                         "sha256:77a3b2e806d15e1b02e8ba132b29c239fcbb0ceaf3a966beb9380154b7ec2eed")
        res = verify(raw, cert)
        self.assertTrue(res["ok"])
        self.assertEqual((res["lut_count"], res["levels"], res["max_fanin"]), (993, 15, 6))
        raw, cert = compile_threshold(1001, 501)
        res = verify(raw, cert)
        self.assertTrue(res["ok"])
        self.assertEqual(res["lut_count"], 987)
        raw, cert = compile_threshold(1001, 501, objective="depth", wallace=3)
        res = verify(raw, cert)
        self.assertTrue(res["ok"])
        self.assertEqual((res["lut_count"], res["levels"]), (1008, 9))
        rng = random.Random(7)
        for _ in range(40):                       # spot simulation near the threshold
            ones = rng.choice((499, 500, 501, 502))
            x = [1] * ones + [0] * (1001 - ones)
            rng.shuffle(x)
            self.assertEqual(simulate(raw, x), int(ones >= 501))


if __name__ == "__main__":
    unittest.main(verbosity=2)
