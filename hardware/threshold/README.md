# Threshold-count compiler

Builds `maj = [popcount(A[0..n-1]) >= T]` as a k-input LUT network, with a proof.

Uses: k-of-n voters, sync-word and preamble detectors with an error allowance, 1-bit correlators, binarised-network neurons.

## Method

Add the constant `2^m - T`. The answer is bit `m` of `popcount + constant`; no comparator is built.
Reduce the bit heap with counters of at most `k` inputs, one LUT per digit.
Only carries cross a column cut. The residue of a cleared column is never observed, so it is never computed.

## Results

Counts are ABC `print_stats` on LUT-6 netlists. Reference: EPFL `voter` (1001-input majority), lsils/benchmarks `82d8cc6910`.

| Netlist | LUT-6 | Levels | Evidence |
| --- | --- | --- | --- |
| EPFL best size, 2026 | 1145 | 33 | published |
| EPFL best depth, 2026 | 1325 | 11 | published |
| `epfl-voter/voter_size_987.blif` | 987 | 12 | derivation replay |
| `epfl-voter/voter_size_991.blif` | 991 | 14 | 12 chained ABC `cec` steps from the original |
| `epfl-voter/voter_depth_1005.blif` | 1005 | 9 | ABC-equivalent to `voter_depth.blif`, which has a derivation |

Submitted to the EPFL suite on 2026-11-11. Acceptance is the organisers' decision and is pending.

Placed and routed on Lattice ECP5 (Yosys `synth_ecp5` + nextpnr-ecp5, best of 3 seeds, register to register). The baseline is behavioural RTL, free to use carry chains.

| Inputs, T | Baseline | This compiler (`--k 4 --objective depth`) |
| --- | --- | --- |
| 36, 32 | 7.61 ns, 155 cells | 6.62 ns, 70 cells |
| 64, 56 | 12.87 ns, 271 cells | 8.76 ns, 139 cells |
| 127, 64 | 12.20 ns, 557 cells | 10.57 ns, 296 cells |
| 255, 160 | 16.62 ns, 1079 cells | 13.87 ns, 664 cells |

## Limits

- Timing is nextpnr's post-route estimate on one device family. The baseline is Yosys inference, not a vendor tool.
- The size objective produces long chains and is slower than the baseline. Use the depth objective for latency.
- On standard cells the LUT form is larger than a full-adder tree. Use `--k 3` there.
- Thresholds near 1 or n (plain OR / AND) are not special-cased and are far from minimal.
- A direct ABC `cec` between the original EPFL netlist and these netlists is undecided. `abc_chain.py` gives the chained route.

## Run

```sh
python3 threshold_compiler.py --n 64 --threshold 56 --objective depth --out out/
python3 independent_threshold_checker.py --netlist out/threshold.blif --derivation out/derivation.json
python3 lean_proof.py --netlist out/threshold.blif --derivation out/derivation.json --out out/proof.lean && lean out/proof.lean
python3 test_threshold.py
```

## Paid evaluation

One block of yours, in your flow: 2,500 USD, fixed.

You send the function, width, FPGA family and your reference RTL. You receive the LUT netlist as Verilog, the proof files with the independent checker, and a comparison sheet measured in your flow.
Full refund if the delivered block does not beat your reference on LUT count or logic depth.

Pay: https://buy.stripe.com/9B614m4Ls2kf6s277R6c004 · Questions: lmtlssss@colony.technology

## Proof

Three checks, sharing no code:

1. `independent_threshold_checker.py` replays the derivation: every node identity on all rows, then integer bookkeeping.
2. `lean_proof.py` emits a Lean 4 file (core Lean, no Mathlib) ending in
   `theorem correct (x : Nat → Bool) : w_maj x = decide (popcount x n ≥ T)`. Checked by the Lean kernel for n up to 255.
3. `bdd_threshold_check.cpp` compares canonical BDDs without any certificate. Completes for n up to 127.

Python 3.9+, standard library only. Licence: see `LICENSE.md` at the repository root.
