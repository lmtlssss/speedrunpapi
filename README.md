# speedrunpapi

Output-determinism analysis for Circom circuits and R1CS, by [Colony Technology](https://colony.technology).

An under-constrained circuit accepts more than one output for the same input, so the prover decides the result instead of the circuit. `speedrunpapi` checks that property on the constraint system the compiler emits and returns one of three verdicts. Each is backed by something you can re-check without trusting this tool.

| Verdict | Meaning | Backed by |
| --- | --- | --- |
| `Certified` | Every satisfying witness with the same inputs has the same outputs. | A derivation, replayed by a checker that shares no rule logic with the prover |
| `Broken` | Two satisfying witnesses share every input and differ on an output. | Both witnesses, re-evaluated against every constraint |
| `Unknown` | Neither was established. | The signals that are still open, and why |

The tool does not guess. A circuit it cannot decide is `Unknown`.

## Quick start

Requires Node.js 20+ and the [circom](https://docs.circom.io/getting-started/installation/) compiler 2.x for `.circom` input.

```sh
npx speedrunpapi scan circuit.circom
```

```text
Broken  examples/division.circom
  claim    Two satisfying witnesses share every input signal and differ on an output signal.
  system   circom 2.2.3 --O0 · 1 constraints · 4 wires · 1 outputs · 2 inputs
  inputs   main.a = 0, main.b = 0
  differs  main.q: 0 vs 1
  checked  both witnesses satisfy all 1 constraints
```

```sh
npm install -g speedrunpapi      # or: pip install speedrunpapi  (same bundle; still needs Node.js)
speedrunpapi scan examples/iszero.circom examples/decoder.circom examples/modsum-safe.circom
```

Exit status is `0` when every file is `Certified`, `2` if any is `Broken`, `3` if any is `Unknown`, `1` on error. Analysis runs on your machine; nothing is uploaded unless you supply an API key for a signed certificate.

## Usage

```sh
# A circuit with a main component
speedrunpapi scan circuits/withdraw.circom -l node_modules

# A library template: instantiate it as main
speedrunpapi scan node_modules/circomlib/circuits/comparators.circom --main "LessThan(64)" -l node_modules/circomlib/circuits

# A template that expects bits: state the precondition, and it becomes part of the claim
speedrunpapi scan pedersen.circom --main "Pedersen(248)" --assume-binary in

# An R1CS you already compiled (a sibling .sym supplies signal names)
speedrunpapi scan build/withdraw.r1cs

# Machine-readable result, and the full report for independent checking
speedrunpapi scan circuit.circom --json
speedrunpapi scan circuit.circom --report out/circuit.report.json
speedrunpapi verify out/circuit.report.json --source out/circuit.r1cs
```

| Option | Effect |
| --- | --- |
| `--main "T(args)"` | Instantiate a template as the main component (for library files) |
| `-l, --include <dir>` | circom library directory, repeatable |
| `--assume-binary <pattern>` | Treat matching input signals as bits: `in`, `"sel[*]"`, `"*"` |
| `--strict` | Require every signal, not only outputs, to be fixed by the inputs |
| `--opt O0\|O1\|O2` | Force one circom simplification level (see below) |
| `--report <path>` | Write the full report: derivation or witnesses, plus what it is bound to |
| `--json`, `--full` | JSON summary; `--full` adds the derivation or witnesses |
| `--sarif <file>` | `Broken` results as SARIF for code-scanning dashboards |
| `--timeout`, `--cex-timeout` | Seconds for proof search (600) and counterexample search (15) |
| `--circom <bin>`, `--prime <name>` | Compiler binary and field (`bn128`, `bls12381`, `goldilocks`, ...) |

## What is claimed, exactly

`Certified` states output determinism of one constraint system: for any two assignments that satisfy every constraint and agree on all input signals, the output signals agree. With `--strict` the same is stated for every signal.

It does not state that a witness exists, that the circuit computes what you intended, that inputs are range-checked, or anything about a proving system. A deterministic circuit can still compute the wrong function.

A circuit with no output signals is never `Certified`: the property says nothing about it. The report then lists the internal signals that are not fixed by the inputs, which is where hint-related bugs live in assert-only circuits.

`--assume-binary` adds the constraint `x * (x - 1) = 0` for each matched input. The verdict then holds for callers that respect the assumption and says nothing about callers that do not. The assumptions are written into the report and the certificate.

### Compiler levels

A verdict about a `.circom` file is a verdict about the R1CS that circom emits for it, under the recorded compiler version and flags.

circom `--O0` applies no simplification, so that system describes the circuit exactly. From `--O1` (circom's default) the compiler merges signals, and an input that equals another signal loses its wire without the `.sym` file recording it; at `--O2` inputs can be substituted by linear combinations. A proof of determinism carries over to every level. A counterexample does not, unless every declared input still has a wire.

`scan` therefore analyses the `--O0` system first and accepts its proof or counterexample. If that is `Unknown` it tries `--O1`, and accepts a counterexample there only when all declared inputs are wired. When you scan an `.r1cs` directly and some declared inputs have no wire, the tool can still certify but will not report `Broken`. Scan the `.circom` source, or an R1CS compiled with `--O0`.

## How it decides

The prover works on the difference of two satisfying assignments that agree on the inputs and shows, wire by wire, that the difference is zero. Rules:

- **lin**: a constraint reduces to a linear equation with constant coefficients in which one wire is not yet determined.
- **fix**: a constraint that mentions a single wire and has a single root.
- **bits**: a linear equation whose undetermined wires are all two-valued, with weights for which the subset-sum map is injective below the modulus. This is the bit-decomposition argument, and it is why `Num2Bits(254)` over BN254 is not certified.
- **gauss**: a linear combination of such equations isolates a wire.
- **onehot**: a selector family. Constraints `s_i * (L - c_i) = C_i` share one determined form `L` and have pairwise distinct constants `c_i`, and a linear equation ties exactly those `s_i` together. At most one factor is zero; every other `s_i` is fixed by its own constraint and the equation fixes the last. This settles `Decoder`-style selectors in one step.
- **split**: case analysis on a determined linear form being zero or nonzero. Both assignments fall in the same case; a wire determined in both cases, or in one while the other is contradictory, is determined. This covers `IsZero` and guarded divisions.

Every rule application is a step in the derivation. The checker re-reads each cited constraint from the R1CS and accepts a step only if its conclusion follows.

For `Broken`, the tool fixes concrete inputs, solves the system by propagation, and looks for a second solution with different outputs, steering inputs toward the degenerate cases the prover could not rule out (a divisor being zero, for example). A pair is reported only after both assignments pass a full evaluation of every constraint.

## Measured

circomlib templates compiled with circom 2.2.3 at `--O0`, analysed on an Apple M1 with Node.js 26. Times are single runs in milliseconds.

| Circuit | Verdict | Constraints | Derivation steps | Prove | Replay |
| --- | --- | ---: | ---: | ---: | ---: |
| `Sha256compression()` | Certified | 202,784 | 192,312 | 228 | 155 |
| `Sha256(64)` | Certified | 204,576 | 194,104 | 252 | 160 |
| `Poseidon(5)` | Certified | 1,347 | 1,347 | 1.9 | 1.1 |
| `MiMCSponge(2, 220, 1)` | Certified | 1,767 | 1,767 | 2.1 | 2.7 |
| Poseidon Merkle root, depth 4 | Certified | 3,102 | 3,098 | 2 | 2 |
| `LessThan(252)` | Certified | 256 | 3 | 0.8 | 0.6 |
| `Multiplexer(2, 4)` | Certified | 36 | 31 | 0.3 | 0.1 |
| `IsZero()` | Certified | 2 | 4 | 0.2 | 0.1 |
| `Num2Bits(254)` | Broken | 255 | | | |
| `Decoder(4)` | Broken | 6 | | | |
| `MontgomeryAdd()` | Broken | 3 | | | |
| `Edwards2Montgomery()` | Broken | 2 | | | |
| `Pedersen(8)`, inputs unrestricted | Broken | 95 (`--O1`) | | | |
| `BabyAdd()` | Unknown | 6 | | | |
| `BabyPbk()` | Unknown | 10,114 | | | |
| `Num2Bits_strict()` | Unknown | 1,285 | | | |

The `Broken` rows are properties of those templates taken alone, with unrestricted inputs. circomlib uses several of them only where the caller rules the degenerate inputs out (`Multiplexer` forces `Decoder`'s `success` to one; Pedersen callers pass bits). The verdict tells you which preconditions your circuit must enforce.

The corpus has 71 circom-compiled cases with known answers. The engine currently decides 61 of them and reports `Unknown` for 10; none of its verdicts contradicts the known answer. A separate fuzzer compares the engine against brute-force enumeration on random systems over small fields (150,000 systems in the release run, no wrong `Certified` or `Broken`).

## What returns Unknown today

- Elliptic-curve arithmetic whose uniqueness depends on a number-theoretic fact, such as the completeness of the Baby Jubjub addition law.
- Big-integer arithmetic whose uniqueness depends on range bounds across limbs.
- Alias checks (`Num2Bits_strict`, `AliasCheck`) that compare a bit string against the modulus.
- Circuits with no outputs.
- R1CS with custom gates (PLONK custom templates), or over a field other than the ones circom targets.

For these the report lists each open signal with the condition under which a constraint would fix it, for example `main.xout: fixed by constraint 4 only where (1 + 168696*main.tau) != 0`. Each line is an obligation to discharge by review.

## Checking a result yourself

A report is self-contained: the derivation or the two witnesses, the R1CS digest, the compiler and flags, and any assumptions.

```sh
speedrunpapi scan circuit.circom --report circuit.report.json     # also writes circuit.r1cs
speedrunpapi verify circuit.report.json --source circuit.r1cs
python3 verifiers/determinism/determinism_check.py circuit.r1cs circuit.report.json
```

`verify` uses the JavaScript checker. `determinism_check.py` is a second implementation in Python with no dependencies beyond the standard library and its own R1CS parser. To tie the R1CS back to your source, recompile with the recorded compiler version and flags and compare digests.

## CI

```yaml
- uses: actions/checkout@v4
- uses: lmtlssss/speedrunpapi@v0.7.1
  with:
    file: circuits/main.circom
    include: node_modules/circomlib/circuits
```

The Action installs the pinned circom compiler, scans, uploads the report, and fails on `Broken`. Set `fail_on_unknown: true` to require `Certified`. Supplying `api_key` additionally requests a signed certificate.

## Signed certificates

Local analysis is free. A paid API key adds an Ed25519-signed statement from Colony Technology that its service replayed your derivation, or re-evaluated your witness pair, against the R1CS you submitted:

```sh
export COLONY_API_KEY=...
speedrunpapi scan circuit.circom --require-signed
```

The service signs only `Certified` and `Broken` results that it has itself re-verified. It does not sign `Unknown`, and it does not sign a verdict it was merely told. The certificate names the R1CS digest, the derivation digest and any assumptions; the source file name and compiler are recorded as client-declared, because the service cannot run your compiler. Uploads are limited to 8 MiB of R1CS; larger circuits are checked locally with `verify` and the Python checker. Certificate status and revocations are public at `api.colony.technology/v1/certificates/status` and `/v1/revocations`.

To check a certificate offline, `node verifiers/cert/verify.mjs certificate.json circuit.r1cs` verifies the Ed25519 signature against the pinned public key and that the certificate names the digest of your file. A signature authenticates the issuer's statement; the report is what lets you re-check the claim itself. Credit packs: [colony.technology/packs](https://colony.technology/packs).

## Changes in 0.7.1

(There is no 0.7.0 package: that tag was placed on the wrong commit and was never published.)

Versions before 0.7.1 classified Circom, Verilog and INT8 sources by template name and keyword. They could report `Certified` for a circuit whose outputs were unconstrained, and the hosted service would sign that verdict. Those results were not proofs.

0.7.1 replaces that analyzer with the one described above, which reasons about the compiled constraint system. If you relied on a `Certified` result from an earlier version, scan again. Certificates issued before 0.7.1 have been revoked.

The Verilog, INT8, ONNX-text and carry-graph classifiers are removed and those inputs return `Unknown`. So are the Bitcoin Script and RV32IM trace adapters: an audit found that the first executed nothing (it accepted scripts that can never complete) and the second only replayed a trace against instruction words the trace itself supplied.

## Also in this package

The hosted-job client (`run`, `solve`, `quote`, `optimize`, `status`, `result`, `check`) and the offline ONNX checker (`verify-onnx`) are unchanged in this release. See [docs/hosted-jobs.md](docs/hosted-jobs.md). The [SCITT claim profile](standards/scitt-exact-computation/) is an individual technical proposal and has not been submitted to the IETF Datatracker.

## Hardware

The same mathematics builds logic. Compilers, netlists and proofs are under [`hardware/`](hardware/).

| EPFL benchmark | Published best | Colony |
| --- | --- | --- |
| `voter`, size | 1145 LUT-6 | 987 LUT-6 |
| `voter`, depth | 11 levels | 9 levels |
| `multiplier`, size | 4282 LUT-6 | 3654 LUT-6 |
| `multiplier`, depth | 25 levels | 11 levels |
| `square`, size | 2894 LUT-6 | 2497 LUT-6 |
| `square`, depth | 10 levels, 3690 LUT-6 | 10 levels, 3358 LUT-6 |
| `sqrt`, size | 2958 LUT-6 | 2174 LUT-6 |
| `hyp`, size | 36451 LUT-6 | 24898 LUT-6 |
| `div`, size | 3082 LUT-6 | 2287 LUT-6 |
| `div`, depth | 170 levels, 30849 LUT-6 | 58 levels, 20232 LUT-6 |
| `sixteen`, size | 3282958 LUT-6 | 13092 LUT-6 |
| `twenty`, size | 4166467 LUT-6 | 13079 LUT-6 |
| `twentythree`, size | 470892 LUT-6 | 13104 LUT-6 |
| `sixteen`, depth | 14 levels, 3387001 LUT-6 | 9 levels, 407332 LUT-6 |
| `twenty`, depth | 14 levels, 4381634 LUT-6 | 9 levels, 419071 LUT-6 |
| `twentythree`, depth | 15 levels, 4913996 LUT-6 | 9 levels, 468313 LUT-6 |

[`hardware/epfl-mtm/`](hardware/epfl-mtm/) holds `sixteen`, `twenty` and `twentythree`, the 16 to 23 million gate circuits of the suite. They are the truth table of a Fibonacci loop in 64-bit integers; the netlists compute it, and each is proven equivalent to the original in minutes without a solver.

[`hardware/divider/udiv.v`](hardware/divider/) is a drop-in unsigned divider: 4,889 cells at 64 bits on Lattice ECP5, placed and routed, where the Verilog operators take 12,246.
`udivf64.v` in the same directory divides in 181 ns on that device, where the operators take 394 ns.
[`hardware/linear/`](hardware/linear/) builds XOR logic: CRC-32 over a 512-bit bus in 701 LUT-6 at 4 levels, where Yosys takes 2,344; with any number of valid bytes, 1,172.

[`hardware/audit/`](hardware/audit/) runs open arithmetic cores beside exact arithmetic: a double-precision divider in a 763-star FPU returns 2^29 times the quotient for a band of subnormal results.
Every netlist has an independent checker; the division and square-root recurrences are proved in Lean 4.

[Terms](https://colony.technology/terms) · [Releases](https://github.com/lmtlssss/speedrunpapi/releases)
