# ᑕ. exact arithmetic circuit verification

[Live race](https://colony.technology/demo) · [Proofs](https://colony.technology/proofs) · [API](https://colony.technology/api)

Paste source, press ᑕ., get a scoped verdict. Local scanning runs on your machine, without an account or API key.

The SHA-256 compression race runs both analyzers live: ᑕ. returns its scoped compositional certificate in microseconds while Picus runs through its 180-second solver budget. The 21 controlled G1 comparisons, source and timings are linked from [proofs](https://colony.technology/proofs).

## Install

Node.js 20 or later:

```sh
npx speedrunpapi scan circuit.circom --json
```

For repeated use:

```sh
npm install -g speedrunpapi
speedrunpapi scan circuit.circom --json
```

Or download the same standalone bundle:

```sh
curl -fsSL https://colony.technology/speedrunpapi.mjs -o speedrunpapi.mjs
node speedrunpapi.mjs scan circuit.circom --json
```

Python 3.9+ and Node.js 20+:

```sh
pip install speedrunpapi
speedrunpapi scan circuit.circom --json
```

## Hosted verified jobs

`speedrunpapi` includes a public client for Colony's hosted optimization and proof service. Set `COLONY_API_KEY` to an active, funded customer key. The same commands work from the npm and Python packages. The source is sent to the hosted API only when you run a hosted command.

```sh
export COLONY_API_KEY="your-customer-key"
speedrunpapi quote model.onnx
speedrunpapi optimize model.onnx --out optimized.onnx --proof-dir evidence
speedrunpapi verify-onnx evidence/source.onnx evidence/artifacts
```

`optimize` returns an executable ONNX model and its source-bound proof artifacts. `verify-onnx` runs the independent checker locally, without the API, the private optimizer or an API key. Install the checker dependencies with `python3 -m pip install 'onnx>=1.16,<2' 'numpy>=1.26,<3'`. For the Python distribution use `pip install 'speedrunpapi[onnx]'`. The CPU timing evidence is a measured observation on the stated host; each exact stage proof checks model behavior under its declared semantics.

For other supported exact problems, use `speedrunpapi run problem.math`, `speedrunpapi solve problem.math`, `speedrunpapi status <job-id>`, `speedrunpapi result <job-id>` and `speedrunpapi check source.file result.json`. `speedrunpapi jobs <command>` and the `colony-jobs` executable expose the same hosted interface. Requests consume credits only when the service accepts and settles a funded job. The hosted API is [api.colony.technology](https://api.colony.technology).

### Exact mathematical jobs (R11)

Eight bounded operators are registered. The public CLI now independently checks all eight, including the new cyclic inverse fibers, tap-span fiber counts, affine inverse cells, and two-stage addition codes. The bounded profiles state their exact input limits. They do not claim complete integration of the related research papers.

Four original input examples are in `examples/m01-cyclic-inverse.math` through `examples/m04-two-stage.math`. Three matching production result bundles accompany the M-02, M-03, and M-04 examples. Replay them offline with:

```sh
speedrunpapi check examples/m02-tap-span.math examples/m02-tap-span.result.json
speedrunpapi check examples/m03-affine-inverse.math examples/m03-affine-inverse.result.json
speedrunpapi check examples/m04-two-stage.math examples/m04-two-stage.result.json
```

These result bundles came from funded technical-test jobs in production. They carry original source digests and exact independent mathematical evidence. They do not represent external card payments. New hosted jobs require an API key with credits.

A [replayable production ONNX proof](proofs/hosted-onnx-production-20261110/) accompanies this release. The source, candidate, cost decision, transformation proof and independent checker are available to inspect. Local scans remain free and offline.

## Three verdicts

- `Certified` — a supported constraint pattern has one output under its stated input and range conditions.
- `Broken` — a supported pattern admits distinct witnesses; the result includes a counterexample.
- `Unknown` — the source needs a supported adapter or a complete constraint graph.

Supported inputs include recognized Circom, Verilog, int8 and ONNX source patterns; exact bounded `carry-graph-v1` JSON; native Bitcoin Script assembly and bytecode for the listed deterministic opcode subset; and RV32IM arithmetic-register guest traces for zkVM projects. Script certificates state deterministic final-stack behavior for a fixed initial stack. Guest trace certificates validate each supplied RISC-V instruction word and register write. These are scoped execution claims, separate from full BitVM or zkVM proof-system validity. The v2 RV32IM format checks conditional branches, jumps, aligned LW/SW word memory, and arithmetic transitions. Bitcoin Script supports alternate-stack transfer and hash opcodes. Host syscalls, signatures and unsupported operations return `Unknown`.

Binary snarkjs `.r1cs` v1 accepts triangular constant pivots and new coupled full-column-rank linear subsystems over BN254. Its guarantee is **at most one wire assignment with fixed public and private input values**. Rank-deficient or unrecognized nonlinear systems return `Unknown`. For `.r1cs`, `.bitvm`, `.script` or `.zkvm`, use `speedrunpapi verify result.json --source source.file` to re-run the source parser and exact certificate check. Source bytes and checker scope remain part of every signed result.

The source-bound Circom examples also cover exact AND, Mux1 field arithmetic and a five-bit LessThan constraint: `examples/and.circom`, `examples/mux.circom` and `examples/compare.circom`. The verifier checks the complete recognized constraints and returns `Unknown` for altered or incomplete templates.

Routine `--json` output contains the verdict, method, source checksum and proof fields. Research DOI metadata is available on demand with `--references`. Both output forms can be checked with `verify`.

Try `speedrunpapi scan examples/native_add.bitvm --json`, `speedrunpapi scan examples/rv32im_arithmetic_trace.zkvm --json` and `speedrunpapi scan examples/coupled_rank.r1cs --json`. The rank-deficient R1CS and forged RV32IM trace examples return `Unknown`. You can also run the original Circom cases: `examples/compare.circom` and `examples/modsum-broken.circom`.

## GitHub Action

```yaml
- uses: actions/checkout@v4
- uses: lmtlssss/speedrunpapi@v0.6.1
  with:
    file: circuits/main.circom
```

The Action scans checked-out source, fails on `Broken`, warns on `Unknown`, and uploads the result. Add an optional `api_key` to request a signed certificate. Source is analyzed again by the hosted API before signing. The [paid customer pilot workflow](https://github.com/lmtlssss/speedrunpapi/actions/workflows/customer-pilot.yml) uses a GitHub secret, submits a source-bound test-order certificate, verifies the public signature, and keeps the receipt as an artifact.

To display the scan workflow status in a repository README, save the above steps in `.github/workflows/speedrunpapi.yml`, then add:

```markdown
[![ᑕ. scan](https://github.com/OWNER/REPO/actions/workflows/speedrunpapi.yml/badge.svg)](https://github.com/OWNER/REPO/actions/workflows/speedrunpapi.yml)
```

Replace `OWNER/REPO` with that repository. The badge shows the workflow status. An issued, source-bound Certified certificate has its own public registry URL.

## Packages

`speedrunpapi@0.6.1` ships the local scanner, hosted universal-job client, and portable ONNX independent checker through [npm](https://www.npmjs.com/package/speedrunpapi) and [PyPI](https://pypi.org/project/speedrunpapi/). The sources and release record are available on [GitHub](https://github.com/lmtlssss/speedrunpapi/releases/tag/v0.6.1).

The free analyzer is bundled here. The paid API and signing service run at [api.colony.technology](https://api.colony.technology). [Terms](https://colony.technology/terms) · [Source release notes](https://github.com/lmtlssss/speedrunpapi/releases).

This public distribution contains the standalone client and its Action. Colony's private service infrastructure, billing, credentials and internal research remain separate.

## Portable ᑕ. proof demonstration

[Exact carry-state contraction, 4,096 → 6 retained states](proofs/carry-frontier-4096/) is a complete portable evidence packet. It preserves the declared high-result observations of six modular additions for **all admissible lower-prefix inputs and every high suffix**. The 682.7× factor describes the reduction in retained states, not a CPU speedup.

The original source, mathematical candidate, separate verifier source, exact input/claim digests and Ed25519 laboratory receipt travel together. A reviewer can run the independent checker with Python 3.11 and Node 20+:

`python3 proofs/carry-frontier-4096/verifier/verify.py`

This mathematical reproduction requires no Colony account, private optimizer, or network access. Its ephemeral Ed25519 signature is a laboratory attestation; commercial certificates and third-party challenge acceptance have separate issuance and review requirements. The [proof workflow](.github/workflows/portable-proof.yml) replays it on GitHub Actions. Additional source-bound operator evidence can be published beside this example when accepted externally.

## Portable certificate profile

The [Exact Computation Claim Profile for SCITT](standards/scitt-exact-computation/) is a public individual technical proposal for independently checked computational claims in signed COSE statements. It separates the issuer signature, exact evidence check and optional transparency receipt. The [ᑕ. mathematical definition](https://github.com/lmtlssss/math/tree/main/mathematics/discrete-mathematics/exact-state-contraction) is published with a paper and exact rational verifier. The IETF draft source is public; it has not yet been submitted to Datatracker.
