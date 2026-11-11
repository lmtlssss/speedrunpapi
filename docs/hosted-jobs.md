# Hosted jobs and offline checkers

This page carries the documentation of the hosted-job client and the ONNX checker as published with 0.6.4. They are unchanged in 0.7.1. The circuit scanner described in the main README is separate from these commands.

## Hosted jobs

`speedrunpapi` includes a public client for Colony's hosted optimization and proof service. Set `COLONY_API_KEY` to an active, funded customer key. The same commands work from the npm and Python packages. The source is sent to the hosted API only when you run a hosted command.

```sh
export COLONY_API_KEY="your-customer-key"
speedrunpapi quote model.onnx
speedrunpapi optimize model.onnx --out optimized.onnx --proof-dir evidence
speedrunpapi verify-onnx evidence/source.onnx evidence/artifacts
```

`optimize` returns an executable ONNX model and its source-bound proof artifacts. `verify-onnx` runs the independent checker locally, without the API, the private optimizer or an API key. Install the checker dependencies with `python3 -m pip install 'onnx>=1.16,<2' 'numpy>=1.26,<3'`. For the Python distribution use `pip install 'speedrunpapi[onnx]'`. The CPU timing evidence is a measured observation on the stated host; each exact stage proof checks model behavior under its declared semantics.

For other supported exact problems, use `speedrunpapi run problem.math`, `speedrunpapi solve problem.math`, `speedrunpapi status <job-id>`, `speedrunpapi result <job-id>` and `speedrunpapi check source.file result.json`. `speedrunpapi jobs <command>` and the `colony-jobs` executable expose the same hosted interface. Requests consume credits only when the service accepts and settles a funded job. The hosted API is [api.colony.technology](https://api.colony.technology).

### Exact mathematical jobs (R15)

Eighteen bounded exact operators are registered. They implement source-specific operators from the M-01 through M-14 mathematical papers, plus four foundational contracts. Each `.math` source names the exact operator and its input domain. The separate CLI checker reconstructs the original mathematics and rejects modified evidence even when its digest is recalculated. Unsupported parameters return `Unknown`.

M-05 adds complete cascaded sum/carry responses. M-07 and M-08 supply the 35-rectangle nonnegative tensor certificate and a 20-term signed tensor algorithm. M-09 checks the sparse GF(2) operators. M-10 determines the cyclic occupancy energy minimum. M-11 selects exact rational lattice phases. M-12 classifies recurrence horizons. M-13 computes transported affine-cycle defects. M-14 composes exact quadratic costs under the ᑕ. observation contract. Each implementation states its bounded inputs in the returned scope; the full research theorems are cited separately.

The production result examples for M-02, M-03, M-04, M-05 and M-06 through M-14 can be independently replayed offline with:

```sh
speedrunpapi check examples/m02-tap-span.math examples/m02-tap-span.result.json
speedrunpapi check examples/m03-affine-inverse.math examples/m03-affine-inverse.result.json
speedrunpapi check examples/m04-two-stage.math examples/m04-two-stage.result.json
speedrunpapi check examples/m06-shared-input.math examples/m06-shared-input.result.json
speedrunpapi check examples/m05-cascade.math examples/m05-cascade.result.json
speedrunpapi check examples/m07-rank35.math examples/m07-rank35.result.json
speedrunpapi check examples/m08-signed20.math examples/m08-signed20.result.json
speedrunpapi check examples/m09-binary-word.math examples/m09-binary-word.result.json
speedrunpapi check examples/m10-cyclic-energy.math examples/m10-cyclic-energy.result.json
speedrunpapi check examples/m11-lattice-phase.math examples/m11-lattice-phase.result.json
speedrunpapi check examples/m12-damped-horizon.math examples/m12-damped-horizon.result.json
speedrunpapi check examples/m13-affine-cycle.math examples/m13-affine-cycle.result.json
speedrunpapi check examples/m14-taa-cost.math examples/m14-taa-cost.result.json
```

These result bundles came from funded technical-test jobs in production. They carry original source digests and exact independent mathematical evidence. They do not represent external card payments. New hosted jobs require an API key with credits.

A [replayable production ONNX proof](proofs/hosted-onnx-production-20261110/) accompanies this release. The source, candidate, cost decision, transformation proof and independent checker are available to inspect. Local scans remain free and offline.

## Portable ᑕ. proof demonstration

[Exact carry-state contraction, 4,096 → 6 retained states](proofs/carry-frontier-4096/) is a complete portable evidence packet. It preserves the declared high-result observations of six modular additions for **all admissible lower-prefix inputs and every high suffix**. The 682.7× factor describes the reduction in retained states, not a CPU speedup.

The original source, mathematical candidate, separate verifier source, exact input/claim digests and Ed25519 laboratory receipt travel together. A reviewer can run the independent checker with Python 3.11 and Node 20+:

`python3 proofs/carry-frontier-4096/verifier/verify.py`

This mathematical reproduction requires no Colony account, private optimizer, or network access. Its ephemeral Ed25519 signature is a laboratory attestation; commercial certificates and third-party challenge acceptance have separate issuance and review requirements. The [proof workflow](.github/workflows/portable-proof.yml) replays it on GitHub Actions. Additional source-bound operator evidence can be published beside this example when accepted externally.
