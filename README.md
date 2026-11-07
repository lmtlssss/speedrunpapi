# ᑕ. exact arithmetic circuit verification

[Live race](https://colony.technology/demo) · [Proofs](https://colony.technology/proofs) · [Packs](https://colony.technology/packs) · [API](https://colony.technology/api)

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
pip install https://github.com/lmtlssss/speedrunpapi/releases/download/v0.3.1/speedrunpapi-0.3.1-py3-none-any.whl
speedrunpapi scan circuit.circom --json
```

## Three verdicts

- `Certified` — a supported constraint pattern has one output under its stated input and range conditions.
- `Broken` — a supported pattern admits distinct witnesses; the result includes a counterexample.
- `Unknown` — the source needs a supported adapter or a complete constraint graph.

Supported inputs include recognized Circom, Verilog, int8 and ONNX source patterns, plus bounded `carry-graph-v1` JSON for BitVM, zkVM and normalized R1CS. Raw Bitcoin Script, binary R1CS and native zkVM traces need source frontends and currently return `Unknown`. The exact mathematical graph is the certification scope until the source compiler is bound.

The source-bound Circom examples also cover exact AND, Mux1 field arithmetic and a five-bit LessThan constraint: `examples/and.circom`, `examples/mux.circom` and `examples/compare.circom`. The verifier checks the complete recognized constraints and returns `Unknown` for altered or incomplete templates.

Try `speedrunpapi scan examples/compare.circom --json` or `speedrunpapi scan examples/modsum-broken.circom --json`.

## GitHub Action

```yaml
- uses: actions/checkout@v4
- uses: lmtlssss/speedrunpapi@v0.3.1
  with:
    file: circuits/main.circom
```

The Action scans checked-out source, fails on `Broken`, warns on `Unknown`, and uploads the result. Add an optional `api_key` to request a signed certificate. Source is analyzed again by the hosted API before signing.

To display the scan workflow status in a repository README, save the above steps in `.github/workflows/speedrunpapi.yml`, then add:

```markdown
[![ᑕ. scan](https://github.com/OWNER/REPO/actions/workflows/speedrunpapi.yml/badge.svg)](https://github.com/OWNER/REPO/actions/workflows/speedrunpapi.yml)
```

Replace `OWNER/REPO` with that repository. The badge shows the workflow status. An issued, source-bound Certified certificate has its own public registry URL.

## Packages

`speedrunpapi@0.3.1` is live on [npm](https://www.npmjs.com/package/speedrunpapi). The Python wheel is in the [v0.3.1 release](https://github.com/lmtlssss/speedrunpapi/releases/tag/v0.3.1); PyPI publication follows trusted-publisher registration.

The free analyzer is bundled here. The paid API and signing service run at [api.colony.technology](https://api.colony.technology). [Terms](https://colony.technology/terms) · [Source release notes](https://github.com/lmtlssss/speedrunpapi/releases).

This public distribution contains the standalone client and its Action. Colony's private service infrastructure, billing, credentials and internal research remain separate.
