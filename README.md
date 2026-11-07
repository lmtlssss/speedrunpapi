# ᑕ. — exact arithmetic circuit verification

[Live race](https://colony.technology/demo) · [Proofs](https://colony.technology/proofs) · [Packs](https://colony.technology/packs) · [API](https://colony.technology/api)

Paste source, press ᑕ., get a scoped verdict. Local scanning runs on your machine, without an account or API key.

The headline demo uses the pinned Circomlib **SHA-256 compression** source. The recorded Picus run reached its 180-second timeout; the live ᑕ. browser analyzer returns a scoped compositional result in microseconds. The 21 controlled G1 comparisons, source and timings are linked from [proofs](https://colony.technology/proofs). The recorded Picus result is identified as recorded.

## Install

Node.js 20 or later:

```sh
npm install -g colony-taa
colony scan circuit.circom --json
```

The npm registry release is pending. Until it is published, install the public repository directly:

```sh
npm install -g github:lmtlssss/colony-taa
colony scan circuit.circom --json
```

Or download the same standalone bundle:

```sh
curl -fsSL https://colony.technology/colony-cli.mjs -o colony.mjs
node colony.mjs scan circuit.circom --json
```

Python 3.9+ and Node.js 20+:

```sh
pip install colony-taa
colony scan circuit.circom --json
```

The PyPI registry release is pending. The `python/` directory is an installable local package using the same bundled engine.

## Three verdicts

- `Certified` — a supported constraint pattern has one output under its stated input and range conditions.
- `Broken` — a supported pattern admits distinct witnesses; the result includes a counterexample.
- `Unknown` — the source needs a supported adapter or a complete constraint graph.

Supported inputs include recognized Circom, Verilog, int8 and ONNX source patterns, plus bounded `carry-graph-v1` JSON for BitVM, zkVM and normalized R1CS. Raw Bitcoin Script, binary R1CS and native zkVM traces need source frontends and currently return `Unknown`. The exact mathematical graph is the certification scope until the source compiler is bound.

Try `colony scan examples/modsum-safe.circom --json` or `colony scan examples/modsum-broken.circom --json`.

## GitHub Action

```yaml
- uses: actions/checkout@v4
- uses: lmtlssss/colony-taa@v0.2.0
  with:
    file: circuits/main.circom
```

The Action scans checked-out source, fails on `Broken`, warns on `Unknown`, and uploads the result. Add an optional `api_key` to request a signed certificate. Source is analyzed again by the hosted API before signing.

The free analyzer is bundled here. The paid API and signing service run at [api.colony.technology](https://api.colony.technology). [Terms](https://colony.technology/terms) · [Source release notes](https://github.com/lmtlssss/colony-taa/releases).

This public distribution contains the standalone client and its Action. Colony's private service infrastructure, billing, credentials and internal research remain separate.
