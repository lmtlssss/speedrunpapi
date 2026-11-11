# speedrunpapi for Python

Output-determinism analysis for Circom circuits and R1CS. This package installs the same bundled command-line tool as the npm distribution, plus an independent Python checker for its reports.

```sh
pip install speedrunpapi
speedrunpapi scan circuit.circom
speedrunpapi scan circuit.circom --report circuit.report.json
python -m speedrunpapi.verifiers.determinism circuit.r1cs circuit.report.json
```

The scanner needs Node.js 20 or later on `PATH`, and the circom compiler for `.circom` input. The checker (`speedrunpapi.verifiers.determinism`) needs only the Python standard library: it parses the R1CS itself and replays the derivation or re-evaluates the counterexample without the scanner.

Full documentation: https://github.com/lmtlssss/speedrunpapi

Versions before 0.7.0 classified sources by template name and keyword and could report `Certified` for a circuit whose outputs were unconstrained. Those results were not proofs. If you relied on one, scan again.

`pip install 'speedrunpapi[onnx]'` adds the dependencies of the separate ONNX checker used by the hosted optimization jobs.
