# Independent determinism checker

`determinism_check.py` re-verifies a speedrunpapi report against the R1CS it is about. It is a second implementation: Python standard library only, its own R1CS parser, no code shared with the scanner.

```sh
python3 determinism_check.py circuit.r1cs circuit.report.json
```

It prints one JSON object and exits `0` when the report's verdict is verified (or the verdict is `Unknown`, which claims nothing), `1` when verification fails, `2` on usage or I/O errors.

- `Certified`: every step of the derivation is replayed against the constraints it cites, and every output wire must end up determined.
- `Broken`: both witnesses are evaluated against every constraint; they must agree on every input wire and differ on an output.
- Which wires are inputs is read from the R1CS. A report cannot add to that set.
- Assumptions declared in the report (input signals assumed binary) are applied as extra constraints and are part of what is verified.
