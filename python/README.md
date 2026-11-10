# speedrunpapi for Python

The Python package supplies the same bundled ᑕ. analyzer as the npm and browser distributions. It requires Node.js 20 or later on `PATH` and works offline for local scans.

Install with `pip install speedrunpapi` for the free scanner and hosted job commands, or `pip install 'speedrunpapi[onnx]'` to include the independent ONNX checker dependencies. Then run `speedrunpapi scan circuit.circom --json` or `speedrunpapi version`. Node.js 20+ must be installed on `PATH`. PyPI uses the repository's trusted publisher. The wheel includes the JavaScript client and the Python independent checker; it does not download executable code at run time.

The default JSON output carries proof data without paper citations. Add `--references` when research provenance is needed; source rechecking supports both forms.

Local scans and independent replay are free. Hosted jobs require a funded Colony API key. Use `speedrunpapi quote model.onnx`, then `speedrunpapi optimize model.onnx --out candidate.onnx --proof-dir proof`, then `speedrunpapi verify-onnx proof/source.onnx proof/artifacts` to check the delivered candidate offline. A paid signed certificate requires a Colony API key. Native Bitcoin Script assembly/bytecode supports alternate-stack transfer and hash opcodes; RV32IM v2 records branches, jumps, aligned word loads and stores. BN254 R1CS v1 checks coupled full-rank linear constraints and exact square-zero elimination. Use `speedrunpapi verify result.json --source input.file` for an independent source recheck. Unsupported code and rank-deficient systems return `Unknown`.
