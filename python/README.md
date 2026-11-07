# speedrunpapi for Python

The Python package supplies the same bundled ᑕ. analyzer as the npm and browser distributions. It requires Node.js 20 or later on `PATH` and works offline for local scans.

Install the [v0.3.0 wheel](https://github.com/lmtlssss/speedrunpapi/releases/tag/v0.3.0) with `pip install https://github.com/lmtlssss/speedrunpapi/releases/download/v0.3.0/speedrunpapi-0.3.0-py3-none-any.whl`, then run `speedrunpapi scan circuit.circom --json` or `speedrunpapi version`. PyPI publication follows the trusted-publisher registration. The package invokes its bundled JavaScript engine; it does not download executable code at run time.

Local scans are free. A paid signed certificate requires a Colony API key. Native BitVM/zkVM source and binary R1CS frontends are on the adapter roadmap; normalized carry graphs work today.
