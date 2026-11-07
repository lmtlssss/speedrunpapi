# speedrunpapi for Python

The Python package supplies the same bundled ᑕ. analyzer as the npm and browser distributions. It requires Node.js 20 or later on `PATH` and works offline for local scans.

Install with `pip install speedrunpapi`, then `speedrunpapi scan circuit.circom --json` or `speedrunpapi version`. The package invokes its bundled JavaScript engine; it does not download executable code at run time.

Local scans are free. A paid signed certificate requires a Colony API key. Native BitVM/zkVM source and binary R1CS frontends are on the adapter roadmap; normalized carry graphs work today.
