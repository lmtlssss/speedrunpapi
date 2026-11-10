# Production ONNX proof · 10 November 2026

A synthetic ONNX model was submitted to the live `api.colony.technology` optimization service through a funded TEST entitlement. The private `colony-onnx-runner` Cloudflare container produced the candidate and proof artifacts. The independently implemented verifier replayed the delivered result and accepted its registered exact-stage contract.

- Hosted job ID: `fe734160-9a40-4669-ab33-169a94943ef8`
- Original source digest: `sha256:589a59ecbda74775cfa4aad73e2444e3689bbb1829712aa5b3ec4da0b7aff2a5`
- Plan digest: `sha256:bf4be4f9ea39d43cb5a85d6bc31d76c538e9d048ac5a8c0516f25f7569cc0ddc`
- Delivered ONNX digest: `sha256:adf8cf00d9eb0286bef42db9d10c6d1069ef7b938230a98b7b64754d78b2faee`
- Verified exact transformation stages: `1`
- Provider measurement: `CPUExecutionProvider` on the host that ran the optimization; timing is a measured observation, not an exact hardware-cost theorem.

Run independent replay from the repository root after installing Python, `onnx` and `numpy`:

`node bin/speedrunpapi.mjs verify-onnx proofs/hosted-onnx-production-20261110/source.onnx proofs/hosted-onnx-production-20261110/artifacts`

The verifier's six source files are in `verifiers/onnx/`. It uses the supplied original ONNX bytes, plan, executable candidate, each stage proof, and the retained cost decision. It uses neither the private optimizer nor a Colony account, API key or network connection. The TEST credit ledger and customer credentials are outside this portable mathematical packet.

The source of the production test and its signed receipt remain in the private Colony repository (`ops/test-uce-production-onnx-live.mts` and `ops/receipts/UCE-R06-LIVE-ONNX-20261110.json`). The public packet proves the declared exact ONNX result independently; it is not a claim of generic performance improvement on every CPU.
