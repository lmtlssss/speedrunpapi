# Internet-Draft submission readiness — 15 November 2026

## Artifact

- Draft name: `draft-lmtlssss-scitt-exact-computation-00`.
- Source: [RFCXML v3](draft-lmtlssss-scitt-exact-computation-00.xml).
- Rendered review copy: [plain text](draft-lmtlssss-scitt-exact-computation-00.txt).
- Technical profile: [SCITT Exact Computation Claim Profile](SCITT_EXACT_COMPUTATION_PROFILE.md).
- Interoperability evidence: [four finite-domain predicates with Node and Python verification](interop/).
- Revision: `-00`; informational, individual contribution, Security area.
- Authorship: the pseudonymous name printed in RFCXML. The author confirms the Datatracker submission identity during upload.

## Reproducible readiness gate

From `interop/node`, run `npm ci --ignore-scripts`, `npm run vectors`, the four Python scripts listed in `interop/README.md`, and `npm run verify`. Render RFCXML with `xml2rfc --text`. The GitHub [SCITT readiness workflow](../../.github/workflows/scitt-readiness.yml) runs these checks on changes. A green workflow and matching source revision are the engineering gate.

The signed test statements use a published **test-only** Ed25519 key. Production JSON certificates and the COSE profile remain distinct implementations. The vectors cover their declared finite domains. This draft does not claim an IETF endorsement, a transparency receipt, or broader circuit-verifier registration.

## Submission

The [IETF submission portal](https://datatracker.ietf.org/submit/) lists the reopening after **14 November 2026 23:59 Pacific Standard Time**, which is **15 November 2026 02:59 Eastern Standard Time**. Submit this RFCXML source when the portal accepts uploads, and complete the author confirmation and Datatracker processing. Record the Datatracker document URL and submission receipt here after acceptance.

Status on 10 November: **source package prepared for the submission window; Datatracker publication pending**.
