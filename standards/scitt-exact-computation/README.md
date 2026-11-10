# Exact Computation Claim Profile for SCITT

**Individual proposal 00 · 8 November 2026 · lmtlssss🜐**

This directory publishes a proposed wire profile for portable exact-computation certificates.

- [Technical profile](SCITT_EXACT_COMPUTATION_PROFILE.md): signed statement, deterministic CBOR claim map, verification procedure, security and privacy.
- [Internet-Draft source](draft-lmtlssss-scitt-exact-computation-00.xml): RFCXML v3 source prepared for IETF Datatracker.
- [Rendered Internet-Draft](draft-lmtlssss-scitt-exact-computation-00.txt): text rendered with the IETF `xml2rfc` author tool.
- [COSE/CBOR vectors and independent verification](interop/): four registered predicates, issuer and verifier implementations in Node and Python, negative evidence cases.
- [Mathematical term and exact replay](https://github.com/lmtlssss/math/tree/main/mathematics/discrete-mathematics/exact-state-contraction): definition of ᑕ. (TAA), paper and verifier.

The proposal uses the SCITT architecture in [RFC 9943](https://www.rfc-editor.org/rfc/rfc9943.html) and COSE receipt structure in [RFC 9942](https://www.rfc-editor.org/rfc/rfc9942.html). The certificate has three distinct layers: an issuer signature, an independently checked computational claim, and an optional transparency receipt.

**Status.** Open proposal on GitHub. The RFCXML source has passed an `xml2rfc` text render; the submission-readiness workflow rechecks the render and the independent COSE/CBOR vectors. It has not been submitted or adopted by the IETF. The [IETF submission portal](https://datatracker.ietf.org/submit/) is closed during the November meeting interval and is scheduled to reopen after 14 November 2026 at 23:59 PST (15 November at 02:59 Toronto time). An IETF Internet-Draft submission requires the author's confirmed submission identity and IETF processing.

**Executable interoperability.** [Four registered predicates, deterministic COSE/CBOR vectors, independent Python and Node verification](interop/). Both implementations reproduce the signed statements byte-for-byte and reject altered statements. The Python verifier also rejects five correctly re-signed false mathematical claims. The test issuer and key are public fixtures; live JSON certificates remain a separate format.

This is a vendor-independent protocol proposal. Issuers can sign their own claims; relying parties check the evidence under an explicit trust policy. No existing JSON signing endpoint is represented as implementing this COSE profile.

## Submission package · 15 November 2026

The [submission-readiness checklist](SUBMISSION_READINESS.md) identifies the exact RFCXML file, rendered draft, independent verification suite, and external Datatracker confirmation step. The submitted draft remains an individual proposal until the Datatracker publishes a submission receipt.
