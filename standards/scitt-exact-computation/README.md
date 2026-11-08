# Exact Computation Claim Profile for SCITT

**Individual proposal 00 · 8 November 2026 · lmtlssss🜐**

This directory publishes a proposed wire profile for portable exact-computation certificates.

- [Technical profile](SCITT_EXACT_COMPUTATION_PROFILE.md): signed statement, deterministic CBOR claim map, verification procedure, security and privacy.
- [Internet-Draft source](draft-lmtlssss-scitt-exact-computation-00.xml): RFCXML v3 source prepared for IETF Datatracker.
- [Rendered Internet-Draft](draft-lmtlssss-scitt-exact-computation-00.txt): text rendered with the IETF `xml2rfc` author tool.
- [Mathematical term and exact replay](https://github.com/lmtlssss/math/tree/main/mathematics/discrete-mathematics/exact-state-contraction): definition of ᑕ. (TAA), paper and verifier.

The proposal uses the SCITT architecture in [RFC 9943](https://www.rfc-editor.org/rfc/rfc9943.html) and COSE receipt structure in [RFC 9942](https://www.rfc-editor.org/rfc/rfc9942.html). The certificate has three distinct layers: an issuer signature, an independently checked computational claim, and an optional transparency receipt.

**Status.** Open proposal on GitHub. The RFCXML source has passed an `xml2rfc` text render. It has not been submitted or adopted by the IETF. The [IETF submission portal](https://datatracker.ietf.org/submit/) is closed during the November meeting interval and is scheduled to reopen after 14 November 2026 Pacific time. An IETF Internet-Draft submission requires the author's confirmed submission identity and IETF processing.

**Next technical gates.** Publish independent COSE/CBOR interoperability vectors; prove exact evidence checking for each registered predicate; submit the individual Internet-Draft when the portal reopens.

This is a vendor-independent protocol proposal. Issuers can sign their own claims; relying parties check the evidence under an explicit trust policy. No existing JSON signing endpoint is represented as implementing this COSE profile.
