# Exact Computation Claim Profile for SCITT

**Individual proposal 00 · 8 November 2026 · lmtlssss🜐**

## 1. Scope

This profile describes a signed statement about a computational artifact. A statement binds source bytes, a precisely named claim, the claim's input domain, a verification method, and evidence. The statement can be registered with a SCITT Transparency Service. The profile works for arithmetic circuits, formal models, software intermediate representations, and other computation artifacts whose claims have independent checking rules.

This text is a proposal for discussion. It is not an IETF standard. A published signed statement is an issuer claim. A successful evidence check is the basis for accepting its mathematical content.

## 2. SCITT transport

Use the **COSE_Sign1** Signed Statement format in RFC 9943. Its media type is `application/scitt-statement+cose`. Put the issuer (`iss`) and artifact subject (`sub`) in the protected COSE header parameter `15` (CWT Claims, RFC 9597). Bind an algorithm, issuer key ID, and payload content type in the protected header. Verify the signature according to COSE. A SCITT Transparency Service adds a receipt according to RFC 9942 and RFC 9943. A receipt proves registration under that service's policy.

For this initial proposal, the payload is a deterministic CBOR map and the protected content type is `application/cbor`. The payload contains a profile identifier. A future revision can request an application-specific media type after interoperability review.

## 3. Claim payload v1

The following is the profile's initial CDDL structure. Integers are the CBOR map keys, and the value of `1` is the exact profile identifier.

```cddl
exact-claim = {
  1: "taa.exact-computation-claim.v1",
  2: artifact,
  3: claim,
  4: verifier,
  5: evidence,
  6: tstr,                  ; issuance time, RFC 3339 UTC
  ? 7: tstr,                ; superseded statement identifier
}
artifact = {
  1: "sha-256",
  2: bstr .size 32,         ; digest of exact artifact bytes
  3: tstr,                  ; artifact media type
  ? 4: tstr,                ; public location, optional
}
claim = {
  1: tstr,                  ; predicate URI or stable identifier
  2: tstr,                  ; declared input domain
  3: "certified" / "broken" / "unknown",
  4: tstr,                  ; observation or witness contract
  5: [* tstr],              ; assumptions
}
verifier = {
  1: tstr,                  ; implementation identifier
  2: tstr,                  ; exact version
  3: "sha-256",
  4: bstr .size 32,         ; digest of verifier artifact
}
evidence = {
  1: "sha-256",
  2: bstr .size 32,         ; evidence digest
  ? 3: tstr,                ; public evidence location
  ? 4: tstr,                ; evidence media type
}
```

## 4. Meaning of the verdict

`certified` asserts that the verifier accepted the stated predicate, for the exact artifact digest and declared domain. `broken` asserts that the evidence contains a reproducible counterexample to the predicate. `unknown` states that the verifier did not establish either result under its current method and resource bounds. A `certified` output-uniqueness claim requires preservation of the possible output set. A witness-uniqueness claim also requires preservation of witness identity or multiplicity. Verification rules belong to the named predicate and checker specification. A SCITT receipt does not replace this check.

## 5. Independent verification

The relying party performs these actions in order:

1. Parse the COSE_Sign1 envelope and require the SCITT profile headers.
2. Identify the issuer trust anchor using the protected `iss` and `kid` fields.
3. Verify the COSE signature over the signed bytes.
4. Parse the payload. Reject unknown profile versions and duplicate keys.
5. Calculate SHA-256 over the supplied artifact bytes. Match the digest exactly.
6. Obtain the named verifier version. Match the verifier artifact digest.
7. Obtain the evidence bytes. Match the evidence digest.
8. Run the independent checker over the artifact, claim, assumptions, and evidence.
9. Verify each SCITT receipt against its chosen transparency service when transparency is required.
10. Accept only a verdict that matches the checker result and the local trust policy.

The source byte stream can stay private. In that case, a relying party can verify the issuer signature and receipt, but it cannot independently establish the artifact claim without the original bytes or a sufficient cryptographic proof.

## 6. Interoperability and migration

Different issuers can use the same payload profile. A verifier must check the named claim and evidence, not the issuer's brand. A self-signed statement can be valid under a relying party's local trust policy. Its signature does not by itself establish correctness. A statement signed with an HMAC key shared only with a central service does not provide third-party offline signature verification.

An implementation that signs a JSON certificate has a separate byte format and signature structure. This profile defines a **SCITT/COSE mapping**. An implementation claims conformance only after its COSE issuer and verifier satisfy this mapping and pass the corresponding interoperability tests.

## 7. Security and privacy

An issuer key can be compromised. A verifier can contain a bug. A claim can omit a necessary assumption. A revoked key or superseded statement must be resolved through the relying party's trust policy. Do not publish proprietary source in a public evidence field. Use exact digests for each artifact and each verifier version. An external URL is a retrieval hint; the digest is the binding. A receipt proves inclusion in one service's record and does not certify circuit correctness.

## 8. Standards path

The individual Internet-Draft source is `draft-lmtlssss-scitt-exact-computation-00.xml`. Its intended entry point is IETF Datatracker. On 8 November 2026, the IETF draft submission portal is closed for the IETF meeting interval and says it will reopen after 14 November (Pacific meeting time). Publication on GitHub is an open technical proposal. It is not a Datatracker submission.

## References

- RFC 9943, *An Architecture for Trustworthy and Transparent Digital Supply Chains*.
- RFC 9597, *CBOR Web Token (CWT) Claims in COSE Headers*.
- RFC 9942, *COSE Receipts*.
- RFC 9052, *CBOR Object Signing and Encryption (COSE): Structures and Process*.
- RFC 8610, *Concise Data Definition Language (CDDL)*.
- RFC 8032, *Edwards-Curve Digital Signature Algorithm (EdDSA)*.
- lmtlssss🜐, *ᑕ. — Exact State Contraction*, terminology proposal 1.0, 2026.

License: CC BY 4.0 for this proposal.
