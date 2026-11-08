# SCITT exact-computation interoperability v1

Four registered, finite-domain predicates. Deterministic CBOR payloads. Tagged COSE_Sign1 with Ed25519. The same byte streams are produced by Node (`cbor` + built-in crypto) and Python (`cbor2` + `cryptography`). An independent Python checker verifies the claim from source and evidence bytes. Node also checks the four predicates independently.

| Predicate URI | Declared domain | Verification |
| --- | --- | --- |
| `urn:taa:finite-trace-preservation:v1` | Complete finite state/input table | Exhaustive transition + observation identities; surjective retained-state map |
| `urn:taa:affine-cost-composition:v1` | Three exact integer affine/quadratic intervals | Exact composition from both parenthesizations, including quadratic and linear cross-terms |
| `urn:taa:output-uniqueness:v1` | Explicit finite witness fibers | Enumerate distinct outputs per input; distinguish witness count |
| `urn:taa:witness-uniqueness:v1` | Explicit finite witness fibers | Reproduce two distinct witnesses for a single input; `broken` counterexample |

The registry is limited to these four predicates. The CLI's other source-format claims require their own named independent checkers before profile registration.

## Signed statement

- Media type: `application/scitt-statement+cose`. COSE tag 18, COSE_Sign1.
- Protected header: `alg=-8` (EdDSA), `ctyp=application/cbor`, `kid=bstr`, `CWT Claims=15` with issuer/subject.
- Payload: versioned deterministic CBOR map in the [profile](../SCITT_EXACT_COMPUTATION_PROFILE.md).
- Signed bytes: CBOR `["Signature1", body_protected, h'', payload]`.
- Binding: exact artifact, evidence and checker-file SHA-256 values; predicate, domain and verdict.
- Transparency receipt: absent in these test vectors. Future receipt checks use the external SCITT transparency service's trust policy.

All vectors use the public, fixed Ed25519 seed `00 01 ... 1f` and issuer `urn:taa:interop:issuer:test-only`. **The seed and issuer are test fixtures. These are never production credentials or production certificates.** The checker pins that test issuer and key.

## Reproduce

From `interop/node/`:

```sh
npm ci --ignore-scripts
npm run vectors
uv run --no-project --with cbor2 --with cryptography python3 ../python/verify.py --negative
uv run --no-project --with cbor2 --with cryptography python3 ../python/roundtrip.py
uv run --no-project --with cbor2 --with cryptography python3 ../python/negative_predicates.py
npm run verify
```

Expected results:

- 4 COSE statements generated and verified by Python.
- 4 Python-resigned CBOR statements with byte-identical signatures and envelopes.
- 4 Node verifications of Node statements and 4 of Python statements.
- 16 Python and 16 Node rejection checks for changed signature, source bytes, evidence bytes and envelope.
- 5 **correctly re-signed** false mathematical claims rejected by the independent checker.
- 4 registered predicate verdicts confirmed, including one `broken` witness-uniqueness claim.

## Failure modes exercised

Signature alteration; source-digest mismatch; evidence-digest mismatch; malformed COSE tagging; false transition identity; altered affine cross-term; two distinct outputs; forged witness counterexample; falsely claimed unique witnesses. Both readers also require deterministic CBOR, the protected issuer/key, checker implementation digest, and complete versioned claim map.

The independent check covers each declared finite domain. It does not imply arbitrary Circom/R1CS/BitVM/zkVM source verification by this reference suite. The existing JSON certificate API is a separate signing format.

[Manifest](vectors/manifest.json) · [Node issuer](node/generate.mjs) · [Node verifier](node/verify.mjs) · [Python verifier](python/verify.py) · [Python round-trip](python/roundtrip.py) · [Signed-false-claim cases](python/negative_predicates.py)
