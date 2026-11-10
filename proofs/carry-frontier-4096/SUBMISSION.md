# ᑕ. · Exact engineering evidence packet

This packet contains an original source, an independently checked mathematical
result, and the reproducible evidence that establishes its **declared scope**.
The candidate and all declared proof prerequisites are content-addressed.

## Observed result

- Claim: For all low prefixes and all high suffixes, preserve the high (width-cut) result bits of each independent unsigned modular addition; low result bits are excluded.
- Verdict: Certified
- Target: No external target registered
- Original digest: sha256:6b6c517d18cc0c86371eb62ed946a8d7acbc3b1ddde179225e32fc0539f891cd
- Independent verifier: engine/packages/colony-math/independent_verify.py
- Qualification: Only the declared observation relation; no whole-program lowering or hardware speedup claim

## Independent reproduction

The full packet is checked locally using:

    python verifier/verify.py

All evidence is bound to the exact original bytes. The receipt has a
local ephemeral Ed25519 **laboratory** signature. It is not a production
Colony certificate and establishes no third-party signer identity.

## Integration / claim boundary

A successful mathematical checker establishes the claim stated above.
Upstream reviewers must still validate their full integration requirements,
licenses and execution environment. Any bounty award depends on the
program's independent eligibility and acceptance rules.

Proof: ᑕ. · https://colony.technology/proofs
Verifier distribution: https://github.com/lmtlssss/speedrunpapi
