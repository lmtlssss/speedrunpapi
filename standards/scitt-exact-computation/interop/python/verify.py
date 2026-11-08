#!/usr/bin/env python3
"""Independent exact-evidence verifier for the TAA SCITT test profile.

Requires cbor2 and cryptography. Does not import speedrunpapi or the issuer.
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path

import cbor2
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

HERE = Path(__file__).resolve().parents[1]
PROFILE = "taa.exact-computation-claim.v1"
ISSUER = "urn:taa:interop:issuer:test-only"
KID = b"taa-interop-test-01"


class Rejected(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Rejected(message)


def sha(data):
    return hashlib.sha256(data).digest()


def compose(first, second):
    a, b, u, v, w = first
    c, d, p, q, r = second
    return [c * a, c * b + d, u + p * a * a,
            v + 2 * p * a * b + q * a,
            w + p * b * b + q * b + r]


def check_predicate(predicate, artifact, evidence, verdict):
    if predicate == "urn:taa:finite-trace-preservation:v1":
        require(verdict == "certified", "unexpected trace verdict")
        s = artifact
        states, inputs = s["states"], s["inputs"]
        pi, nxt, obs = s["pi"], s["next"], s["observations"]
        rnext, robs = s["reduced_next"], s["reduced_observations"]
        q = len(rnext)
        require(len(states) > 0 and len(inputs) > 0 and q > 0, "empty domain")
        require(len(pi) == len(states) and set(pi) == set(range(q)), "not surjective")
        require(len(nxt) == len(states) and len(obs) == len(states), "state extent")
        require(len(robs) == q, "reduced extent")
        for i in range(q):
            require(len(rnext[i]) == len(inputs) and len(robs[i]) == len(inputs),
                    "reduced input extent")
        for i in range(len(states)):
            require(len(nxt[i]) == len(inputs) and len(obs[i]) == len(inputs),
                    "input extent")
            for j in range(len(inputs)):
                k = nxt[i][j]
                require(type(k) is int and 0 <= k < len(states), "transition range")
                require(pi[k] == rnext[pi[i]][j], "transition preservation")
                require(obs[i][j] == robs[pi[i]][j], "observation preservation")
        require(evidence == {"checked_pairs": len(states) * len(inputs),
                             "finite_trace_preserved": True}, "trace evidence")
    elif predicate == "urn:taa:affine-cost-composition:v1":
        require(verdict == "certified", "unexpected affine verdict")
        intervals = artifact["intervals"]
        require(len(intervals) == 3 and all(len(x) == 5 and
                all(type(z) is int for z in x) for x in intervals), "affine input")
        left = compose(compose(intervals[0], intervals[1]), intervals[2])
        right = compose(intervals[0], compose(intervals[1], intervals[2]))
        require(left == right, "associativity")
        require(evidence == {"composed": left, "associative": True}, "affine evidence")
    elif predicate in ("urn:taa:output-uniqueness:v1",
                       "urn:taa:witness-uniqueness:v1"):
        fibers = artifact["fibers"]
        require(len(fibers) > 0, "empty fibers")
        outputs = []
        witnesses = []
        for fiber in fibers:
            items = fiber["witnesses"]
            ids = [x["id"] for x in items]
            require(len(items) > 0 and len(ids) == len(set(ids)), "witness identifiers")
            outputs.append(len(set(x["output"] for x in items)))
            witnesses.append(len(items))
        if predicate.endswith("output-uniqueness:v1"):
            require(verdict == "certified" and all(n == 1 for n in outputs),
                    "output not unique")
            require(evidence == {"output_counts": outputs,
                                 "witness_counts": witnesses}, "output evidence")
        else:
            require(verdict == "broken" and any(n > 1 for n in witnesses),
                    "no counterexample to witness uniqueness")
            first = next(i for i, n in enumerate(witnesses) if n > 1)
            require(evidence == {"input": fibers[first]["input"],
                                 "witness_ids": [x["id"] for x in fibers[first]["witnesses"]]},
                    "witness counterexample")
    else:
        raise Rejected("unregistered predicate")


def verify_statement(raw, artifact_bytes, evidence_bytes):
    try:
        value = cbor2.loads(raw)
        require(isinstance(value, cbor2.CBORTag) and value.tag == 18, "COSE tag 18")
        require(cbor2.dumps(value, canonical=True) == raw, "non-deterministic COSE")
        fields = value.value
        require(isinstance(fields, (list, tuple)) and len(fields) == 4, "COSE_Sign1 extent")
        protected, unprotected, payload, signature = fields
        require(isinstance(protected, bytes) and isinstance(payload, bytes),
                "COSE bytes")
        require(isinstance(signature, bytes) and len(signature) == 64, "signature bytes")
        require(unprotected == {}, "unexpected unprotected headers")
        header = cbor2.loads(protected)
        require(cbor2.dumps(header, canonical=True) == protected, "protected encoding")
        require(header == {1: -8, 3: "application/cbor", 4: KID,
                           15: {1: ISSUER, 2: "urn:taa:interop:artifact"}},
                "protected headers or trust identity")
        statement = cbor2.loads(payload)
        require(cbor2.dumps(statement, canonical=True) == payload, "payload encoding")
        require(set(statement.keys()) == {1, 2, 3, 4, 5, 6}, "profile keys")
        require(statement[1] == PROFILE, "profile version")
        public = base64.b64decode((HERE / "test-public-key.base64").read_text().strip())
        tbs = cbor2.dumps(["Signature1", protected, b"", payload], canonical=True)
        try:
            Ed25519PublicKey.from_public_bytes(public).verify(signature, tbs)
        except Exception as exc:
            raise Rejected("COSE issuer signature invalid") from exc
        art, claim, verifier, ev = (statement[i] for i in (2, 3, 4, 5))
        require(set(art) == {1, 2, 3} and art[1] == "sha-256" and
                art[2] == sha(artifact_bytes) and art[3] == "application/json",
                "artifact digest or type")
        require(set(verifier) == {1, 2, 3, 4} and
                verifier[1] == "taa-reference-python-independent" and
                verifier[2] == "1.0.0" and verifier[3] == "sha-256" and
                verifier[4] == sha(Path(__file__).read_bytes()), "verifier identity")
        require(set(ev) == {1, 2, 4} and ev[1] == "sha-256" and
                ev[2] == sha(evidence_bytes) and ev[4] == "application/json",
                "evidence digest or type")
        require(set(claim) == {1, 2, 3, 4, 5} and
                claim[2] == "finite-exact-domain" and claim[4] == "full-domain-check" and
                claim[5] == [], "claim extent")
        artifact = json.loads(artifact_bytes)
        evidence = json.loads(evidence_bytes)
        check_predicate(claim[1], artifact, evidence, claim[3])
        return {"predicate": claim[1], "verdict": claim[3], "verified": True}
    except (KeyError, IndexError, TypeError, json.JSONDecodeError, ValueError) as exc:
        if isinstance(exc, Rejected):
            raise
        raise Rejected(str(exc)) from exc


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", default=str(HERE / "vectors/manifest.json"))
    parser.add_argument("--negative", action="store_true")
    args = parser.parse_args()
    manifest_path = Path(args.manifest)
    manifest = json.loads(manifest_path.read_text())
    passed = []
    for item in manifest["vectors"]:
        base = manifest_path.parent
        raw = (base / item["cose"]).read_bytes()
        art = (base / item["artifact"]).read_bytes()
        ev = (base / item["evidence"]).read_bytes()
        record = verify_statement(raw, art, ev)
        require(record["predicate"] == item["predicate"], "manifest predicate mismatch")
        passed.append(record)
        if args.negative:
            tests = [
                ("mutated signature", raw[:-1] + bytes([raw[-1] ^ 1]), art, ev),
                ("mutated source", raw, art + b" ", ev),
                ("mutated evidence", raw, art, ev + b" "),
                ("corrupt COSE", b"\x00" + raw[1:], art, ev),
            ]
            for label, forged, source, proof in tests:
                try:
                    verify_statement(forged, source, proof)
                    raise AssertionError("accepted " + label)
                except Rejected:
                    pass
    print(json.dumps({"passed": len(passed),
                      "negative_rejections": 4 * len(passed) if args.negative else 0,
                      "records": passed}))


if __name__ == "__main__":
    main()
