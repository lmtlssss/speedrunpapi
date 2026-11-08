#!/usr/bin/env python3
"""Reject validly signed COSE messages whose exact computational evidence is false."""
import copy
import hashlib
import json
from pathlib import Path
import cbor2
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from verify import Rejected, verify_statement

HERE = Path(__file__).resolve().parents[1]
manifest = json.loads((HERE / "vectors/manifest.json").read_text())
private = Ed25519PrivateKey.from_private_bytes(bytes(range(32)))


def resign(raw, artifact_bytes, evidence_bytes, new_claim=None):
    data = cbor2.loads(raw)
    protected, _, payload_bytes, _ = data.value
    payload = dict(cbor2.loads(payload_bytes))
    artifact = dict(payload[2])
    evidence = dict(payload[5])
    artifact[2] = hashlib.sha256(artifact_bytes).digest()
    evidence[2] = hashlib.sha256(evidence_bytes).digest()
    payload[2], payload[5] = artifact, evidence
    if new_claim:
        claim = dict(payload[3])
        claim.update(new_claim)
        payload[3] = claim
    pb = cbor2.dumps(payload, canonical=True)
    sig = private.sign(cbor2.dumps(["Signature1", protected, b"", pb],
                                   canonical=True))
    return cbor2.dumps(cbor2.CBORTag(18, [protected, {}, pb, sig]),
                       canonical=True)


rejected = []
for item in manifest["vectors"]:
    d = HERE / "vectors"
    raw = (d / item["cose"]).read_bytes()
    artifact = json.loads((d / item["artifact"]).read_bytes())
    evidence = json.loads((d / item["evidence"]).read_bytes())
    if item["name"] == "finite-trace":
        artifact["observations"][0][0] = 99
    elif item["name"] == "affine-cost":
        evidence["composed"][2] += 1
    elif item["name"] == "output-unique":
        artifact["fibers"][0]["witnesses"][1]["output"] = 88
    else:
        evidence["witness_ids"][0] = "forged"
    a = (json.dumps(artifact, separators=(",", ":")) + "\n").encode()
    e = (json.dumps(evidence, separators=(",", ":")) + "\n").encode()
    forged = resign(raw, a, e)
    try:
        verify_statement(forged, a, e)
        raise AssertionError("accepted signed false mathematics " + item["name"])
    except Rejected:
        rejected.append(item["name"])
    if item["name"] == "witness-nonunique":
        restored_art = (d / item["artifact"]).read_bytes()
        restored_ev = (d / item["evidence"]).read_bytes()
        false_verdict = resign(raw, restored_art, restored_ev, {3: "certified"})
        try:
            verify_statement(false_verdict, restored_art, restored_ev)
            raise AssertionError("accepted falsely certified witness uniqueness")
        except Rejected:
            rejected.append("false-certified-witness-uniqueness")
print(json.dumps({"signed_false_claims_rejected": len(rejected),
                  "cases": rejected}))
