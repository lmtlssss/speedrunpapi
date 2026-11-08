#!/usr/bin/env python3
"""Independently reconstruct and sign each Node-produced COSE vector with Python."""
import json
from pathlib import Path
import cbor2
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

HERE = Path(__file__).resolve().parents[1]
manifest = json.loads((HERE / "vectors/manifest.json").read_text())
private = Ed25519PrivateKey.from_private_bytes(bytes(range(32)))
for item in manifest["vectors"]:
    raw = (HERE / "vectors" / item["cose"]).read_bytes()
    decoded = cbor2.loads(raw)
    assert decoded.tag == 18
    protected, unprotected, payload, signature = decoded.value
    to_sign = cbor2.dumps(["Signature1", protected, b"", payload], canonical=True)
    new_signature = private.sign(to_sign)
    assert new_signature == signature, item["name"] + ": signature mismatch"
    encoded = cbor2.dumps(cbor2.CBORTag(
        18, [protected, dict(unprotected), payload, new_signature]), canonical=True)
    assert encoded == raw, item["name"] + ": deterministic encoding mismatch"
    (HERE / "vectors" / (item["name"] + ".python.cose")).write_bytes(encoded)
print(json.dumps({"python_reencoded_and_signed": len(manifest["vectors"]),
                  "bit_exact_to_node": True}))
