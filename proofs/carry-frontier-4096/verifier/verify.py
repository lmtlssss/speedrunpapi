#!/usr/bin/env python3
"""ᑕ. Standalone proof packet verifier.

No optimizer, Colony account, network connection or private repository.
The accompanying ONNX independent checkers are derived from their
standalone reference modules, without proposal-generator imports.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parent.parent
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))

def sha(raw):return "sha256:"+hashlib.sha256(raw).hexdigest()
def ensure(condition,message):
    if not condition:raise ValueError(message)

def inspect():
    packet=json.loads((ROOT/"receipt.json").read_bytes())
    ensure(packet.get("schema")=="colony.operator-packet.v1","Packet contract unrecognized")
    ensure(packet.get("signer_claim")=="ephemeral_laboratory_only","Signer scope unrecognized")
    manifest=packet.get("files")
    ensure(type(manifest) is list and manifest,"File digest manifest required")
    listed={}
    for item in manifest:
        name=item["name"]
        ensure(type(name) is str and not name.startswith("/") and ".." not in Path(name).parts,
               "Unsafe file path")
        ensure(name not in listed,"Duplicate file manifest")
        f=(ROOT/name).resolve()
        ensure(f.is_relative_to(ROOT) and f.is_file(),"Missing or outside-bound file")
        raw=f.read_bytes()
        ensure(len(raw)==item["bytes"] and sha(raw)==item["digest"],"File bytes modified: "+name)
        listed[name]=True
    actual={f.relative_to(ROOT).as_posix() for f in ROOT.rglob("*")
            if f.is_file() and f.name not in ("receipt.json","signature.json") and "__pycache__" not in f.parts}
    ensure(actual==set(listed),"Unexpected file added or missing")
    cp=subprocess.run(["node",str(HERE/"verify_signature.mjs"),str(ROOT)],
                      capture_output=True,text=True,timeout=12)
    ensure(cp.returncode==0,"Laboratory signature verification failed")
    kind=packet["kind"]
    result=packet["result"]
    if kind=="onnx":
        from onnx_plan import check as check_onnx
        data=(ROOT/"source.onnx").read_bytes()
        assets={f.name:f.read_bytes() for f in (ROOT/"artifacts").iterdir() if f.is_file()}
        verdict=check_onnx(data,assets)
        ensure(verdict["ok"],"Independent ONNX mathematical replay failed: "+verdict.get("reason",""))
        ensure(verdict["plan_digest"]==result["verified_execution_plan_digest"],"Plan digest changed")
    elif kind=="math":
        from independent_verify import verify_package
        verdict=verify_package((ROOT/"source.math").read_bytes(),
            json.loads((ROOT/"artifacts/proof.json").read_bytes()))
        ensure(verdict["ok"],"Independent finite mathematical relation rejected")
    elif kind=="rtl":
        from rtl_independent import verify
        verdict=verify((ROOT/"source.sv").read_bytes(),
            (ROOT/"source_pkg.sv").read_bytes(),
            (ROOT/"artifacts/candidate-dma.sv").read_bytes(),
            json.loads((ROOT/"artifacts/proof.json").read_bytes()))
        ensure(verdict["ok"],"Independent SMT/RTL transition proof rejected")
    else:raise ValueError("Unregistered packet domain")
    return {"ok":True,"scope":result["scope"],"kind":kind,
            "source_digest":result["original_digest"],
            "receipt_digest":sha((ROOT/"receipt.json").read_bytes()),
            "local_signature":True,"production_issuer":False,
            "independent_mathematics":True}

if __name__=="__main__":
    try:
        print(json.dumps(inspect(),sort_keys=True))
    except Exception as exc:
        print(json.dumps({"ok":False,"reason":type(exc).__name__+": "+str(exc)[:280]}))
        sys.exit(1)
