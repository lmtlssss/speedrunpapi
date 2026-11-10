"""Independent end-to-end replay of an ONNX transformation artifact chain.

Source and all stage artifacts are read by digest, every stage is proved
without using the proposal generator, and final bytes equal the claimed final.
"""
import argparse
import hashlib
import json
from pathlib import Path

from independent_graph_checker import check as check_shape
from quantized_zero_independent import check as check_quantized
from quantized_column_independent import check as check_columns
from quantized_sparse_independent import check as check_sparse

SCHEMA="colony.inference-pipeline.v1"
CLAIM="Every admitted ONNX output remains identical under the ordered conjunction of stage observation contracts."
VERIFIER="colony.inference-pipeline-independent.v1"
CHECKERS={
    "onnx.static-metadata-graph.v1":(0,check_shape),
    "onnx.quantized-zero-matmul.v1":(1,check_quantized),
    "onnx.quantized-trailing-zero-columns.v1":(2,check_columns),
    "onnx.quantized-sparse-columns.v1":(3,check_sparse)
}
def digest(raw):
    return "sha256:"+hashlib.sha256(raw).hexdigest()

def check(original:bytes, artifact_dir:Path, report:dict):
    try:
        if not isinstance(report,dict) or set(report)!={
            "schema","verdict","source_digest","final_digest","final_artifact","stages",
            "claim","independent_verifier","measurement"
        } or report.get("schema")!=SCHEMA or report.get("verdict")!="Candidate" or report["claim"]!=CLAIM or report["independent_verifier"]!=VERIFIER or report["measurement"]!="No hardware speed claim in the mathematical proof; run a separate paired benchmark":
            return {"ok":False,"reason":"Pipeline proof schema or claim mismatch"}
        if not original or len(original)>4*1024*1024 or digest(original)!=report["source_digest"]:
            return {"ok":False,"reason":"Original source bytes do not match"}
        if report["final_artifact"]!="candidate.onnx":
            return {"ok":False,"reason":"Final artifact reference mismatch"}
        stages=report["stages"]
        if not isinstance(stages,list) or not 1<=len(stages)<=len(CHECKERS):
            return {"ok":False,"reason":"Invalid number of stages"}
        current=original
        previous_order=-1
        accepted=[]
        for i,step in enumerate(stages,1):
            if not isinstance(step,dict) or set(step)!={
                "index","operator","input_digest","output_digest","artifact_name","proof_name",
                "independent_verifier","rewrites"
            }:
                return {"ok":False,"reason":"Unexpected stage metadata"}
            operation=step["operator"]
            if operation not in CHECKERS:
                return {"ok":False,"reason":"Unregistered stage operation"}
            position,checker=CHECKERS[operation]
            if position<=previous_order or step["index"]!=i:
                return {"ok":False,"reason":"Stage order or index altered"}
            previous_order=position
            name="stage-%02d"%i
            if step["artifact_name"]!=name+".onnx" or step["proof_name"]!=name+".proof.json":
                return {"ok":False,"reason":"Stage file name not canonical"}
            if digest(current)!=step["input_digest"]:
                return {"ok":False,"reason":"Incorrect source closure for stage"}
            stage_bytes=(artifact_dir/step["artifact_name"]).read_bytes()
            proof=json.loads((artifact_dir/step["proof_name"]).read_text())
            if step["output_digest"]!=digest(stage_bytes) or step["independent_verifier"]!=proof.get("verifier") or step["rewrites"]!=len(proof["rewrites"]):
                return {"ok":False,"reason":"Stage output or proof metadata incorrect"}
            verdict=checker(current,stage_bytes,proof)
            if not verdict["ok"]:
                return {"ok":False,"reason":"Stage %d rejected: %s"%(i,verdict.get("reason","unknown"))}
            accepted.append({"operation":operation,"source_digest":step["input_digest"],
                             "candidate_digest":step["output_digest"],"rewrites":step["rewrites"]})
            current=stage_bytes
        final=(artifact_dir/"candidate.onnx").read_bytes()
        if current!=final or digest(final)!=report["final_digest"]:
            return {"ok":False,"reason":"Final artifact not proven by complete chain"}
        return {"ok":True,"stages":len(stages),"verified":accepted,"final_digest":report["final_digest"],
                "proven_contract":"Exact preservation of declared ONNX graph outputs for admissible input tensors"}
    except Exception as exc:
        return {"ok":False,"reason":"Independent pipeline replay failed: "+type(exc).__name__+": "+str(exc)[:140]}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,required=True)
    p.add_argument("--artifacts",type=Path,required=True)
    args=p.parse_args()
    result=check(args.source.read_bytes(),args.artifacts,
                 json.loads((args.artifacts/"pipeline.json").read_text()))
    print(json.dumps(result,sort_keys=True))
    if not result["ok"]:raise SystemExit(1)

if __name__=="__main__":main()
