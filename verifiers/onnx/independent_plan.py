"""Offline independent checker of Colony's executable ONNX plan.

No optimizer, runner, generator, signer or Colony network connection is used.
It validates original model bytes, every selected ONNX stage through its
independent checker, the original/delivered bytes, and the target-selection
arithmetic from a retained measurement transcript. Physical timings are
reported observations, not mathematical proofs of hardware cost.
"""
from __future__ import annotations
import base64
import hashlib
import json
import math
import statistics
import tempfile
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
from pipeline_independent import check as check_pipeline

SCHEMA="colony.verified-execution-plan.v1"
VERIFIER="colony.onnx-plan-independent.v1"
REGISTRY=[
  "onnx.static-metadata-graph.v1",
  "onnx.quantized-zero-matmul.v1",
  "onnx.quantized-trailing-zero-columns.v1",
  "onnx.quantized-sparse-columns.v1",
]
SEMANTICS={
 "dialect":"onnx.standard-closed-graph.v1",
 "predicate":"onnx.all-graph-outputs.bit-exact.v1",
 "equivalence":"bit_exact",
 "admissible_inputs":"model_declared_tensor_domain",
 "observations":"all_original_graph_outputs",
 "effects":"no_extra_outputs_or_effects",
 "registered_operators":REGISTRY
}
VERIFICATION={
 "checker":VERIFIER,
 "stage_checker":"colony.inference-pipeline-independent.v1",
 "source_closed":True,
 "proof_kind":"registered_source_to_source_replay"
}
ECONOMICS={"kind":"no_customer_savings_claim","cash_value":None}
TOP_FIELDS={"schema","profile","source","semantics","transformations","delivery","target","verification","economic_claim"}

def sha(raw):
 return "sha256:"+hashlib.sha256(raw).hexdigest()

def canonical(obj):
 return json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False,allow_nan=False).encode("utf8")

def require(test,reason):
 if not test:raise ValueError(reason)

def checked_json(data):
 def reject_duplicate_keys(pairs):
  result={}
  for k,v in pairs:
   if k in result:raise ValueError("Duplicate JSON key")
   result[k]=v
  return result
 return json.loads(data,object_pairs_hook=reject_duplicate_keys)

def check_median_metrics(decision,source,final,selected_stage):
 require(type(decision)==dict and decision.get("schema")=="colony.inference-cost-decision.v1","Cost decision schema mismatch")
 require(decision.get("source_digest")==sha(source) and decision.get("selected_digest")==sha(final),"Cost input or selected executable mismatch")
 require(decision.get("target")=="CPUExecutionProvider","Cost target not registered")
 require(type(decision.get("benchmark_iterations"))==int and 12<=decision["benchmark_iterations"]<=400,"Missing iterations")
 require(type(decision.get("warmups"))==int and decision["warmups"]>=1,"Missing warmups")
 margin=decision.get("minimum_gain")
 require(type(margin) in (int,float) and 0<=margin<=0.4,"Invalid minimum-gain threshold")
 metrics=decision.get("measurements")
 require(type(metrics)==list and 2<=len(metrics)<=5,"Target measurements absent")
 runs=decision["benchmark_iterations"]
 for i,m in enumerate(metrics):
  require(type(m)==dict and m.get("stage_index")==i,"Measurement stage order invalid")
  values=m.get("samples_us")
  require(type(values)==list and len(values)==runs,"Raw target measurements missing")
  require(all(type(x) in (float,int) and math.isfinite(x) and 0<x<1_000_000 for x in values),"Invalid raw sample")
  require(m.get("median_us")==round(statistics.median(values),4),"Median differs from raw samples")
  require(m.get("p90_us")==round(sorted(values)[int(0.90*(runs-1))],4),"P90 differs from raw samples")
  require(type(m.get("digest"))==str and m["digest"].startswith("sha256:") and m.get("bytes",0)>0,"Metric artifact invalid")
 require(metrics[0]["digest"]==sha(source) and metrics[0]["operator"]=="original","Original measurement differs from model")
 best=min(range(len(metrics)),key=lambda i:(metrics[i]["median_us"],metrics[i]["bytes"]))
 if best==0 or metrics[best]["median_us"]>metrics[0]["median_us"]*(1-margin):
  best=0
 require(decision.get("selected_stage")==best and selected_stage==best,"Device-cost selection does not follow declared gate")
 require(metrics[best]["digest"]==sha(final),"Selected cost metric does not bind delivered model")
 require(decision.get("original_median_us")==metrics[0]["median_us"],"Original median inconsistent")
 require(decision.get("outcome")==("measured_improvement" if best else "baseline_retained"),"Measured outcome mismatch")
 return metrics[0]["median_us"],metrics[best]["median_us"]

def check(source:bytes, artifacts:dict[str,bytes]):
 try:
  require(type(artifacts)==dict and all(type(k)==str and type(v)==bytes for k,v in artifacts.items()),"Invalid artifact bytes")
  require(set(("plan.json","candidate.onnx")).issubset(artifacts),"Required plan and executable missing")
  plan=checked_json(artifacts["plan.json"])
  require(type(plan)==dict and set(plan)==TOP_FIELDS and plan["schema"]==SCHEMA and plan["profile"]=="onnx-exact-cpu-v1","Unregistered plan schema")
  require(plan["semantics"]==SEMANTICS and plan["verification"]==VERIFICATION and plan["economic_claim"]==ECONOMICS,"Executable semantics or verifier registry mismatch")
  require(plan["source"]=={"digest":sha(source),"size_bytes":len(source),"closure":"single_immutable_file","missing_dependencies":[]},"Original source closure mismatch")
  final=artifacts["candidate.onnx"]
  delivered=plan["delivery"]
  require(type(delivered)==dict and set(delivered)=={"artifact_name","digest","size_bytes","outcome"},"Delivered artifact shape mismatch")
  require(delivered["artifact_name"]=="candidate.onnx" and delivered["digest"]==sha(final) and delivered["size_bytes"]==len(final),"Delivered bytes differ")
  require(delivered["outcome"] in ("optimized","no_improvement"),"Unregistered plan outcome")
  transform=plan["transformations"]
  require(type(transform)==dict and set(transform)=={"stages","selected_count","identity"},"Transformation manifest shape mismatch")
  stages=transform["stages"]
  require(type(stages)==list and 0<=len(stages)<=len(REGISTRY),"Unregistered transformation count")
  require(transform["selected_count"]==len(stages) and transform["identity"] is (len(stages)==0),"Invalid identity/selection claim")
  target=plan["target"]
  require(type(target)==dict and set(target)=={"provider","evidence","decision_artifact","decision_digest","original_median_us","selected_median_us","selected_stage"},"Execution target schema mismatch")
  require(target["provider"]=="CPUExecutionProvider" and target["selected_stage"]==len(stages),"Selected stage differs from transformation proof")
  if stages:
   require(delivered["outcome"]=="optimized","Transformed executable marked unchanged")
   require("pipeline.json" in artifacts and "decision.json" in artifacts,"Independent proof and cost evidence required")
   report=checked_json(artifacts["pipeline.json"])
   require(report.get("source_digest")==sha(source) and report.get("final_digest")==sha(final),"Proof source/final digest mismatch")
   require(len(report.get("stages",[]))==len(stages),"Proof stage count mismatch")
   with tempfile.TemporaryDirectory(prefix="colony-offline-plan-") as d:
    folder=Path(d)
    (folder/"pipeline.json").write_bytes(artifacts["pipeline.json"])
    (folder/"candidate.onnx").write_bytes(final)
    for i,stage in enumerate(stages):
     original_stage=report["stages"][i]
     require(stage=={
       "index":original_stage["index"],
       "operator":original_stage["operator"],
       "source_digest":original_stage["input_digest"],
       "output_digest":original_stage["output_digest"],
       "artifact_name":original_stage["artifact_name"],
       "artifact_digest":sha(artifacts[original_stage["artifact_name"]]),
       "proof_name":original_stage["proof_name"],
       "proof_digest":sha(artifacts[original_stage["proof_name"]]),
       "independent_verifier":original_stage["independent_verifier"]
     },"Operator, digest or proof chain has changed")
     require(stage["operator"] in REGISTRY,"Unregistered mathematical transformation")
     (folder/stage["artifact_name"]).write_bytes(artifacts[stage["artifact_name"]])
     (folder/stage["proof_name"]).write_bytes(artifacts[stage["proof_name"]])
    proved=check_pipeline(source,folder,report)
    require(proved["ok"],"Independent ONNX stage proof failed: "+proved.get("reason",""))
  else:
   require(delivered["outcome"]=="no_improvement" and final==source,"Identity must deliver identical source bytes")
  if "decision.json" in artifacts:
   d_raw=artifacts["decision.json"]
   d=checked_json(d_raw)
   original_med,selected_med=check_median_metrics(d,source,final,len(stages))
   expected={"provider":"CPUExecutionProvider","evidence":"measured_single_host",
             "decision_artifact":"decision.json","decision_digest":sha(d_raw),
             "original_median_us":original_med,"selected_median_us":selected_med,
             "selected_stage":len(stages)}
   require(target==expected,"Plan and actual target decision differ")
  else:
   require(target=={"provider":"CPUExecutionProvider","evidence":"identity_only",
             "decision_artifact":None,"decision_digest":None,"original_median_us":None,
             "selected_median_us":None,"selected_stage":0},"Unmeasured plan cannot claim target speed")
  # A plan binds all admitted source, semantics, stage proofs and chosen bytes.
  # The actual physical duration remains an observed benchmark, not a theorem.
  return {"ok":True,"plan_digest":sha(artifacts["plan.json"]),"source_digest":sha(source),
          "candidate_digest":sha(final),"verified_stages":len(stages),
          "kind":"offline_independent_exact_onnx_plan",
          "measurement_evidence":target["evidence"],
          "customer_savings_claimed":False}
 except Exception as e:
  return {"ok":False,"reason":type(e).__name__+": "+str(e)[:180]}

def from_runner_response(source:bytes, result:dict):
 try:
  require(type(result)==dict and type(result.get("artifacts"))==list,"Runner artifacts missing")
  assets={}
  for a in result["artifacts"]:
   require(type(a)==dict and set(a)=={"name","media_type","digest","size_bytes","base64"},"Runner artifact fields invalid")
   name=a["name"]
   require(type(name)==str and name not in assets and name and len(name)<81 and
           all(c.isalnum() or c in "._-" for c in name),"Invalid artifact name")
   raw=base64.b64decode(a["base64"],validate=True)
   require(base64.b64encode(raw).decode()==a["base64"] and len(raw)==a["size_bytes"] and sha(raw)==a["digest"],"Artifact digest mismatch")
   assets[name]=raw
  return check(source,assets)
 except Exception as e:
  return {"ok":False,"reason":type(e).__name__+": "+str(e)[:180]}

def main():
 import argparse
 p=argparse.ArgumentParser()
 p.add_argument("--source",type=Path,required=True)
 p.add_argument("--artifacts",type=Path,required=True)
 args=p.parse_args()
 folder=args.artifacts
 assets={f.name:f.read_bytes() for f in folder.iterdir() if f.is_file() and f.name in
         {"plan.json","candidate.onnx","decision.json","pipeline.json"} or f.is_file() and f.name.startswith("stage-")}
 result=check(args.source.read_bytes(),assets)
 print(json.dumps(result,sort_keys=True))
 if not result["ok"]:raise SystemExit(1)

if __name__=="__main__":main()
