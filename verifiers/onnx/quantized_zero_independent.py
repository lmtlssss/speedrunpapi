"""Independent algebraic/structural checker for quantized ONNX zero-weight pruning.

Uses original ONNX bytes and proof to reconstruct the one allowed rewrite.
Never imports candidate generation. All non-rewritten model fields and ops
must match original source exactly, including order.
"""
from __future__ import annotations
import copy
import hashlib
import json
import math
from pathlib import Path
import numpy as np
import onnx
from onnx import TensorProto, numpy_helper

PROFILE="onnx.quantized-zero-matmul.v1"
CONTRACT=("For all valid tensor values and A zero points admitted by the original "
          "ONNX MatMulInteger graph, any output with a fixed B initializer equal "
          "elementwise to its scalar B zero point is exactly the int32 zero tensor.")
SIDE_CONDITIONS=[
    "ONNX standard opset 15–25, single closed graph, no external data or control flow",
    "MatMulInteger has no attributes and uses fixed 2D int8/uint8 A and B",
    "B and its optional scalar B zero point are signedness-compatible initializers",
    "All B entries equal B zero point, so every exact integer product is zero",
    "Original output shape is static and contains at most 16384 int32 elements",
    "Every untouched node, model field and interface is byte-preserved",
]

def digest(raw):
    return "sha256:"+hashlib.sha256(raw).hexdigest()

def tensor_shapes(source):
    inferred=onnx.shape_inference.infer_shapes(source,strict_mode=False,data_prop=False)
    result={}
    for v in list(inferred.graph.input)+list(inferred.graph.value_info)+list(inferred.graph.output):
        t=v.type
        if not t.HasField("tensor_type") or not t.tensor_type.HasField("shape"):
            continue
        dims=[]
        for d in t.tensor_type.shape.dim:
            if d.WhichOneof("value")!="dim_value" or d.dim_value<0:
                break
            dims.append(int(d.dim_value))
        else:result[v.name]=(t.tensor_type.elem_type,tuple(dims))
    return result

def reconstruct_step(node,index,known,shapes):
    if node.op_type!="MatMulInteger" or node.domain not in ("","ai.onnx"):
        return None
    if node.attribute or len(node.input)<2 or len(node.input)>4 or len(node.output)!=1 or not node.output[0]:
        return None
    aname,bname=node.input[:2]
    shape=shapes.get(aname)
    if shape is None or shape[0] not in (TensorProto.INT8,TensorProto.UINT8):
        return None
    weights=known.get(bname)
    if weights is None or weights.ndim!=2 or weights.dtype not in (np.dtype("int8"),np.dtype("uint8")) or len(shape[1])!=2:
        return None
    m,k=shape[1]
    kb,n=weights.shape
    if not (m>0 and k>0 and kb==k and n>0 and m*n<=16384):
        return None
    bzp=0
    if len(node.input)==4 and node.input[3]:
        point=known.get(node.input[3])
        if point is None or point.shape!=() or point.dtype!=weights.dtype:
            return None
        bzp=int(point)
    # All rows and all output columns must have zero centered weight.
    # Then sum_j ((A_ij - azp_i) * (B_jk - bzp)) equals 0 over exact integers.
    for row in weights:
        for entry in row:
            if int(entry)-bzp != 0:
                return None
    output=shapes.get(node.output[0])
    if output is not None and output!=(TensorProto.INT32,(m,n)):
        return None
    return {"index":index,"op_type":"MatMulInteger","output":node.output[0],
            "dims":[int(m),int(n)],"b_name":bname,"b_zero_point":bzp,
            "reason":"All centered B weights are exactly zero"}

def check(source_bytes,candidate_bytes,proof):
    try:
        if not isinstance(proof,dict) or set(proof)!={
           "schema","operator","source_digest","candidate_digest","contract","side_conditions","rewrites","verifier"
        } or proof.get("schema")!="colony.inference-proof.v1" or proof.get("operator")!=PROFILE or (
           proof.get("verifier")!="colony.quantized-zero-independent.v1"
        ) or proof["contract"]!=CONTRACT or proof["side_conditions"]!=SIDE_CONDITIONS:
            return {"ok":False,"reason":"Contract, verifier or proof fields are incorrect"}
        if not source_bytes or len(source_bytes)>4*1024*1024 or proof["source_digest"]!=digest(source_bytes) or proof["candidate_digest"]!=digest(candidate_bytes):
            return {"ok":False,"reason":"Original or transformed bytes differ from bound digests"}
        source=onnx.load_model_from_string(source_bytes)
        candidate=onnx.load_model_from_string(candidate_bytes)
        onnx.checker.check_model(source)
        onnx.checker.check_model(candidate)
        if len(source.opset_import)!=1 or source.opset_import[0].domain not in ("","ai.onnx") or not 15<=source.opset_import[0].version<=25:
            return {"ok":False,"reason":"Unexpected operator set"}
        if source.functions or source.training_info or source.graph.sparse_initializer or len(source.graph.node)>512:
            return {"ok":False,"reason":"Model outside closed flat graph domain"}
        if any(n.domain not in ("","ai.onnx") or n.op_type in ("If","Loop","Scan") for n in source.graph.node):
            return {"ok":False,"reason":"Model contains custom/control operators"}
        if any(t.data_location==TensorProto.EXTERNAL or t.external_data for t in source.graph.initializer):
            return {"ok":False,"reason":"External bytes not present"}
        steps=proof["rewrites"]
        if not isinstance(steps,list) or not 1<=len(steps)<=512:
            return {"ok":False,"reason":"Empty or overlength rewrite list"}
        overridable={v.name for v in source.graph.input}
        known={t.name:numpy_helper.to_array(t) for t in source.graph.initializer if t.name not in overridable}
        shapes=tensor_shapes(source)
        indices=set()
        expected_steps=[]
        for step in steps:
            if not isinstance(step,dict) or set(step)!={"index","op_type","output","dims","b_name","b_zero_point","reason"}:
                return {"ok":False,"reason":"Unexpected rewrite content"}
            i=step["index"]
            if type(i) is not int or i<0 or i>=len(source.graph.node) or i in indices:
                return {"ok":False,"reason":"Invalid/duplicate original node index"}
            expected=reconstruct_step(source.graph.node[i],i,known,shapes)
            if expected is None or expected!=step:
                return {"ok":False,"reason":"Original ONNX integer algebra does not justify rewrite"}
            indices.add(i)
            expected_steps.append(expected)
        if [x["index"] for x in steps]!=sorted(indices):
            return {"ok":False,"reason":"Out-of-order rewrites"}
        # Build expected model exclusively from original source. Candidate cannot
        # change any unrelated operation, metadata or graph input/output.
        rebuilt=copy.deepcopy(source)
        prior_nodes=list(rebuilt.graph.node)
        del rebuilt.graph.node[:]
        rebuilt.graph.node.extend(n for i,n in enumerate(prior_nodes) if i not in indices)
        for step in expected_steps:
            rebuilt.graph.initializer.append(numpy_helper.from_array(
                 np.zeros(tuple(step["dims"]),dtype=np.int32),name=step["output"]))
        onnx.checker.check_model(rebuilt)
        if rebuilt.SerializeToString(deterministic=True)!=candidate.SerializeToString(deterministic=True):
            return {"ok":False,"reason":"Transformed ONNX model has unproved differences"}
        original_products=sum(int(s["dims"][0])*int(shapes[source.graph.node[s["index"]].input[0]][1][1])*int(s["dims"][1])
                              for s in expected_steps)
        return {"ok":True,"operator":PROFILE,"source_digest":proof["source_digest"],
                "candidate_digest":proof["candidate_digest"],"exact_rewrites":len(expected_steps),
                "eliminated_integer_multiply_terms":original_products,
                "scope":CONTRACT,"backend":"independent exact ONNX structural and integer-algebra replay"}
    except Exception as exc:
        return {"ok":False,"reason":"Independent checker failed: "+type(exc).__name__+": "+str(exc)[:160]}

def main():
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,required=True)
    p.add_argument("--candidate",type=Path,required=True)
    p.add_argument("--proof",type=Path,required=True)
    a=p.parse_args()
    result=check(a.source.read_bytes(),a.candidate.read_bytes(),json.loads(a.proof.read_text()))
    print(json.dumps(result,sort_keys=True))
    if not result["ok"]:raise SystemExit(1)

if __name__=="__main__":main()
