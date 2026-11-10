"""Independent replay for arbitrary centered-zero MatMulInteger columns.

Derives active indices with scalar integer loops over original B, independently
constructs a zero-column selection map and rebuilds the complete candidate.
This module imports no proposal-generator code.
"""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import Path
import numpy as np
import onnx
from onnx import TensorProto,helper,numpy_helper

PROFILE="onnx.quantized-sparse-columns.v1"
CONTRACT=("For every admissible quantized A tensor and A zero point, replace the "
          "full integer matrix product with its sorted active columns, append one "
          "exact zero column, and gather the original column order wherever "
          "removed B weights equal the scalar B zero point; preserve every "
          "original graph output.")
SIDE_CONDITIONS=[
    "Closed standard ONNX opset 15–25 with no custom control flow or external data",
    "MatMulInteger uses fixed rank-2 int8/uint8 A and initializer B",
    "B zero point is absent or a scalar initializer of the same integer dtype",
    "Every removed B column equals B zero point for all rows; sorted active columns remain",
    "All introduced intermediate names are fresh, output shape has at most 16384 entries",
    "Untouched graph nodes, retained original initializers, interfaces and fields remain identical"
]

def digest(raw):
    return "sha256:"+hashlib.sha256(raw).hexdigest()

def types_and_shapes(model):
    inferred=onnx.shape_inference.infer_shapes(model,strict_mode=False,data_prop=False)
    shapes={}
    for item in list(inferred.graph.input)+list(inferred.graph.value_info)+list(inferred.graph.output):
        t=item.type
        if not t.HasField("tensor_type") or not t.tensor_type.HasField("shape"):
            continue
        dims=[]
        for dim in t.tensor_type.shape.dim:
            if dim.WhichOneof("value")!="dim_value" or dim.dim_value<0:break
            dims.append(int(dim.dim_value))
        else:shapes[item.name]=(t.tensor_type.elem_type,tuple(dims))
    return shapes

def name_inventory(model):
    used={x.name for x in model.graph.initializer}
    used.update(x.name for x in model.graph.input)
    used.update(x.name for x in model.graph.output)
    used.update(x.name for x in model.graph.value_info)
    for node in model.graph.node:
        used.update(x for x in node.output if x)
    return used

def derive(original,index,initializers,shape,used):
    if original.op_type!="MatMulInteger" or original.domain not in ("","ai.onnx") or original.attribute or len(original.input) not in (2,3,4) or len(original.output)!=1:
        return None
    a,b=original.input[:2]
    if not a or not b or not original.output[0] or b not in initializers:
        return None
    a_shape=shape.get(a)
    if a_shape is None or a_shape[0] not in (TensorProto.INT8,TensorProto.UINT8) or len(a_shape[1])!=2:
        return None
    weights=initializers[b]
    if weights.ndim!=2 or weights.dtype not in (np.dtype("int8"),np.dtype("uint8")):
        return None
    m,k=a_shape[1]
    bk,n=weights.shape
    if m<=0 or k<=0 or bk!=k or n<2 or m*n>16384:
        return None
    zero=0
    if len(original.input)==4 and original.input[3]:
        point=initializers.get(original.input[3])
        if point is None or point.shape!=() or point.dtype!=weights.dtype:return None
        zero=int(point)
    nonzero_columns=[]
    for column in range(n):
        if any(int(weights[row,column])!=zero for row in range(k)):
            nonzero_columns.append(column)
    if not nonzero_columns:return None
    active=nonzero_columns
    if len(active)==n:return None
    selection=[]
    for column in range(n):
        selection.append(active.index(column) if column in active else len(active))
    output=shape.get(original.output[0])
    if output is not None and output!=(TensorProto.INT32,(m,n)):
        return None
    tag="__colony_qsparse_%03d"%index
    names={"b_name":tag+"_B","matmul_output":tag+"_Y","zeros_name":tag+"_Z",
           "shape_name":tag+"_SH","packed_output":tag+"_P","indices_name":tag+"_IX"}
    if any(name in used for name in names.values()):
        return None
    return {
        "index":index,"output":original.output[0],"old_b_name":b,
        "active_indices":active,"retained_columns":len(active),"removed_columns":n-len(active),
        "selection_indices":selection,
        "m":int(m),"k":int(k),"n":int(n),"b_zero_point":int(zero),
        **names
    }

def check(source_raw,candidate_raw,proof):
    try:
        if not isinstance(proof,dict) or set(proof)!={
            "schema","operator","source_digest","candidate_digest","contract",
            "side_conditions","rewrites","verifier"
        } or proof.get("schema")!="colony.inference-proof.v1" or proof.get("operator")!=PROFILE or proof.get("contract")!=CONTRACT or proof.get("side_conditions")!=SIDE_CONDITIONS or proof.get("verifier")!="colony.quantized-sparse-independent.v1":
            return {"ok":False,"reason":"Unregistered contract or claim"}
        if not source_raw or len(source_raw)>4*1024*1024 or not candidate_raw or len(candidate_raw)>8*1024*1024 or digest(source_raw)!=proof["source_digest"] or digest(candidate_raw)!=proof["candidate_digest"]:
            return {"ok":False,"reason":"Source/candidate digest mismatch"}
        source=onnx.load_model_from_string(source_raw)
        candidate=onnx.load_model_from_string(candidate_raw)
        onnx.checker.check_model(source)
        onnx.checker.check_model(candidate)
        if len(source.opset_import)!=1 or source.opset_import[0].domain not in ("","ai.onnx") or not 15<=source.opset_import[0].version<=25:
            return {"ok":False,"reason":"Unsupported source ONNX opset"}
        if source.functions or source.training_info or source.graph.sparse_initializer or len(source.graph.node)>512:
            return {"ok":False,"reason":"Unsupported source graph"}
        if any(n.domain not in ("","ai.onnx") or n.op_type in ("If","Loop","Scan") for n in source.graph.node):
            return {"ok":False,"reason":"Unsupported graph operators"}
        if any(t.data_location==TensorProto.EXTERNAL or t.external_data for t in source.graph.initializer):
            return {"ok":False,"reason":"Missing original initializer bytes"}
        steps=proof["rewrites"]
        if not isinstance(steps,list) or not 1<=len(steps)<=512:
            return {"ok":False,"reason":"Invalid or empty transformation sequence"}
        overridable={v.name for v in source.graph.input}
        known={x.name:numpy_helper.to_array(x) for x in source.graph.initializer if x.name not in overridable}
        shapes=types_and_shapes(source)
        used=name_inventory(source)
        by_index={}
        for step in steps:
            if type(step) is not dict or set(step)!={
                "index","output","old_b_name","active_indices","retained_columns","removed_columns","selection_indices","m","k",
                "n","b_zero_point","b_name","matmul_output","zeros_name","shape_name","packed_output","indices_name"
            }:
                return {"ok":False,"reason":"Unexpected candidate fields"}
            i=step["index"]
            if type(i) is not int or not 0<=i<len(source.graph.node) or i in by_index:
                return {"ok":False,"reason":"Duplicate or invalid source node"}
            expected=derive(source.graph.node[i],i,known,shapes,used)
            if expected is None or step!=expected:
                return {"ok":False,"reason":"Original integer matrix relation does not support rewrite"}
            by_index[i]=step
            used.update(step[key] for key in ("b_name","matmul_output","zeros_name","shape_name","packed_output","indices_name"))
        if [x["index"] for x in steps]!=sorted(by_index):
            return {"ok":False,"reason":"Rewrite order changed"}
        rebuilt=copy.deepcopy(source)
        original_nodes=list(rebuilt.graph.node)
        nodes=[]
        products_before=products_after=0
        for i,node in enumerate(original_nodes):
            if i not in by_index:
                nodes.append(node)
                continue
            s=by_index[i]
            prefix=copy.deepcopy(node)
            prefix.input[1]=s["b_name"]
            prefix.output[0]=s["matmul_output"]
            nodes.append(prefix)
            nodes.append(helper.make_node("ConstantOfShape",[s["shape_name"]],[s["zeros_name"]],
                value=numpy_helper.from_array(np.array([0],dtype=np.int32))))
            nodes.append(helper.make_node("Concat",[s["matmul_output"],s["zeros_name"]],[s["packed_output"]],axis=1))
            nodes.append(helper.make_node("Gather",[s["packed_output"],s["indices_name"]],[s["output"]],axis=1))
            reduced=np.empty((s["k"],s["retained_columns"]),dtype=known[s["old_b_name"]].dtype)
            for j,original_column in enumerate(s["active_indices"]):
                for row in range(s["k"]):
                    reduced[row,j]=known[s["old_b_name"]][row,original_column]
            rebuilt.graph.initializer.append(numpy_helper.from_array(reduced,name=s["b_name"]))
            rebuilt.graph.initializer.append(numpy_helper.from_array(
                np.array([s["m"],1],dtype=np.int64),
                name=s["shape_name"]))
            rebuilt.graph.initializer.append(numpy_helper.from_array(
                np.array(s["selection_indices"],dtype=np.int64),name=s["indices_name"]))
            products_before+=s["m"]*s["k"]*s["n"]
            products_after+=s["m"]*s["k"]*s["retained_columns"]
        del rebuilt.graph.node[:]
        rebuilt.graph.node.extend(nodes)
        # Independent dead-initializer check: the removed original matrix
        # must be absent from every surviving use and graph interface.
        referenced={x for node in rebuilt.graph.node for x in node.input if x}
        referenced.update(v.name for v in rebuilt.graph.input)
        referenced.update(v.name for v in rebuilt.graph.output)
        referenced.update(v.name for v in rebuilt.graph.value_info)
        dead={s["old_b_name"] for s in steps}.difference(referenced)
        retained=[t for t in rebuilt.graph.initializer if t.name not in dead]
        del rebuilt.graph.initializer[:]
        rebuilt.graph.initializer.extend(retained)
        onnx.checker.check_model(rebuilt)
        if rebuilt.SerializeToString(deterministic=True)!=candidate.SerializeToString(deterministic=True):
            return {"ok":False,"reason":"Candidate has unchecked ONNX changes"}
        return {
            "ok":True,"operator":PROFILE,"source_digest":digest(source_raw),
            "candidate_digest":digest(candidate_raw),"exact_rewrites":len(steps),
            "original_integer_products":products_before,"retained_integer_products":products_after,
            "avoided_integer_products":products_before-products_after,
            "scope":CONTRACT,"independent_semantics":"All A values and A zero points; active B columns unchanged in sorted order; Gather restores each exact output, using zero for every centered-zero column"
        }
    except Exception as exc:
        return {"ok":False,"reason":"Independent checker failed: "+type(exc).__name__+": "+str(exc)[:150]}

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
