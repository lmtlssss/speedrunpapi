"""Independent verifier for Colony ONNX static-metadata graph transformations.

Reconstructs replacement constants directly from the original ONNX source
and verifies that every untouched source node, interface and model field
is preserved byte-for-byte by deterministic protobuf serialization.
Never imports or trusts the optimizer's evaluator or its claimed improvement.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path
import numpy as np
import onnx
from onnx import TensorProto, numpy_helper

CONTRACT = "For all input tensor values conforming to fixed ONNX input shapes and types, preserve every graph output under the original ONNX operator semantics. Only shape-dependent integer metadata operations are replaced with equal constants."
SIDE_CONDITIONS = [
    "Source ONNX standard opset 15–25", "All evaluated Shape inputs have declared fixed static dimensions",
    "All folded metadata inputs are int64 constants", "External data and control-flow excluded",
    "All non-rewritten source nodes and graph interface are byte-identical in normalized model"
]


def digest(raw):
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def exact_shape_declarations(model):
    result = {}
    i = onnx.shape_inference.infer_shapes(model, strict_mode=False, data_prop=False)
    for v in list(i.graph.input) + list(i.graph.value_info) + list(i.graph.output):
        if not v.type.HasField("tensor_type"):
            continue
        t = v.type.tensor_type
        if not t.HasField("shape") or not t.elem_type:
            continue
        sizes = []
        for d in t.shape.dim:
            if d.WhichOneof("value") != "dim_value" or d.dim_value < 0:
                break
            sizes.append(int(d.dim_value))
        else:
            result[v.name] = tuple(sizes)
    return result


def known_int64_tensor(t):
    if t.data_location == TensorProto.EXTERNAL or t.external_data:
        return None
    array = numpy_helper.to_array(t)
    if array.dtype != np.dtype("int64") or array.size > 4096 or array.ndim > 6:
        return None
    return array.copy()


def integer_attribute(node, field, fallback):
    attrs = [a for a in node.attribute if a.name == field]
    if len(attrs) > 1 or any(a.type != onnx.AttributeProto.INT for a in attrs):
        raise ValueError("Attribute has unsupported form")
    return int(attrs[0].i) if attrs else fallback


def derive(node, static_shapes, known):
    if node.domain not in ("", "ai.onnx") or len(node.output) != 1:
        return None
    if node.op_type == "Shape":
        if len(node.input) != 1 or node.input[0] not in static_shapes:
            return None
        if any(a.name not in ("start", "end") for a in node.attribute):
            return None
        dims = static_shapes[node.input[0]]
        lo = integer_attribute(node, "start", 0)
        hi = integer_attribute(node, "end", len(dims))
        return np.asarray(dims[lo:hi], dtype=np.int64)
    if node.op_type == "Size":
        if len(node.input) != 1 or node.input[0] not in static_shapes or node.attribute:
            return None
        size = math.prod(static_shapes[node.input[0]])
        return np.asarray(size, dtype=np.int64) if size < 2 ** 63 else None
    if node.op_type == "Gather":
        if len(node.input) != 2 or any(x not in known for x in node.input):
            return None
        if any(a.name != "axis" for a in node.attribute) or integer_attribute(node, "axis", 0) != 0:
            return None
        source, indices = known[node.input[0]], known[node.input[1]]
        if source.ndim != 1 or indices.ndim > 1:
            return None
        # Independent scalar indexing rather than optimizer numpy.take.
        flat = []
        for index in indices.reshape(-1):
            x = int(index)
            if x < 0:
                x += len(source)
            if x < 0 or x >= len(source):
                return None
            flat.append(int(source[x]))
        return np.array(flat, dtype=np.int64).reshape(indices.shape)
    if node.op_type == "Concat":
        if not node.input or any(x not in known for x in node.input):
            return None
        if any(a.name != "axis" for a in node.attribute) or integer_attribute(node, "axis", None) != 0:
            return None
        arrays = [known[x] for x in node.input]
        if any(a.ndim != 1 for a in arrays):
            return None
        return np.asarray([int(y) for a in arrays for y in a], dtype=np.int64)
    if node.op_type == "Unsqueeze":
        if len(node.input) != 2 or any(x not in known for x in node.input) or node.attribute:
            return None
        data, axes = known[node.input[0]], known[node.input[1]]
        if axes.ndim != 1 or len(axes) > 5:
            return None
        rank = data.ndim + len(axes)
        normalized = [int(x) if x >= 0 else int(x) + rank for x in axes]
        if len(normalized) != len(set(normalized)) or any(x < 0 or x >= rank for x in normalized):
            return None
        return np.reshape(data, tuple(1 if i in normalized else data.shape[i - sum(x < i for x in normalized)]
                                      for i in range(rank)))
    return None


def check(original_bytes, candidate_bytes, proof):
    try:
        if (type(proof) is not dict or
            set(proof) != {"schema", "operator", "contract", "original_digest", "candidate_digest", "opset",
                           "rewrites", "side_conditions", "verifier"} or
            proof["schema"] != "colony.onnx-proof.v1" or
            proof["operator"] != "onnx.static-metadata-graph.v1" or
            proof["verifier"] != "onnx.static-metadata-independent.v1" or
            proof["contract"] != CONTRACT or proof["side_conditions"] != SIDE_CONDITIONS or
            proof["original_digest"] != digest(original_bytes) or
            proof["candidate_digest"] != digest(candidate_bytes)):
            return {"ok": False, "reason": "proof metadata, source or candidate mismatch"}
        if not original_bytes or len(original_bytes) > 4 * 1024 * 1024:
            return {"ok": False, "reason": "source bounds"}
        source = onnx.load_model_from_string(original_bytes)
        received = onnx.load_model_from_string(candidate_bytes)
        onnx.checker.check_model(source)
        onnx.checker.check_model(received)
        if source.functions or source.training_info or source.graph.sparse_initializer:
            return {"ok": False, "reason": "unsupported model extension"}
        if len(source.opset_import) != 1 or source.opset_import[0].domain not in ("", "ai.onnx"):
            return {"ok": False, "reason": "unsupported ONNX domain"}
        if not 15 <= source.opset_import[0].version <= 25 or source.opset_import[0].version != proof["opset"]:
            return {"ok": False, "reason": "unsupported ONNX opset"}
        if any(n.op_type in ("Loop", "If", "Scan") or n.domain not in ("", "ai.onnx") for n in source.graph.node):
            return {"ok": False, "reason": "control flow or custom op"}
        if any(x.data_location == TensorProto.EXTERNAL or x.external_data for x in source.graph.initializer):
            return {"ok": False, "reason": "external source not closed"}
        if len(source.graph.node) > 512:
            return {"ok": False, "reason": "node budget"}
        rewrites = proof["rewrites"]
        if not isinstance(rewrites, list) or not 1 <= len(rewrites) <= 512:
            return {"ok": False, "reason": "empty or oversized rewrite list"}
        by_index = {}
        for item in rewrites:
            if type(item) is not dict or set(item) != {"index", "op_type", "output", "dims", "values"}:
                return {"ok": False, "reason": "rewrite fields"}
            index = item["index"]
            if type(index) is not int or index < 0 or index >= len(source.graph.node) or index in by_index:
                return {"ok": False, "reason": "rewrite index"}
            by_index[index] = item
        declared = exact_shape_declarations(source)
        known = {}
        overridable={v.name for v in source.graph.input}
        for t in source.graph.initializer:
            if t.name in overridable:
                continue
            a = known_int64_tensor(t)
            if a is not None:
                known[t.name] = a
        actual_rewrites = []
        for i, node in enumerate(source.graph.node):
            if node.op_type == "Constant" and len(node.output) == 1 and len(node.attribute) == 1 and node.attribute[0].name == "value":
                value = known_int64_tensor(node.attribute[0].t)
                if value is not None:
                    known[node.output[0]] = value
                if i in by_index:
                    return {"ok": False, "reason": "cannot rewrite original Constant"}
                continue
            # Source compiler semantics are independently derived for the entire
            # recorded chain. The verifier can use untouched constants as inputs.
            if i not in by_index:
                continue
            step = by_index[i]
            if node.op_type != step["op_type"] or len(node.output) != 1 or node.output[0] != step["output"]:
                return {"ok": False, "reason": "rewritten source node changed"}
            value = derive(node, declared, known)
            if value is None or value.dtype != np.dtype("int64") or value.size > 4096 or value.ndim > 6:
                return {"ok": False, "reason": "cannot derive exact metadata value"}
            if step["dims"] != list(value.shape) or step["values"] != [int(z) for z in value.reshape(-1)]:
                return {"ok": False, "reason": "incorrect exact metadata value"}
            known[node.output[0]] = value
            actual_rewrites.append((i, node.output[0], value))
        expected = copy.deepcopy(source)
        keep = [node for i, node in enumerate(expected.graph.node) if i not in by_index]
        del expected.graph.node[:]
        expected.graph.node.extend(keep)
        for _, name, value in actual_rewrites:
            expected.graph.initializer.append(numpy_helper.from_array(value, name=name))
        onnx.checker.check_model(expected)
        if expected.SerializeToString(deterministic=True) != received.SerializeToString(deterministic=True):
            return {"ok": False, "reason": "candidate includes unverified changes"}
        return {"ok": True, "verifier": "onnx.static-metadata-independent.v1",
                "scope": CONTRACT, "rewritten_nodes": len(actual_rewrites),
                "source_digest": proof["original_digest"], "candidate_digest": proof["candidate_digest"]}
    except Exception as exc:
        return {"ok": False, "reason": "replay failed: " + type(exc).__name__ + ": " + str(exc)[:160]}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--candidate", required=True, type=Path)
    p.add_argument("--proof", required=True, type=Path)
    args = p.parse_args()
    result = check(args.source.read_bytes(), args.candidate.read_bytes(), json.loads(args.proof.read_text()))
    print(json.dumps(result, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
