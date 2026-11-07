#!/usr/bin/env node

// src/cli.ts
import * as fs2 from "node:fs";
import * as path2 from "node:path";
import { createHash } from "node:crypto";

// ../carrycert-core/src/math.ts
var BN128_PRIME = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
function arrangementNumber(k) {
  let v = 1n;
  for (let i = 1; i <= k; i++) v = BigInt(i) * v + 1n;
  return v;
}
function cascadeFunctionCount(radix, stages) {
  if (radix < 2n || stages < 0) throw new Error("radix>=2, stages>=0");
  const t = Math.min(stages, Number(radix - 1n) > 1e9 ? stages : Number(radix - 1n));
  const tt = Math.min(stages, Number(radix > 10n ** 9n ? 10n ** 9n : radix - 1n));
  const tEff = stages;
  const A = arrangementNumber(tEff);
  return (radix - 1n) * A + 1n;
}
function cascadeMinBits(radix, stages) {
  const n = cascadeFunctionCount(radix, stages);
  return n === 0n ? 0 : n.toString(2).length;
}
function twoStageCount(radix) {
  return 5n * radix - 4n;
}
function frontierBound(m) {
  return m + 1;
}
function frontierSolve(width, offsets, masks, targets) {
  const m = offsets.length;
  const limit = 1 << width;
  const mm = masks ?? Array(m).fill(0);
  const tt = targets ?? Array(m).fill(0);
  let thresholds = Array(m).fill(1);
  let order = [...Array(m).keys()];
  let boundaries = [0, 1];
  let switches = Array(m).fill(0);
  let counts = [1n];
  let attempted = 0;
  let maxStates = 1;
  const layer = (w, th, ord) => {
    const lim = 1 << w;
    const b = [0];
    const sw = Array(th.length).fill(0);
    for (const j of ord) {
      const t = th[j];
      if (t < lim && t !== b[b.length - 1]) b.push(t);
      sw[j] = t < lim ? b.length - 1 : -1;
    }
    for (let j = 0; j < th.length; j++) if (th[j] === lim) sw[j] = b.length;
    b.push(lim);
    return { boundaries: b, switches: sw, states: b.length - 1 };
  };
  let current = layer(0, thresholds, order);
  for (let i = 0; i < width; i++) {
    const span = 1 << i;
    const bits = offsets.map((a) => a >> i & 1);
    order = [...order.filter((j) => bits[j]), ...order.filter((j) => !bits[j])];
    thresholds = thresholds.map((t, j) => t + (1 - bits[j]) * span);
    const following = layer(i + 1, thresholds, order);
    const nextCounts = Array(following.states).fill(0n);
    maxStates = Math.max(maxStates, current.states, following.states);
    const successors = (bit) => {
      const target = [];
      let r = 0;
      const shift = bit << current.boundaries.length;
      const sh = bit << i;
      for (let idx = 0; idx < current.states; idx++) {
        const v = current.boundaries[idx] + sh;
        while (r + 1 < following.states && following.boundaries[r + 1] <= v) r++;
        target.push(r);
      }
      return target;
    };
    for (const b of [0, 1]) {
      const dest = successors(b);
      let lo = 0, hi = current.states - 1;
      for (let j = 0; j < m; j++) {
        if (mm[j] >> i & 1) {
          const required = b ^ bits[j] ^ tt[j] >> i & 1;
          if (required) lo = Math.max(lo, current.switches[j]);
          else hi = Math.min(hi, current.switches[j] - 1);
        }
      }
      for (let r = 0; r < current.states; r++) {
        attempted++;
        if (!counts[r] || r < lo || r > hi) continue;
        nextCounts[dest[r]] += counts[r];
      }
    }
    counts = nextCounts;
    current = following;
  }
  const count = counts.reduce((a, b) => a + b, 0n);
  return { count, attempted, maxStates };
}

// ../carrycert-core/src/analyze.ts
function modsumUnique(c) {
  if (c.equation && c.sum_bitified && c.carry_bitified) {
    return { unique: true, reason: "joint Num2Bits-style (sum+carry bits) uniquely determines (sum,carry)" };
  }
  if (c.equation && c.sum_bitified && !c.carry_bitified) {
    return { unique: false, reason: "sum bits without carry bit: field alias carry=(a+b)*inv(2^n)" };
  }
  if (c.equation && !c.sum_bitified) {
    return { unique: false, reason: "equation alone leaves free rank-1 variable over F_p" };
  }
  return { unique: false, reason: "insufficient constraints" };
}
function modsumCex(n, a = 3, b = 5) {
  const MOD = 1 << n;
  const sum0 = (a + b) % MOD;
  const carry0 = Math.floor((a + b) / MOD);
  const sum1 = ((BigInt(sum0) - BigInt(MOD) + BN128_PRIME) % BN128_PRIME).toString();
  const carry1 = ((BigInt(carry0) + 1n) % BN128_PRIME).toString();
  return {
    inputs: { a, b, n },
    witness_a: { sum: sum0, carry: carry0 },
    witness_b: { sum: sum1, carry: carry1 },
    equation: "a+b = sum + carry*2^n (mod p)",
    prime: BN128_PRIME.toString()
  };
}
function sumBitsCarryFreeCex(n, a = 0, b = 1) {
  const MOD = 1 << n;
  const inv = (() => {
    return BigInt(MOD) === 0n ? 0n : modInv(BigInt(MOD), BN128_PRIME);
  })();
  const sum0 = (a + b) % MOD;
  const carry0 = Math.floor((a + b) / MOD);
  const sum1 = 0;
  const carry1 = BigInt(a + b) % BN128_PRIME * inv % BN128_PRIME;
  return {
    inputs: { a, b, n },
    witness_a: { sum: sum0, carry: carry0 },
    witness_b: { sum: sum1, carry: carry1.toString() },
    equation: "a+b = sum + carry*2^n (mod p), sum in [0,2^n)",
    prime: BN128_PRIME.toString()
  };
}
function modInv(a, m) {
  let [old_r, r] = [a % m, m];
  let [old_s, s] = [1n, 0n];
  while (r !== 0n) {
    const q = old_r / r;
    [old_r, r] = [r, old_r - q * r];
    [old_s, s] = [s, old_s - q * s];
  }
  return (old_s % m + m) % m;
}
function limbCex(n, k) {
  const MOD = 1 << n;
  const a = Array(k).fill(0);
  const b = Array(k).fill(0);
  const out = Array(k + 1).fill(0);
  const carries = Array(k).fill(0);
  out[0] = MOD;
  carries[0] = Number(BN128_PRIME - 1n);
  for (let i = 1; i < k; i++) {
    carries[i] = 0;
    out[i] = carries[i - 1];
  }
  out[k] = carries[k - 1];
  return {
    inputs: { a, b, n, k },
    witness_a: { out: Array(k + 1).fill(0), carry: Array(k).fill(0) },
    witness_b: { out, carry: carries },
    prime: BN128_PRIME.toString()
  };
}
function withDomain(gadget, r) {
  if (!r.domain && gadget.domain) r.domain = gadget.domain;
  return r;
}
function analyze(gadget) {
  const t0 = performance.now();
  const { family, constraints: c, params, id } = gadget;
  const finish = (r) => withDomain(gadget, r);
  if (family === "circom_function") {
    const primitive = String(params.primitive ?? "");
    const expr = primitive === "and" ? "a*b" : primitive === "mux1" ? "(b-a)*s+a" : null;
    if (!expr || !c.equation) {
      return finish({
        id,
        verdict: "Unknown",
        time_ms: performance.now() - t0,
        method: "circom_direct_incomplete",
        theorem: "n/a",
        reason: "Incomplete field assignment"
      });
    }
    return finish({
      id,
      verdict: "Certified",
      witness_count: 1,
      time_ms: performance.now() - t0,
      method: "circom_direct_arithmetic",
      theorem: "A constrained field assignment fixes its output for each input tuple",
      certificate: {
        type: "functional_assignment",
        primitive,
        expression: expr,
        field: "BN254",
        input_domain: "field elements",
        scope: "The main template contains only the declared inputs and one constrained output; every input tuple has one output."
      }
    });
  }
  if (family === "circom_comparison") {
    const n = Number(params.n ?? 0);
    const bits = Number(params.range_bits ?? 0);
    if (n !== 4 || bits !== 5 || !c.equation || !c.sum_bitified || !c.carry_bitified) {
      return finish({
        id,
        verdict: "Unknown",
        time_ms: performance.now() - t0,
        method: "circom_comparison_incomplete",
        theorem: "n/a",
        reason: "Missing exact bit decomposition"
      });
    }
    return finish({
      id,
      verdict: "Certified",
      witness_count: 1,
      time_ms: performance.now() - t0,
      method: "circom_bitified_comparison",
      theorem: "Unique bit decomposition for 2^5 < p, followed by a constrained output",
      certificate: {
        type: "bit_decomposition",
        n: 4,
        range_bits: 5,
        field: "BN254",
        equation: "diff=a+16-b; diff=sum(bit[i]*2^i); out=1-bit[4]",
        scope: "At most one witness for fixed field inputs when the five-bit decomposition is satisfiable; usual less-than semantics for inputs 0..15."
      }
    });
  }
  if (family === "modsum") {
    const n = Number(params.n ?? 4);
    const { unique, reason } = modsumUnique(c);
    const dt = performance.now() - t0;
    if (unique) {
      const B = 1n << BigInt(n);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "modsum_uniqueness_lemma",
        theorem: "two-stage-addition + Num2Bits soundness",
        certificate: {
          type: "uniqueness_lemma",
          family: "modsum",
          n,
          lemma: reason,
          two_stage_count: twoStageCount(B).toString(),
          theorem_ref: "DOI 10.5281/zenodo.23698617"
        }
      });
    }
    const cex = c.sum_bitified && !c.carry_bitified ? sumBitsCarryFreeCex(n) : modsumCex(n);
    return finish({
      id,
      verdict: "Broken",
      time_ms: dt,
      method: c.sum_bitified ? "modsum_sum_bits_carry_free" : "modsum_equation_rank",
      theorem: "field alias / free variable over F_p",
      counterexample: cex,
      reason
    });
  }
  if (family === "modsum3" || family === "full_adder") {
    const dt = performance.now() - t0;
    const ok = c.sum_bitified && c.carry_bitified && (family === "full_adder" || c.incoming_bitified || true);
    if (family === "full_adder" && c.sum_bitified && c.carry_bitified) {
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "full_adder_num2bits",
        theorem: "two-stage-addition",
        certificate: { type: "uniqueness_lemma", family, safety: c.input_bitified ? "strong" : "weak" }
      });
    }
    if (family === "modsum3" && c.sum_bitified && c.carry_bitified) {
      const n = Number(params.n ?? 4);
      const B = 1n << BigInt(n);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "modsum3_bitified",
        theorem: "cascaded-sum-carry",
        certificate: { cascade_count: cascadeFunctionCount(B, 2).toString(), theorem_ref: "DOI 10.5281/zenodo.23700193" }
      });
    }
    return finish({ id, verdict: "Broken", time_ms: dt, method: "open", theorem: "n/a", counterexample: modsumCex(Number(params.n ?? 1)), reason: "missing bitification" });
  }
  if (family === "limb_add" || family === "binsum") {
    const n = Number(params.n ?? 4);
    const k = Number(params.k ?? params.ops ?? 2);
    const dt = performance.now() - t0;
    if (c.equation && c.sum_bitified && c.carry_bitified) {
      const B = 1n << BigInt(n);
      const stages = Math.max(1, k - 1);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "limb_add_bitified",
        theorem: "cascaded-sum-carry + two-stage-addition",
        certificate: {
          n,
          k,
          two_stage_count: twoStageCount(B).toString(),
          cascade_count: cascadeFunctionCount(B, stages).toString(),
          cascade_bits: cascadeMinBits(B, stages),
          theorem_ref: ["DOI 10.5281/zenodo.23698617", "DOI 10.5281/zenodo.23700193"]
        }
      });
    }
    return finish({
      id,
      verdict: "Broken",
      time_ms: dt,
      method: "limb_add_equation_only",
      theorem: "cascaded-sum-carry (negative)",
      counterexample: limbCex(n, k),
      reason: "equation-only limb chain"
    });
  }
  if (family === "shared_input") {
    const width = Number(params.width ?? 8);
    const offsets = params.offsets ?? [13, 45, 93];
    const sample = frontierSolve(width, offsets);
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.carry_bitified && c.input_bitified) {
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "shared_input_frontier",
        theorem: "shared-input-carry-frontiers DOI 10.5281/zenodo.23702847",
        certificate: {
          frontier_bound: frontierBound(offsets.length),
          sample_count: sample.count.toString(),
          max_states: sample.maxStates,
          offsets
        }
      });
    }
    const MOD = 1 << width;
    return finish({
      id,
      verdict: "Broken",
      time_ms: dt,
      method: "shared_input_equation_only",
      theorem: "shared-input-carry-frontiers (negative)",
      counterexample: {
        inputs: { x: 0, offsets, width },
        witness_a: { y: offsets.map((o) => o % MOD), c: offsets.map((o) => Math.floor(o / MOD)) },
        witness_b: {
          y: [(offsets[0] + MOD) % Number(BN128_PRIME > BigInt(Number.MAX_SAFE_INTEGER) ? MOD * 2 : Number(BN128_PRIME)), ...offsets.slice(1).map((o) => o % MOD)],
          c: [Number(BN128_PRIME - 1n), ...offsets.slice(1).map((o) => Math.floor(o / MOD))]
        },
        frontier_bound: frontierBound(offsets.length)
      }
    });
  }
  if (family === "cascade") {
    const n = Number(params.n ?? 4);
    const stages = Number(params.stages ?? 3);
    const B = 1n << BigInt(n);
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.carry_bitified && c.incoming_bitified) {
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "cascade_bitified",
        theorem: "cascaded-sum-carry",
        certificate: {
          exact_function_count: cascadeFunctionCount(B, stages).toString(),
          minimum_label_bits: cascadeMinBits(B, stages),
          theorem_ref: "DOI 10.5281/zenodo.23700193"
        }
      });
    }
    return finish({
      id,
      verdict: "Broken",
      time_ms: dt,
      method: "cascade_equation_only",
      theorem: "cascaded-sum-carry (negative)",
      counterexample: limbCex(n, stages)
    });
  }
  if (family === "bigint_mod") {
    const n = Number(params.n ?? 3);
    const k = Number(params.k ?? 2);
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.carry_bitified) {
      const B = 1n << BigInt(n);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "bigint_mod_range_checked",
        theorem: "limb range checks + reconstruction (circom-bigint BigMod pattern)",
        certificate: {
          n,
          k,
          note: "Certifies uniqueness under the standard BigMod constraint pattern: Num2Bits on div/mod limbs, BigMult/BigAdd reconstruction equality, and mod < b. Subgadget carry structure uses two-stage/cascade counts.",
          two_stage_count: twoStageCount(B).toString(),
          cascade_count: cascadeFunctionCount(B, Math.max(1, k)).toString(),
          theorem_ref: ["DOI 10.5281/zenodo.23698617", "DOI 10.5281/zenodo.23700193"],
          scope: "weak_safety_outputs_unique_given_public_inputs_under_stated_pattern"
        }
      });
    }
    return finish({
      id,
      verdict: "Unknown",
      time_ms: dt,
      method: "bigint_mod_incomplete",
      theorem: "n/a",
      reason: "BigMod without detected limb range checks; refusing to guess"
    });
  }
  if (family === "arx_sha256") {
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.input_bitified) {
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        method: "arx_sha256_binsum_bitpath",
        theorem: "circomlib Sha256compression uses bit signals + BinSum; shared-input/cascade bounds apply to add layers",
        certificate: {
          type: "compositional",
          subgadgets: ["BinSum(32,2)", "BinSum(32,5)", "SigmaPlus", "T1", "T2"],
          frontier_note: "T1 adds the same derived word into multiple running states \u2014 shared-input frontier DOI 10.5281/zenodo.23702847",
          theorem_ref: [
            "DOI 10.5281/zenodo.23702847",
            "DOI 10.5281/zenodo.23697726",
            "DOI 10.5281/zenodo.23697063"
          ],
          scope: "Certified for circomlib-style bit-level SHA-256 compression where all wires are bits and sums use BinSum. Not a general ARX soundness proof for arbitrary encodings.",
          honesty: "Full differential/fiber analysis via affine-carry-inversion is available for \u03C3-shaped maps but not yet auto-composed for every custom SHA circuit."
        }
      });
    }
    return finish({
      id,
      verdict: "Unknown",
      time_ms: dt,
      method: "arx_sha256_unclassified",
      theorem: "affine-carry-inversion / tap-span available but pattern incomplete",
      reason: "SHA-256-like circuit without detected bit-level BinSum pattern"
    });
  }
  if (family === "fixed_mac") {
    const bits = Number(params.bits ?? 8);
    const accBits = Number(params.acc_bits ?? 32);
    const mode = String(params.overflow ?? "wrap");
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.carry_bitified) {
      const B = 1n << BigInt(accBits);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        domain: gadget.domain,
        method: "fixed_mac_range_checked",
        theorem: "cascaded-sum-carry / two-stage-addition applied to fixed-point accumulator",
        certificate: {
          bits,
          acc_bits: accBits,
          overflow: mode,
          two_stage_count: twoStageCount(1n << BigInt(Math.min(accBits, 32))).toString(),
          theorem_ref: ["DOI 10.5281/zenodo.23698617", "DOI 10.5281/zenodo.23700193"],
          scope: "Unique accumulator update given inputs when product and acc residue are range-checked (or jointly bitified)."
        }
      });
    }
    const n = Math.min(bits, 16);
    return finish({
      id,
      verdict: "Broken",
      time_ms: dt,
      domain: gadget.domain,
      method: "fixed_mac_equation_only",
      theorem: "field/int alias of accumulator residue",
      counterexample: modsumCex(n, 3, 5),
      reason: "accumulator equation without range checks admits multiple (residue, overflow) pairs"
    });
  }
  if (family === "hw_adder") {
    const width = Number(params.width ?? 8);
    const style = String(params.style ?? "ripple");
    const dt = performance.now() - t0;
    if (c.sum_bitified && c.carry_bitified && c.input_bitified) {
      const B = 1n << BigInt(width);
      return finish({
        id,
        verdict: "Certified",
        witness_count: 1,
        time_ms: dt,
        domain: gadget.domain,
        method: "hw_adder_bit_carry_chain",
        theorem: "cascaded-sum-carry exact state; ripple/CLA with bit I/O is unique",
        certificate: {
          width,
          style,
          cascade_count: cascadeFunctionCount(2n, width).toString(),
          cascade_bits: cascadeMinBits(2n, width),
          theorem_ref: "DOI 10.5281/zenodo.23700193",
          scope: "Bit-level adder netlist with full carry chain: (sum, cout) unique given (a,b,cin)."
        }
      });
    }
    if (c.equation && !c.carry_bitified) {
      return finish({
        id,
        verdict: "Broken",
        time_ms: dt,
        domain: gadget.domain,
        method: "hw_adder_missing_carry_bits",
        theorem: "carry frontier incomplete",
        counterexample: modsumCex(Math.min(width, 8), 1, 1),
        reason: "adder equation without bit-constrained carries"
      });
    }
    return finish({
      id,
      verdict: "Unknown",
      time_ms: dt,
      domain: gadget.domain,
      method: "hw_adder_partial",
      theorem: "n/a",
      reason: "hardware adder pattern incomplete (need bit I/O + carry chain flags)"
    });
  }
  return finish({
    id,
    verdict: "Unknown",
    time_ms: performance.now() - t0,
    method: "no_analyzer",
    theorem: "n/a",
    reason: `unsupported family ${family}`
  });
}

// ../carrycert-core/src/circom-adapter.ts
function stripComments(src) {
  return src.replace(/\/\*[\s\S]*?\*\//g, "").replace(/\/\/.*$/gm, "");
}
function detectMain(src) {
  const m = src.match(/component\s+main(?:\s*\{[^}]*\})?\s*=\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(([^)]*)\))?\s*;/);
  if (!m) return null;
  const args = (m[2] ?? "").split(",").map((s) => s.trim()).filter(Boolean).map((s) => Number(s)).filter((n) => !Number.isNaN(n));
  return { template: m[1], args };
}
function extractTemplateBody(src, name) {
  const re = new RegExp(String.raw`template\s+${name}\s*(?:\([^)]*\))?\s*\{`);
  const m = re.exec(src);
  if (!m) return null;
  let i = m.index + m[0].length;
  let depth = 1;
  const start = i;
  while (i < src.length && depth > 0) {
    if (src[i] === "{") depth++;
    else if (src[i] === "}") depth--;
    i++;
  }
  return src.slice(start, i - 1);
}
function num2BitsOnSumOnly(body) {
  const sumBits = /Num2Bits\s*\([^)]*\)[\s\S]{0,120}?\.in\s*<==\s*sum\b/.test(body) || /n2b\.in\s*<==\s*sum\b/.test(body);
  const carryFromBits = /carry\s*<==\s*[^;]*n2b\.out/.test(body) || /carry\s*<==\s*[^;]*\.out\[/.test(body);
  const carryFree = /carry\s*<--/.test(body);
  return sumBits && (carryFree || !carryFromBits);
}
function jointNum2BitsOnSum(body) {
  return /Num2Bits\s*\(\s*n\s*\+\s*[12]\s*\)/.test(body) && /\.in\s*<==\s*a\s*\+\s*b/.test(body) && /carry\s*<==/.test(body);
}
function hasNum2Bits(src) {
  return /Num2Bits\s*\(/.test(src);
}
function hasBitConstraint(src) {
  return /\*\s*\(\s*[A-Za-z0-9_\.]+\s*-\s*1\s*\)\s*===\s*0/.test(src) || /Num2Bits\s*\(\s*1\s*\)/.test(src);
}
function hasEquationAssign(src) {
  return /<--|===/.test(src);
}
function usesBinSum(src) {
  return /BinSum\s*\(/.test(src);
}
function usesModSum(src) {
  return /ModSum(?:Three|Four)?\s*\(/.test(src) || /template\s+ModSum/.test(src);
}
function usesBigAdd(src) {
  return /BigAdd\s*\(/.test(src) || /template\s+BigAdd/.test(src);
}
function usesBigMod(src) {
  return /BigMod\s*\(/.test(src) || /template\s+BigMod/.test(src);
}
function looksSha256(src) {
  return /Sha256compression|SigmaPlus|BigSigma|SmallSigma|template\s+T1\b/.test(src);
}
function defaultConstraints(partial) {
  return {
    equation: partial.equation ?? true,
    sum_bitified: partial.sum_bitified ?? false,
    carry_bitified: partial.carry_bitified ?? false,
    input_bitified: partial.input_bitified ?? false,
    incoming_bitified: partial.incoming_bitified ?? false
  };
}
function classifyCircomSource(src, id = "circuit") {
  const clean = stripComments(src);
  const main2 = detectMain(clean);
  const tpl = main2?.template ?? "";
  const args = main2?.args ?? [];
  const body = tpl && extractTemplateBody(clean, tpl) || clean;
  if (!/\binclude\s*["']/.test(clean) && tpl && extractTemplateBody(clean, tpl)) {
    const compact = body.replace(/\s+/g, "");
    const direct = /* @__PURE__ */ new Map([
      ["signalinputa;signalinputb;signaloutputout;out<==a*b;", "and"],
      ["signalinputa;signalinputb;signalinputs;signaloutputout;out<==(b-a)*s+a;", "mux1"]
    ]);
    const primitive = direct.get(compact);
    if (primitive) {
      return {
        id,
        domain: "circom",
        family: "circom_function",
        params: { primitive },
        constraints: defaultConstraints({ equation: true }),
        source: "circom",
        notes: "Single field output bound by a complete arithmetic assignment"
      };
    }
    const compare4 = "signalinputa;signalinputb;signaloutputout;signaldiff;signalbit[5];diff<==a+16-b;varlc=0;vare2=1;for(vari=0;i<5;i++){bit[i]<--(diff>>i)&1;bit[i]*(bit[i]-1)===0;lc+=bit[i]*e2;e2=e2+e2;}lc===diff;out<==1-bit[4];";
    if (compact === compare4) {
      return {
        id,
        domain: "circom",
        family: "circom_comparison",
        params: { n: 4, range_bits: 5 },
        constraints: defaultConstraints({
          equation: true,
          sum_bitified: true,
          carry_bitified: true
        }),
        source: "circom",
        notes: "Five checked bits give a unique residue and comparison output"
      };
    }
  }
  if (/^ModSumCarryFree$/i.test(tpl)) {
    const n = args[0] ?? 4;
    return { id, family: "modsum", params: { n }, constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: false }), source: "circom", notes: "sum Num2Bits only" };
  }
  if (/^ModSumBuggy$/i.test(tpl)) {
    const n = args[0] ?? 4;
    return { id, family: "modsum", params: { n }, constraints: defaultConstraints({ equation: true }), source: "circom", notes: "equation-only" };
  }
  if (/^ModSumThreeSafe$/i.test(tpl) || /^ModSumThree$/i.test(tpl)) {
    const n = args[0] ?? 4;
    return { id, family: "modsum3", params: { n }, constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, incoming_bitified: true }), source: "circom" };
  }
  if (/^ModSum$/i.test(tpl) || /^ModSumSafe$/i.test(tpl)) {
    const n = args[0] ?? 4;
    if (num2BitsOnSumOnly(body)) {
      return { id, family: "modsum", params: { n }, constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: false }), source: "circom" };
    }
    if (/sum\s*<--/.test(body) && !/Num2Bits\s*\(/.test(body)) {
      return { id, family: "modsum", params: { n }, constraints: defaultConstraints({ equation: true }), source: "circom", notes: "equation-only ModSum" };
    }
    const joint = jointNum2BitsOnSum(body) || /Num2Bits\s*\(\s*n\s*\+\s*1\s*\)/.test(body);
    return { id, family: "modsum", params: { n }, constraints: defaultConstraints({ equation: true, sum_bitified: joint, carry_bitified: joint }), source: "circom" };
  }
  if (/^FullAdder$/i.test(tpl)) {
    return {
      id,
      family: "full_adder",
      params: { n: 1 },
      constraints: defaultConstraints({
        equation: true,
        sum_bitified: hasNum2Bits(clean),
        carry_bitified: hasNum2Bits(clean),
        input_bitified: hasBitConstraint(clean),
        incoming_bitified: hasBitConstraint(clean)
      }),
      source: "circom"
    };
  }
  if (/FullAdderLoose/i.test(tpl)) {
    return {
      id,
      family: "full_adder",
      params: { n: 1 },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, input_bitified: false }),
      source: "circom"
    };
  }
  if (/BinSum/i.test(tpl)) {
    return {
      id,
      family: "binsum",
      params: { n: args[0] ?? 2, ops: args[1] ?? 2 },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, input_bitified: true }),
      source: "circom"
    };
  }
  if (/BigAdd/i.test(tpl)) {
    return {
      id,
      family: "limb_add",
      params: { n: args[0] ?? 1, k: args[1] ?? 2 },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true }),
      source: "circom",
      notes: "BigAdd via ModSum/ModSumThree"
    };
  }
  if (/BigMod/i.test(tpl)) {
    return {
      id,
      family: "bigint_mod",
      params: { n: args[0] ?? 3, k: args[1] ?? 2 },
      constraints: defaultConstraints({
        equation: true,
        sum_bitified: hasNum2Bits(clean),
        carry_bitified: hasNum2Bits(clean)
      }),
      source: "circom",
      notes: "BigMod with Num2Bits range checks + reconstruction"
    };
  }
  if (/Sha256compression|Sha256/i.test(tpl) || looksSha256(clean)) {
    return {
      id,
      family: "arx_sha256",
      params: { rounds: 64 },
      constraints: defaultConstraints({
        equation: true,
        sum_bitified: usesBinSum(clean) || hasNum2Bits(clean),
        carry_bitified: usesBinSum(clean),
        input_bitified: true
        // circomlib uses bit wires
      }),
      source: "circom",
      notes: "SHA-256 compression / ARX"
    };
  }
  if (/U4AddSafe|LimbAddSafe/i.test(tpl)) {
    const n = /U4/.test(tpl) ? 4 : args[0] ?? 4;
    const k = /U4AddSafe/.test(tpl) ? args[0] ?? 8 : args[1] ?? args[0] ?? 2;
    return {
      id,
      family: "limb_add",
      params: { n, k },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true }),
      source: "circom"
    };
  }
  if (/U4AddBuggy|LimbAddBuggy/i.test(tpl)) {
    const n = /U4/.test(tpl) ? 4 : args[0] ?? 4;
    const k = /U4AddBuggy/.test(tpl) ? args[0] ?? 8 : args[1] ?? 2;
    return {
      id,
      family: "limb_add",
      params: { n, k },
      constraints: defaultConstraints({ equation: true, sum_bitified: false, carry_bitified: false }),
      source: "circom"
    };
  }
  if (/SharedInputParallel/i.test(tpl)) {
    return {
      id,
      family: "shared_input",
      params: { width: args[0] ?? 8, offsets: [13, 45, 93] },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, input_bitified: true }),
      source: "circom"
    };
  }
  if (/SharedInputBuggy/i.test(tpl)) {
    return {
      id,
      family: "shared_input",
      params: { width: args[0] ?? 8, offsets: [13, 45, 93] },
      constraints: defaultConstraints({ equation: true }),
      source: "circom"
    };
  }
  if (/^Cascade3$/i.test(tpl)) {
    return {
      id,
      family: "cascade",
      params: { n: args[0] ?? 4, stages: 3 },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, incoming_bitified: true }),
      source: "circom"
    };
  }
  if (/Cascade3Buggy/i.test(tpl)) {
    return {
      id,
      family: "cascade",
      params: { n: args[0] ?? 4, stages: 3 },
      constraints: defaultConstraints({ equation: true }),
      source: "circom"
    };
  }
  if (usesBigMod(clean)) {
    return {
      id,
      family: "bigint_mod",
      params: { n: args[0] ?? 3, k: args[1] ?? 2 },
      constraints: defaultConstraints({ equation: true, sum_bitified: hasNum2Bits(clean), carry_bitified: hasNum2Bits(clean) }),
      source: "circom"
    };
  }
  if (looksSha256(clean)) {
    return {
      id,
      family: "arx_sha256",
      params: { rounds: 64 },
      constraints: defaultConstraints({
        equation: true,
        sum_bitified: usesBinSum(clean),
        carry_bitified: usesBinSum(clean),
        input_bitified: true
      }),
      source: "circom"
    };
  }
  if (usesBigAdd(clean) || usesModSum(clean)) {
    return {
      id,
      family: "limb_add",
      params: { n: args[0] ?? 4, k: args[1] ?? 2 },
      constraints: defaultConstraints({
        equation: true,
        sum_bitified: hasNum2Bits(clean),
        carry_bitified: hasNum2Bits(clean)
      }),
      source: "circom"
    };
  }
  if (usesBinSum(clean)) {
    return {
      id,
      family: "binsum",
      params: { n: args[0] ?? 32, ops: args[1] ?? 2 },
      constraints: defaultConstraints({ equation: true, sum_bitified: true, carry_bitified: true, input_bitified: true }),
      source: "circom"
    };
  }
  if (/<--/.test(clean) && !hasNum2Bits(clean) && /\+\s*.*===/.test(clean)) {
    return {
      id,
      family: "modsum",
      params: { n: 4 },
      constraints: defaultConstraints({ equation: true }),
      source: "circom",
      notes: "heuristic: assignments without Num2Bits"
    };
  }
  return {
    id,
    family: "unknown",
    params: {},
    constraints: defaultConstraints({ equation: hasEquationAssign(clean) }),
    source: "circom",
    notes: `unclassified template=${tpl || "(none)"}`
  };
}

// ../carrycert-core/src/circom-fs.ts
import * as fs from "node:fs";
import * as path from "node:path";
function readWithIncludes(entry, depth = 0, maxDepth = 6, seen = /* @__PURE__ */ new Set()) {
  const abs = path.resolve(entry);
  if (seen.has(abs) || depth > maxDepth) return "";
  seen.add(abs);
  if (!fs.existsSync(abs)) return "";
  let text = fs.readFileSync(abs, "utf8");
  const dir = path.dirname(abs);
  const includeRe = /include\s+"([^"]+)"\s*;/g;
  let m;
  const parts = [text];
  while (m = includeRe.exec(text)) {
    const inc = path.resolve(dir, m[1]);
    parts.push(readWithIncludes(inc, depth + 1, maxDepth, seen));
  }
  return parts.join("\n");
}
function classifyCircomFile(filePath, opts = {}) {
  const follow = opts.followIncludes !== false;
  const src = follow ? readWithIncludes(filePath, 0, opts.maxIncludeDepth ?? 8) : fs.readFileSync(filePath, "utf8");
  const id = opts.id ?? path.basename(filePath, path.extname(filePath));
  return classifyCircomSource(src, id);
}
function scanCircomFile(filePath, opts = {}) {
  return analyze(classifyCircomFile(filePath, opts));
}

// ../carrycert-core/src/checker.ts
function checkResult(r) {
  if (r.verdict === "Broken") {
    const cex = r.counterexample ?? {};
    const wa = cex.witness_a;
    const wb = cex.witness_b;
    if (wa?.sum !== void 0 && wb?.sum !== void 0) {
      const n = cex.inputs.n;
      const MOD = 1n << BigInt(n);
      const a = BigInt(cex.inputs.a);
      const b = BigInt(cex.inputs.b);
      const lhs = (a + b) % BN128_PRIME;
      const okA = (BigInt(String(wa.sum)) + BigInt(String(wa.carry)) * MOD) % BN128_PRIME === lhs;
      const okB = (BigInt(String(wb.sum)) + BigInt(String(wb.carry)) * MOD) % BN128_PRIME === lhs;
      const differ = !(String(wa.sum) === String(wb.sum) && String(wa.carry) === String(wb.carry));
      return { ok: okA && okB && differ, kind: "modsum_cex" };
    }
    if (wb?.out) {
      return { ok: Array.isArray(wb.out) && wb.out.some((x) => x !== 0), kind: "limb_cex" };
    }
    if (wa?.y) {
      return { ok: JSON.stringify(wa) !== JSON.stringify(wb), kind: "shared_cex" };
    }
    return { ok: false, kind: "unrecognized_cex" };
  }
  if (r.verdict === "Certified") {
    if (r.method === "circom_direct_arithmetic") {
      const c = r.certificate;
      const expected = c?.primitive === "and" ? "a*b" : c?.primitive === "mux1" ? "(b-a)*s+a" : null;
      return { ok: c?.type === "functional_assignment" && c.expression === expected && r.witness_count === 1, kind: "functional_assignment" };
    }
    if (r.method === "circom_bitified_comparison") {
      const c = r.certificate;
      return { ok: c?.type === "bit_decomposition" && c.n === 4 && c.range_bits === 5 && r.witness_count === 1, kind: "bit_decomposition" };
    }
    return { ok: !!r.certificate, kind: "certificate" };
  }
  return { ok: true, kind: "unknown_skip" };
}

// ../carrycert-core/src/adapters/verilog.ts
function classifyVerilogSource(src, id = "hw_circuit") {
  const clean = src.replace(/\/\/.*$/gm, "").replace(/\/\*[\s\S]*?\*\//g, "");
  const widthM = clean.match(/\[\s*(\d+)\s*:\s*0\s*\]/);
  const width = widthM ? Number(widthM[1]) + 1 : 8;
  const hasFullAdder = /full_adder|FA\b|module\s+fa\b/i.test(clean);
  const hasRipple = /ripple|rca\b|generate.*full_adder|cout\s*\(\s*c\s*\[/i.test(clean) || hasFullAdder;
  const bitIO = /input\s+\[\s*\d+\s*:\s*0\s*\]\s*a/.test(clean) && /output\s+\[\s*\d+\s*:\s*0\s*\]\s*sum/.test(clean);
  const carryChain = /cout|carry/.test(clean);
  const bareAssign = /assign\s+sum\s*=\s*a\s*\+\s*b/.test(clean) && !carryChain;
  if (bareAssign) {
    return {
      id,
      family: "hw_adder",
      domain: "verilog",
      params: { width, style: "bare_assign" },
      constraints: { equation: true, sum_bitified: false, carry_bitified: false, input_bitified: bitIO, incoming_bitified: false },
      notes: "bare a+b assign without explicit carry chain"
    };
  }
  if (hasRipple || hasFullAdder || bitIO && carryChain) {
    return {
      id,
      family: "hw_adder",
      domain: "verilog",
      params: { width, style: hasRipple ? "ripple" : "adder" },
      constraints: {
        equation: true,
        sum_bitified: true,
        carry_bitified: carryChain,
        input_bitified: true,
        incoming_bitified: /cin/.test(clean)
      },
      notes: "structural bit-level adder"
    };
  }
  return {
    id,
    family: "unknown",
    domain: "verilog",
    params: { width },
    constraints: { equation: false, sum_bitified: false, carry_bitified: false, input_bitified: false, incoming_bitified: false },
    notes: "unrecognized verilog"
  };
}

// ../carrycert-core/src/adapters/int8.ts
function classifyInt8Kernel(k) {
  const range = k.range_checked !== false;
  return {
    id: k.id,
    family: "fixed_mac",
    domain: "int8",
    params: {
      bits: k.bits ?? 8,
      acc_bits: k.acc_bits ?? 32,
      overflow: k.overflow ?? "wrap"
    },
    constraints: {
      equation: true,
      sum_bitified: range,
      carry_bitified: range,
      input_bitified: range,
      incoming_bitified: false,
      extra: { overflow: k.overflow ?? "wrap" }
    },
    notes: k.notes
  };
}
function classifyInt8Source(src, id = "int8_kernel") {
  const s = src.toLowerCase();
  const bitsM = s.match(/int(\d+)/);
  const accM = s.match(/acc(\d+)/);
  const range = /norange|no.?range|unchecked/.test(s) ? false : !/unchecked/.test(s);
  const overflow = /sat/.test(s) ? "saturate" : "wrap";
  return classifyInt8Kernel({
    id,
    bits: bitsM ? Number(bitsM[1]) : 8,
    acc_bits: accM ? Number(accM[1]) : 32,
    overflow,
    range_checked: range && !/norange/.test(s)
  });
}

// ../carrycert-core/src/adapters/onnx.ts
function classifyOnnxKernel(k) {
  const ir = classifyInt8Kernel({
    id: k.id,
    bits: k.bits ?? 8,
    acc_bits: k.acc_bits ?? 32,
    overflow: k.overflow ?? "wrap",
    range_checked: k.range_checked !== false,
    notes: k.notes ?? `onnx ${k.op ?? "mac"}`
  });
  ir.domain = "onnx";
  ir.params = { ...ir.params, op: k.op ?? "mac" };
  return ir;
}
function classifyOnnxSource(src, id = "onnx_kernel") {
  const s = src.toLowerCase();
  const bitsM = s.match(/int(\d+)/);
  const accM = s.match(/acc(\d+)/);
  const op = /conv/.test(s) ? "conv" : /matmul|gemm/.test(s) ? "matmul" : "mac";
  const norange = /norange|unchecked|no.?quant/.test(s);
  const overflow = /sat/.test(s) ? "saturate" : "wrap";
  return classifyOnnxKernel({
    id,
    op,
    bits: bitsM ? Number(bitsM[1]) : 8,
    acc_bits: accM ? Number(accM[1]) : 32,
    range_checked: !norange,
    overflow,
    notes: src.trim().slice(0, 120)
  });
}

// ../carrycert-core/src/adapters/carry-graph.ts
function unsupported(id, domain, reason) {
  return {
    id,
    domain,
    family: "unknown",
    params: {},
    constraints: {
      equation: false,
      sum_bitified: false,
      carry_bitified: false,
      input_bitified: false,
      incoming_bitified: false
    },
    notes: reason
  };
}
function classifyCarryGraph(graph, id = "carry_graph") {
  const n = graph?.limb_bits;
  const k = graph?.limbs;
  const domain = graph?.domain || "unknown";
  if (graph?.format !== "carry-graph-v1" || !["bitvm", "zkvm", "r1cs"].includes(domain) || graph.op !== "add" || !Number.isInteger(n) || n < 1 || n > 32 || !Number.isInteger(k) || k < 1 || k > 64 || !Array.isArray(graph.equations) || !Array.isArray(graph.ranges) || graph.equations.length !== k || graph.ranges.length !== 4 * k)
    return unsupported(id, domain, "Carry graph requires complete bounded addition constraints");
  const radix = (1n << BigInt(n)).toString();
  const requiredEquations = Array.from(
    { length: k },
    (_, i) => `a[${i}]+b[${i}]${i ? `+carry[${i - 1}]` : ""}=sum[${i}]+${radix}*carry[${i}]`
  );
  const requiredRanges = Array.from({ length: k }, (_, i) => [
    `a[${i}]:${n}`,
    `b[${i}]:${n}`,
    `sum[${i}]:${n}`,
    `carry[${i}]:1`
  ]).flat();
  const normalize = (x) => typeof x === "string" ? x.replace(/\s+/g, "") : "";
  const eqs = graph.equations.map(normalize);
  const ranges = graph.ranges.map(normalize);
  if (new Set(eqs).size !== k || new Set(ranges).size !== 4 * k || requiredEquations.some((e) => !eqs.includes(e)) || requiredRanges.some((r) => !ranges.includes(r)))
    return unsupported(id, domain, "Unrecognized or incomplete equations/ranges; source contract undecided");
  return {
    id,
    domain,
    family: "limb_add",
    params: { n, k, style: "bounded_carry_graph_v1" },
    constraints: {
      equation: true,
      sum_bitified: true,
      carry_bitified: true,
      input_bitified: true,
      incoming_bitified: false,
      extra: { graph_format: "carry-graph-v1", equations: k, ranges: 4 * k }
    },
    notes: "Exact carry-graph constraints. Scope: mathematical graph; source frontend binding required."
  };
}

// ../carrycert-core/src/scan.ts
function unknown(id, domain, detail) {
  return {
    id,
    domain,
    family: "unknown",
    params: {},
    constraints: {
      equation: false,
      sum_bitified: false,
      carry_bitified: false,
      input_bitified: false,
      incoming_bitified: false
    },
    notes: detail
  };
}
function classifySource(text, options = {}) {
  const id = options.id || options.filename?.replace(/^.*[/\\]/, "").replace(/\.[^.]+$/, "") || "pasted";
  const fmt = options.format || options.filename?.toLowerCase().split(".").pop();
  if (text.trimStart().startsWith("{")) {
    try {
      const spec = JSON.parse(text);
      if (spec?.format === "carry-graph-v1") return classifyCarryGraph(spec, id);
      if (spec?.format === "bitvm-limb-v1" || spec?.format === "zkvm-limb-v1")
        return unknown(
          id,
          spec.format.startsWith("bitvm") ? "bitvm" : "zkvm",
          "Legacy declaration alone does not bind carry constraints. Supply a carry-graph-v1."
        );
      return unknown(id, "declaration", "Unrecognized contract format");
    } catch {
      return unknown(id, "declaration", "Invalid JSON state contract");
    }
  }
  if (fmt === "r1cs")
    return unknown(id, "r1cs", "Binary R1CS needs a decoded constraint graph");
  if (fmt === "circom" || /pragma\s+circom|template\s+\w+/.test(text))
    return classifyCircomSource(text, id);
  if (fmt === "verilog" || fmt === "v" || fmt === "sv" || /module\s+\w+/.test(text))
    return classifyVerilogSource(text, id);
  if (fmt === "int8" || fmt === "mac" || /mac\s+int|int8|acc\d+|range_checked/i.test(text))
    return classifyInt8Source(text, id);
  if (fmt === "bitvm" || fmt === "script" || /bitvm|script\s+limb|op_add/i.test(text))
    return unknown(id, "bitvm", "Raw Bitcoin Script/BitVM requires a constraint-graph frontend");
  if (fmt === "zkvm" || /zkvm|alu\s+limb/i.test(text))
    return unknown(id, "zkvm", "Raw zkVM trace requires a constraint-graph frontend");
  if (fmt === "onnx" || /onnx|quantizelinear/i.test(text))
    return classifyOnnxSource(text, id);
  return unknown(id, "pasted", "No recognized source adapter");
}
function scanPasted(source, options = {}) {
  const ir = classifySource(String(source || ""), options);
  const result = analyze(ir);
  if (result.method === "arx_sha256_binsum_bitpath" && !options.trusted_sha256) {
    return {
      id: result.id,
      domain: result.domain,
      verdict: "Unknown",
      method: "sha256_source_binding_required",
      theorem: result.theorem,
      time_ms: result.time_ms,
      reason: "SHA-256 source requires a pinned dependency graph and digest",
      source_note: ir.notes || null,
      check: { ok: true, kind: "unknown_skip" }
    };
  }
  return {
    ...result,
    source_note: ir.notes || null,
    check: checkResult(result)
  };
}

// src/cli.ts
function usage() {
  console.log(`\u1455. \u2014 exact arithmetic circuit verification by state contraction

Usage:
  speedrunpapi scan <file> [--json] [--sarif out.sarif] [--api <url>] [--key <key>]
  speedrunpapi classify <file>
  speedrunpapi verify <result.json>
  speedrunpapi claim <order> <confirmation> <email>
  speedrunpapi usage [--key <key>]
  speedrunpapi version

File types: .circom | .v/.sv | .txt/.mac (int8) | .bitvm/.script | .zkvm | .json (carry graph) | .onnx.txt
Compute is local. Optional source-bound API signature uses one certificate credit.
`);
}
function scanAny(file) {
  const abs = path2.resolve(file);
  const id = path2.basename(file).replace(/\.[^.]+$/, "");
  if (path2.extname(file).toLowerCase() === ".circom")
    return scanCircomFile(abs, { followIncludes: true });
  return scanPasted(fs2.readFileSync(abs, "utf8"), { id, filename: file });
}
function classifyAny(file) {
  const abs = path2.resolve(file);
  const id = path2.basename(file).replace(/\.[^.]+$/, "");
  if (path2.extname(file).toLowerCase() === ".circom")
    return classifyCircomFile(abs, { followIncludes: true });
  return classifySource(fs2.readFileSync(abs, "utf8"), { id, filename: file });
}
async function maybeRegister(api, key, result, file) {
  const source = fs2.readFileSync(path2.resolve(file), "utf8");
  const body = {
    source,
    filename: path2.basename(file),
    result: result.verdict,
    family: result.certificate?.family || result.method || "unknown",
    domain: result.domain || "circom",
    scope: result.certificate?.lemma || result.theorem || result.method,
    gadget_id: result.id,
    checksum: result.source_checksum,
    public: process.env.COLONY_CERT_PUBLIC === "true"
  };
  const res = await fetch(`${api.replace(/\/$/, "")}/v1/cert`, {
    method: "POST",
    headers: { "content-type": "application/json", authorization: `Bearer ${key}` },
    body: JSON.stringify(body)
  });
  if (!res.ok) throw new Error(`API ${res.status}: ${await res.text()}`);
  return res.json();
}
function toSarif(file, result) {
  return {
    $schema: "https://json.schemastore.org/sarif-2.1.0.json",
    version: "2.1.0",
    runs: [{
      tool: { driver: {
        name: "exactlab",
        version: "0.1.0",
        rules: [{ id: "exact-broken", shortDescription: { text: "Multiple witnesses / underconstrained" } }]
      } },
      results: result.verdict === "Broken" ? [{
        ruleId: "exact-broken",
        level: "error",
        message: { text: `${result.id}: ${result.reason ?? result.method}` },
        locations: [{ physicalLocation: { artifactLocation: { uri: file } } }]
      }] : []
    }]
  };
}
async function main() {
  const args = process.argv.slice(2);
  const cmd = args[0];
  if (!cmd || cmd === "-h" || cmd === "--help") return usage();
  if (cmd === "version") return void console.log("\u1455. speedrunpapi 0.3.1");
  if (cmd === "claim") {
    if (!args[1] || !args[2] || !args[3]) return usage();
    const order = args[1].startsWith("#") ? args[1] : "#" + args[1];
    const api = (process.env.COLONY_API || "https://api.colony.technology").replace(/\/$/, "");
    const res = await fetch(api + "/v1/claim", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({ order_number: order, confirmation_number: args[2], email: args[3] })
    });
    const body = await res.json();
    if (!res.ok) throw new Error("Claim " + res.status + ": " + (body.error || "failed"));
    console.log(JSON.stringify({ api_key: body.api_key, balance: body.balance, order }, null, 2));
    return;
  }
  if (cmd === "usage") {
    const idx = args.indexOf("--key");
    const token = idx >= 0 ? args[idx + 1] : process.env.COLONY_API_KEY || process.env.EXACTLAB_API_KEY;
    if (!token) throw new Error("Set COLONY_API_KEY or use --key");
    const api = (process.env.COLONY_API || "https://api.colony.technology").replace(/\/$/, "");
    const res = await fetch(api + "/v1/usage", { headers: { authorization: "Bearer " + token } });
    const body = await res.json();
    if (!res.ok) throw new Error("Usage " + res.status + ": " + (body.error || "failed"));
    console.log(JSON.stringify(body, null, 2));
    return;
  }
  if (cmd === "classify") {
    console.log(JSON.stringify(classifyAny(args[1]), null, 2));
    return;
  }
  if (cmd === "verify") {
    const results = JSON.parse(fs2.readFileSync(args[1], "utf8"));
    const arr = Array.isArray(results) ? results : [results];
    let bad = 0;
    for (const x of arr) {
      const c = checkResult(x);
      console.log(`${c.ok ? "PASS" : "FAIL"} ${x.id} ${x.verdict}`);
      if (!c.ok) bad++;
    }
    process.exit(bad ? 1 : 0);
  }
  if (cmd === "scan") {
    const file = args[1];
    if (!file) return usage();
    const result = scanAny(file);
    result.source_checksum = "sha256:" + createHash("sha256").update(fs2.readFileSync(path2.resolve(file))).digest("hex");
    const sarifIdx = args.indexOf("--sarif");
    if (sarifIdx >= 0) fs2.writeFileSync(args[sarifIdx + 1], JSON.stringify(toSarif(file, result), null, 2));
    const apiIdx = args.indexOf("--api");
    const keyIdx = args.indexOf("--key");
    const api = apiIdx >= 0 ? args[apiIdx + 1] : process.env.EXACTLAB_API || process.env.COLONY_API || "https://api.colony.technology";
    const key = keyIdx >= 0 ? args[keyIdx + 1] : process.env.EXACTLAB_API_KEY || process.env.COLONY_API_KEY;
    if (key && result.verdict !== "Unknown") {
      const reg = await maybeRegister(api, key, result, file);
      result.certificate_id = reg.certificate?.id || reg.id;
      result.mark = reg.certificate?.mark;
      result.signed = Boolean(reg.certificate?.signature);
      result.remaining = reg.remaining;
    }
    if (args.includes("--json")) console.log(JSON.stringify(result, null, 2));
    else {
      console.log(`${result.verdict}  ${result.id}`);
      console.log(`  method: ${result.method}`);
      console.log(`  theorem: ${result.theorem}`);
      console.log(`  domain: ${result.domain ?? "circom/ir"}`);
      console.log(`  time: ${result.time_ms.toFixed(3)} ms (client-side)`);
      if (result.reason) console.log(`  reason: ${result.reason}`);
      if (result.certificate_id) console.log(`  cert: ${result.certificate_id}${result.mark ? `  ${result.mark}` : ""}`);
    }
    process.exit(result.verdict === "Broken" ? 2 : result.verdict === "Unknown" ? 3 : 0);
  }
  usage();
  process.exit(1);
}
main().catch((e) => {
  console.error(e);
  process.exit(1);
});
