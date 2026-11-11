#!/usr/bin/env node

// src/cli.ts
import * as fs3 from "node:fs";
import * as path3 from "node:path";
import { createHash as createHash2 } from "node:crypto";

// ../carrycert-core/src/scan.ts
function unknown(id, domain, method, reason) {
  return {
    id,
    domain,
    verdict: "Unknown",
    method,
    theorem: "No claim.",
    time_ms: 0,
    reason,
    source_note: null,
    check: { ok: true, kind: "unknown_skip" }
  };
}
var CIRCOM_GUIDANCE = "A verdict about Circom source is a verdict about its compiled constraint system. Run `speedrunpapi scan file.circom` where the circom compiler is installed, or scan the compiled .r1cs.";
var RETIRED_GUIDANCE = "Versions before 0.7.1 returned verdicts for this input type without establishing them. That path has been removed. The scanner analyses Circom (through the compiler) and binary R1CS.";
function scanPasted(source, options = {}) {
  const input = String(source || "");
  const ext = options.format || options.filename?.toLowerCase().split(".").pop();
  const id = options.id || options.filename?.replace(/^.*[/\\]/, "").replace(/\.[^.]+$/, "") || "pasted";
  const trimmed = input.trimStart();
  if (ext === "circom" || /\bpragma\s+circom\b|\btemplate\s+\w+\s*\(/.test(input))
    return unknown(id, "circom", "circom_needs_compiler", CIRCOM_GUIDANCE);
  if (ext === "r1cs" || trimmed.startsWith("r1cs"))
    return unknown(id, "r1cs", "r1cs_needs_binary", "R1CS is a binary format; submit the file bytes, not text.");
  const domain = ext === "v" || ext === "sv" || ext === "verilog" ? "verilog" : ext === "bitvm" || ext === "script" ? "bitvm" : ext === "zkvm" ? "zkvm" : "unsupported";
  return unknown(id, domain, "unsupported_input", RETIRED_GUIDANCE);
}

// ../carrycert-core/src/determinism/ff.ts
function mod(a, p) {
  const r = a % p;
  return r < 0n ? r + p : r;
}
function modPow(base, exp, p) {
  let b = mod(base, p), e = exp, out = 1n;
  while (e > 0n) {
    if (e & 1n) out = out * b % p;
    b = b * b % p;
    e >>= 1n;
  }
  return out;
}
function modInv(a, p) {
  let r0 = mod(a, p), r1 = p;
  if (r0 === 0n) throw new Error("inverse of zero");
  let s0 = 1n, s1 = 0n;
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1n) throw new Error("modulus is not prime");
  return mod(s0, p);
}
function balanced(a, p) {
  const r = mod(a, p);
  return r > p >> 1n ? r - p : r;
}
function abs(a) {
  return a < 0n ? -a : a;
}
var nonResidue = /* @__PURE__ */ new Map();
function modSqrt(a, p) {
  const n2 = mod(a, p);
  if (n2 === 0n) return 0n;
  if (p === 2n) return n2;
  if (modPow(n2, p - 1n >> 1n, p) !== 1n) return null;
  if ((p & 3n) === 3n) return modPow(n2, p + 1n >> 2n, p);
  let q = p - 1n, s = 0n;
  while ((q & 1n) === 0n) {
    q >>= 1n;
    s++;
  }
  let z = nonResidue.get(p);
  if (z === void 0) {
    z = 2n;
    while (modPow(z, p - 1n >> 1n, p) !== p - 1n) {
      if (++z > 4096n) return null;
    }
    nonResidue.set(p, z);
  }
  let m = s, c = modPow(z, q, p), t = modPow(n2, q, p), r = modPow(n2, q + 1n >> 1n, p);
  while (t !== 1n) {
    let i = 0n, t2 = t;
    while (t2 !== 1n) {
      t2 = t2 * t2 % p;
      i++;
      if (i === m) return null;
    }
    const b = modPow(c, 1n << m - i - 1n, p);
    m = i;
    c = b * b % p;
    t = t * c % p;
    r = r * b % p;
  }
  return r;
}
function superIncreasingUnder(weights, scale, p) {
  if (mod(scale, p) === 0n) return false;
  const h = weights.map((g) => abs(balanced(g * scale, p)));
  h.sort((x, y) => x < y ? -1 : x > y ? 1 : 0);
  let prefix = 0n;
  for (const v of h) {
    if (v <= prefix) return false;
    prefix += v;
  }
  return prefix < p;
}
function findSuperIncreasingScale(weights, p, maxTries = 64) {
  if (!weights.length) return null;
  if (weights.some((g) => mod(g, p) === 0n)) return null;
  if (superIncreasingUnder(weights, 1n, p)) return 1n;
  const tried = /* @__PURE__ */ new Set([1n]);
  const order = weights.map((g, i) => ({ i, m: abs(balanced(g, p)) })).sort((x, y) => x.m < y.m ? -1 : x.m > y.m ? 1 : 0);
  let tries = 0;
  for (const { i } of order) {
    if (tries++ >= maxTries) break;
    const scale = modInv(weights[i], p);
    if (tried.has(scale)) continue;
    tried.add(scale);
    if (superIncreasingUnder(weights, scale, p)) return scale;
  }
  return null;
}

// ../carrycert-core/src/determinism/r1cs.ts
var DEFAULT_LIMITS = {
  maxBytes: 1 << 30,
  maxWires: 1 << 26,
  maxConstraints: 1 << 26,
  maxTerms: 1 << 28,
  allowUnlistedPrime: false
};
var CIRCOM_PRIMES = /* @__PURE__ */ new Map([
  [21888242871839275222246405745257275088548364400416034343698204186575808495617n, "bn128"],
  [8444461749428370424248824938781546531375899335154063827935233455917409239041n, "bls12377"],
  [52435875175126190479447740508185965837690552500527637822603658699938581184513n, "bls12381"],
  [18446744069414584321n, "goldilocks"],
  [21888242871839275222246405745257275088696311157297823662689037894645226208583n, "grumpkin"],
  [28948022309329048855892746252171976963363056481941560715954676764349967630337n, "pallas"],
  [115792089210356248762697446949407573530086143415290314195533631308867097853951n, "secq256r1"],
  [28948022309329048855892746252171976963363056481941647379679742748393362948097n, "vesta"]
]);
function isProbablePrime(n2) {
  if (n2 < 2n) return false;
  const small = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n, 53n];
  for (const q of small) {
    if (n2 === q) return true;
    if (n2 % q === 0n) return false;
  }
  let d = n2 - 1n, r = 0;
  while ((d & 1n) === 0n) {
    d >>= 1n;
    r++;
  }
  const pow = (b, e) => {
    let out = 1n, x = b % n2;
    for (; e > 0n; e >>= 1n) {
      if (e & 1n) out = out * x % n2;
      x = x * x % n2;
    }
    return out;
  };
  outer: for (const a of small) {
    let x = pow(a, d);
    if (x === 1n || x === n2 - 1n) continue;
    for (let i = 1; i < r; i++) {
      x = x * x % n2;
      if (x === n2 - 1n) continue outer;
    }
    return false;
  }
  return true;
}
function parseR1CS(bytes, limits = {}) {
  const lim = { ...DEFAULT_LIMITS, ...limits };
  if (bytes.byteLength > lim.maxBytes) throw new Error("R1CS exceeds the configured size limit");
  const view2 = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const total = bytes.byteLength;
  const need = (pos2, n2) => {
    if (!Number.isSafeInteger(n2) || n2 < 0 || pos2 + n2 > total) throw new Error("Truncated R1CS");
  };
  need(0, 12);
  if (bytes[0] !== 114 || bytes[1] !== 49 || bytes[2] !== 99 || bytes[3] !== 115)
    throw new Error("Invalid R1CS magic");
  if (view2.getUint32(4, true) !== 1) throw new Error("Unsupported R1CS version");
  const nSections = view2.getUint32(8, true);
  if (nSections < 2 || nSections > 64) throw new Error("Invalid R1CS section count");
  const sections = /* @__PURE__ */ new Map();
  let pos = 12;
  for (let i = 0; i < nSections; i++) {
    need(pos, 12);
    const kind = view2.getUint32(pos, true);
    const sizeBig = view2.getBigUint64(pos + 4, true);
    pos += 12;
    if (sizeBig > BigInt(total - pos)) throw new Error("Invalid R1CS section length");
    const size = Number(sizeBig);
    if (sections.has(kind)) throw new Error("Duplicate R1CS section");
    sections.set(kind, { start: pos, size });
    pos += size;
  }
  if (pos !== total) throw new Error("Trailing bytes after R1CS sections");
  if (sections.has(4) || sections.has(5))
    throw new Error("R1CS custom gates are outside the rank-1 analysis scope");
  const header = sections.get(1), cons = sections.get(2);
  if (!header || !cons) throw new Error("Missing required R1CS section");
  let h = header.start;
  const hEnd = header.start + header.size;
  const hNeed = (n2) => {
    if (h + n2 > hEnd) throw new Error("Truncated R1CS header");
  };
  hNeed(4);
  const fieldBytes = view2.getUint32(h, true);
  h += 4;
  if (fieldBytes < 1 || fieldBytes > 128 || fieldBytes % 8 !== 0) throw new Error("Unsupported R1CS field size");
  const readField = (at) => {
    let v = 0n;
    for (let off = fieldBytes - 8; off >= 0; off -= 8) v = v << 64n | view2.getBigUint64(at + off, true);
    return v;
  };
  hNeed(fieldBytes);
  const prime = readField(h);
  h += fieldBytes;
  if (!CIRCOM_PRIMES.has(prime) && !(lim.allowUnlistedPrime && prime >= 3n && isProbablePrime(prime)))
    throw new Error("Unsupported R1CS modulus: not one of the prime fields circom targets");
  hNeed(16 + 8 + 4);
  const nWires = view2.getUint32(h, true);
  h += 4;
  const nPubOut = view2.getUint32(h, true);
  h += 4;
  const nPubIn = view2.getUint32(h, true);
  h += 4;
  const nPrvIn = view2.getUint32(h, true);
  h += 4;
  const nLabelsBig = view2.getBigUint64(h, true);
  h += 8;
  const nConstraints = view2.getUint32(h, true);
  h += 4;
  if (h !== hEnd) throw new Error("Unexpected R1CS header length");
  if (nWires < 1 || nWires > lim.maxWires || nConstraints > lim.maxConstraints || 1 + nPubOut + nPubIn > nWires || nLabelsBig > BigInt(Number.MAX_SAFE_INTEGER))
    throw new Error("Invalid R1CS dimensions");
  const nIO = nPubOut + nPubIn + nPrvIn;
  const firstPrv = 1 + nPubOut + nPubIn;
  let nPrvInWires;
  let inputLayout;
  const labels = sections.get(3);
  if (labels) {
    if (labels.size !== nWires * 8) throw new Error("Invalid R1CS wire-to-label map size");
    const labelOf = (w) => view2.getBigUint64(labels.start + 8 * w, true);
    if (labelOf(0) !== 0n) throw new Error("Invalid R1CS wire-to-label map");
    for (let w = 1; w < firstPrv; w++) {
      const l = labelOf(w);
      if (l < 1n || l > BigInt(nIO)) throw new Error("R1CS output/public-input wire has a non-I/O label");
    }
    let count = 0;
    while (firstPrv + count < nWires && labelOf(firstPrv + count) <= BigInt(nIO)) count++;
    for (let w = firstPrv + count; w < nWires; w++)
      if (labelOf(w) <= BigInt(nIO)) throw new Error("R1CS input wires are not contiguous");
    if (count > nPrvIn) throw new Error("R1CS has more private-input wires than declared");
    nPrvInWires = count;
    inputLayout = "label-map";
  } else {
    if (firstPrv + nPrvIn > nWires) throw new Error("R1CS has no label map and its header exceeds the wire count");
    nPrvInWires = nPrvIn;
    inputLayout = "header";
  }
  const inputEnd = firstPrv + nPrvInWires;
  const intern = /* @__PURE__ */ new Map();
  let c = cons.start;
  const cEnd = cons.start + cons.size;
  let terms = 0;
  const termBytes = 4 + fieldBytes;
  const readLC = () => {
    if (c + 4 > cEnd) throw new Error("Truncated R1CS constraint");
    const n2 = view2.getUint32(c, true);
    c += 4;
    if (n2 > (cEnd - c) / termBytes) throw new Error("Invalid R1CS linear-combination length");
    terms += n2;
    if (terms > lim.maxTerms) throw new Error("R1CS exceeds the configured term limit");
    const w = new Array(n2);
    const co = new Array(n2);
    let sorted = true, prev = -1;
    for (let i = 0; i < n2; i++) {
      const wire = view2.getUint32(c, true);
      if (wire >= nWires) throw new Error("R1CS term references a wire outside the circuit");
      let v = readField(c + 4);
      if (v >= prime) v %= prime;
      const seen = intern.get(v);
      if (seen === void 0) intern.set(v, v);
      else v = seen;
      w[i] = wire;
      co[i] = v;
      if (wire <= prev) sorted = false;
      prev = wire;
      c += termBytes;
    }
    if (sorted && !co.includes(0n)) return { w, c: co };
    const acc = /* @__PURE__ */ new Map();
    for (let i = 0; i < n2; i++) acc.set(w[i], mod((acc.get(w[i]) ?? 0n) + co[i], prime));
    const keys = [...acc.keys()].filter((k) => acc.get(k) !== 0n).sort((x, y) => x - y);
    return { w: keys, c: keys.map((k) => acc.get(k)) };
  };
  const A = new Array(nConstraints), B = new Array(nConstraints), C = new Array(nConstraints);
  for (let k = 0; k < nConstraints; k++) {
    A[k] = readLC();
    B[k] = readLC();
    C[k] = readLC();
  }
  if (c !== cEnd) throw new Error("Trailing bytes in R1CS constraint section");
  return {
    prime,
    fieldBytes,
    nWires,
    nPubOut,
    nPubIn,
    nPrvIn,
    nPrvInWires,
    inputEnd,
    inputLayout,
    inputsAllWired: nPrvInWires === nPrvIn,
    nLabels: Number(nLabelsBig),
    nConstraints,
    A,
    B,
    C
  };
}
function wireRole(r, w) {
  if (w === 0) return "one";
  if (w <= r.nPubOut) return "output";
  if (w <= r.nPubOut + r.nPubIn) return "public_input";
  if (w < r.inputEnd) return "private_input";
  return "internal";
}
function parseSym(input) {
  const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
  let cap = 1024;
  let start = new Uint32Array(cap), len = new Uint32Array(cap);
  const n2 = bytes.length;
  let i = 0;
  while (i < n2) {
    while (i < n2 && bytes[i] !== 44 && bytes[i] !== 10) i++;
    if (i >= n2 || bytes[i] === 10) {
      i++;
      continue;
    }
    i++;
    let neg = false, wire = 0, digits = 0;
    if (i < n2 && bytes[i] === 45) {
      neg = true;
      i++;
    }
    while (i < n2 && bytes[i] >= 48 && bytes[i] <= 57) {
      wire = wire * 10 + (bytes[i] - 48);
      i++;
      digits++;
    }
    if (i >= n2 || bytes[i] !== 44 || !digits) {
      while (i < n2 && bytes[i] !== 10) i++;
      i++;
      continue;
    }
    i++;
    while (i < n2 && bytes[i] !== 44 && bytes[i] !== 10) i++;
    if (i >= n2 || bytes[i] === 10) {
      i++;
      continue;
    }
    i++;
    const nameStart = i;
    while (i < n2 && bytes[i] !== 10) i++;
    let nameEnd = i;
    if (nameEnd > nameStart && bytes[nameEnd - 1] === 13) nameEnd--;
    i++;
    if (neg || wire > 1073741823) continue;
    if (wire >= cap) {
      while (wire >= cap) cap *= 2;
      const s2 = new Uint32Array(cap), l2 = new Uint32Array(cap);
      s2.set(start);
      l2.set(len);
      start = s2;
      len = l2;
    }
    if (len[wire] === 0 && nameEnd > nameStart) {
      start[wire] = nameStart;
      len[wire] = nameEnd - nameStart;
    }
  }
  const decoder = new TextDecoder();
  const names = {
    get(wire) {
      if (!Number.isInteger(wire) || wire < 0 || wire >= cap || len[wire] === 0) return void 0;
      return decoder.decode(bytes.subarray(start[wire], start[wire] + len[wire]));
    }
  };
  return { names };
}
function withAssumptions(r, a) {
  const binary = [...new Set(a?.binary ?? [])].sort((x, y) => x - y);
  if (!binary.length) return r;
  const A = r.A.slice(), B = r.B.slice(), C = r.C.slice();
  for (const w of binary) {
    if (!Number.isInteger(w) || w <= r.nPubOut || w >= r.inputEnd)
      throw new Error(`assumption on wire ${w}: only input wires can be assumed binary`);
    A.push({ w: [w], c: [1n] });
    B.push({ w: [0, w], c: [r.prime - 1n, 1n] });
    C.push({ w: [], c: [] });
  }
  return { ...r, A, B, C, nConstraints: r.nConstraints + binary.length };
}

// ../carrycert-core/src/determinism/prove.ts
var NONE = { kind: "none" };
var DEAD = { kind: "dead" };
var QUAD = { kind: "quad" };
var COND_A = { kind: "cond", side: "A" };
var COND_B = { kind: "cond", side: "B" };
var Ctx = class {
  constructor(eng, parent, zero, nz, depth) {
    this.eng = eng;
    this.parent = parent;
    this.zero = zero;
    this.nz = nz;
    this.depth = depth;
  }
  det = /* @__PURE__ */ new Set();
  val = /* @__PURE__ */ new Map();
  steps = [];
  dead = -1;
  visits = 0;
  touched = /* @__PURE__ */ new Set();
  /** Wires this branch is trying to determine, and how many of them are still open. */
  targets = null;
  remaining = 0;
  /** True when the branch stopped because it ran out of budget rather than out of work. */
  exhausted = false;
  isDet(w) {
    let c = this;
    while (c.parent) {
      if (c.det.has(w)) return true;
      c = c.parent;
    }
    return this.eng.det[w] === 1;
  }
  getVal(w) {
    let c = this;
    while (c.parent) {
      const v = c.val.get(w);
      if (v !== void 0) return v;
      c = c.parent;
    }
    return this.eng.hasVal[w] ? this.eng.val.get(w) : void 0;
  }
};
var Engine = class {
  constructor(r, options = {}) {
    this.r = r;
    this.p = r.prime;
    this.opts = {
      branchBudget: options.branchBudget ?? 4096,
      maxSplitDepth: options.maxSplitDepth ?? 2,
      timeBudgetMs: options.timeBudgetMs ?? 6e5,
      gaussMaxWires: options.gaussMaxWires ?? 600,
      maxOps: options.maxOps ?? Number.MAX_SAFE_INTEGER
    };
    const n2 = r.nWires, m = r.nConstraints;
    this.det = new Uint8Array(n2);
    this.hasVal = new Uint8Array(n2);
    this.top = new Ctx(this, null, null, null, 0);
    this.unk = new Int32Array(m);
    this.nonDom = new Int32Array(m);
    this.dom2k = new Int32Array(n2).fill(-1);
    this.inQueue = new Uint8Array(m);
    this.queue = new Int32Array(Math.max(1, m));
    const counts = new Int32Array(n2 + 1);
    this.cw = new Array(m);
    const mark = new Int32Array(n2).fill(-1);
    for (let k = 0; k < m; k++) {
      const list = [];
      for (const lc of [r.A[k], r.B[k], r.C[k]])
        for (const w of lc.w) if (w !== 0 && mark[w] !== k) {
          mark[w] = k;
          list.push(w);
        }
      this.cw[k] = Int32Array.from(list);
      for (const w of list) counts[w + 1]++;
    }
    for (let i = 0; i < n2; i++) counts[i + 1] += counts[i];
    this.occStart = counts;
    this.occ = new Int32Array(counts[n2]);
    const fill = counts.slice(0, n2);
    for (let k = 0; k < m; k++) for (const w of this.cw[k]) this.occ[fill[w]++] = k;
    this.det[0] = 1;
    this.hasVal[0] = 1;
    this.val.set(0, 1n);
    for (let w = 1 + r.nPubOut; w < r.inputEnd; w++) this.det[w] = 1;
    this.findTwoValued();
    for (let k = 0; k < m; k++) {
      let u = 0, nd = 0;
      for (const w of this.cw[k]) if (!this.det[w]) {
        u++;
        if (this.dom2k[w] < 0) nd++;
      }
      this.unk[k] = u;
      this.nonDom[k] = nd;
    }
  }
  p;
  det;
  hasVal;
  val = /* @__PURE__ */ new Map();
  top;
  /** distinct non-constant wires per constraint */
  cw = [];
  /** occurrence lists (CSR) */
  occStart;
  occ;
  unk;
  nonDom;
  dom2k;
  dom2 = /* @__PURE__ */ new Map();
  queue;
  qHead = 0;
  qTail = 0;
  qLen = 0;
  inQueue;
  rules = { lin: 0, fix: 0, bits: 0, gauss: 0, onehot: 0, split: 0 };
  splitAttempts = 0;
  ops = 0;
  deadline = Infinity;
  timedOut = false;
  opts;
  // ---------------------------------------------------------------- facts
  /** Single-wire constraints: q2 x^2 + q1 x + q0 = 0. */
  singleWirePoly(k) {
    const ws = this.cw[k];
    if (ws.length !== 1) return null;
    const x = ws[0], p = this.p;
    const co = (lc) => {
      let c12 = 0n, c02 = 0n;
      for (let i = 0; i < lc.w.length; i++) {
        if (lc.w[i] === 0) c02 = lc.c[i];
        else c12 = lc.c[i];
      }
      return [c12, c02];
    };
    const [a1, a0] = co(this.r.A[k]), [b1, b0] = co(this.r.B[k]), [c1, c0] = co(this.r.C[k]);
    return { x, q2: mod(a1 * b1, p), q1: mod(a1 * b0 + a0 * b1 - c1, p), q0: mod(a0 * b0 - c0, p) };
  }
  /** Roots of a single-wire constraint: [] (none), [r] or [r1, r2]; null when every value is a root. */
  rootsOf(k) {
    const poly = this.singleWirePoly(k);
    if (!poly) return null;
    const { x, q2, q1, q0 } = poly, p = this.p;
    if (q2 === 0n) {
      if (q1 === 0n) return q0 === 0n ? null : { x, roots: [] };
      return { x, roots: [mod(-q0 * modInv(q1, p), p)] };
    }
    if (q0 === 0n) {
      if (q1 === 0n) return { x, roots: [0n] };
      return { x, roots: [0n, mod(-q1 * modInv(q2, p), p)] };
    }
    const inv2a = modInv(2n * q2, p);
    const disc = mod(q1 * q1 - 4n * q2 * q0, p);
    if (disc === 0n) return { x, roots: [mod(-q1 * inv2a, p)] };
    const s = modSqrt(disc, p);
    if (s === null) return { x, roots: [] };
    const r1 = mod((-q1 + s) * inv2a, p), r2 = mod((-q1 - s) * inv2a, p);
    return { x, roots: r1 < r2 ? [r1, r2] : [r2, r1] };
  }
  findTwoValued() {
    for (let k = 0; k < this.r.nConstraints; k++) {
      if (this.cw[k].length !== 1) continue;
      const got = this.rootsOf(k);
      if (!got || got.roots.length !== 2) continue;
      if (this.dom2k[got.x] < 0) {
        this.dom2k[got.x] = k;
        this.dom2.set(got.x, [got.roots[0], got.roots[1]]);
      }
    }
  }
  // ---------------------------------------------------------------- classification
  part(lc, ctx) {
    const ui = [];
    let known = 0n, nsym = 0;
    const w = lc.w, c = lc.c;
    if (!ctx.parent) {
      const det = this.det, hasVal = this.hasVal;
      for (let i = 0; i < w.length; i++) {
        const wi = w[i];
        if (!det[wi]) ui.push(i);
        else if (hasVal[wi]) known += c[i] * this.val.get(wi);
        else nsym++;
      }
    } else {
      for (let i = 0; i < w.length; i++) {
        const wi = w[i];
        if (!ctx.isDet(wi)) {
          ui.push(i);
          continue;
        }
        const v = ctx.getVal(wi);
        if (v === void 0) nsym++;
        else known += c[i] * v;
      }
    }
    return { ui, known: known % this.p, nsym };
  }
  /** Normal form of a determined linear form under the context's known values. */
  normForm(lc, ctx) {
    const p = this.p;
    const wires = [], coefs = [];
    let c0 = 0n;
    for (let i = 0; i < lc.w.length; i++) {
      const v = ctx.getVal(lc.w[i]);
      if (v !== void 0) c0 += lc.c[i] * v;
      else {
        wires.push(lc.w[i]);
        coefs.push(lc.c[i]);
      }
    }
    c0 = mod(c0, p);
    if (!wires.length) return null;
    const inv2 = modInv(coefs[0], p);
    return { wires, coefs: coefs.map((c) => c * inv2 % p), c0: c0 * inv2 % p };
  }
  sameForm(a, b, ctx) {
    const x = this.normForm(a, ctx), y = this.normForm(b, ctx);
    if (!x || !y || x.wires.length !== y.wires.length || x.c0 !== y.c0) return false;
    for (let i = 0; i < x.wires.length; i++)
      if (x.wires[i] !== y.wires[i] || x.coefs[i] !== y.coefs[i]) return false;
    return true;
  }
  /** 0 = known zero, 1 = known nonzero, -1 = no fact, for a determined non-constant form. */
  formFact(lc, ctx) {
    let c = ctx;
    while (c && c.parent) {
      if (c.zero && this.sameForm(lc, c.zero, ctx)) return 0;
      if (c.nz && this.sameForm(lc, c.nz, ctx)) return 1;
      c = c.parent;
    }
    return -1;
  }
  rowFrom(lcs, rhs) {
    const p = this.p;
    if (lcs.length === 1) {
      const { lc, ui, scale } = lcs[0];
      const wires2 = ui.map((i) => lc.w[i]);
      const coefs2 = ui.map((i) => mod(lc.c[i] * scale, p));
      return { kind: "row", wires: wires2, coefs: coefs2, rhs };
    }
    const acc = /* @__PURE__ */ new Map();
    for (const { lc, ui, scale } of lcs)
      for (const i of ui) acc.set(lc.w[i], mod((acc.get(lc.w[i]) ?? 0n) + lc.c[i] * scale, p));
    const wires = [], coefs = [];
    for (const [w, c] of acc) if (c !== 0n) {
      wires.push(w);
      coefs.push(c);
    }
    return { kind: "row", wires, coefs, rhs };
  }
  /**
   * Reduce constraint k (A*B = C) under a context to what it says about the
   * undetermined wires. `rhs` is the right-hand side of the row equation
   * sum(coefs_i * x_i) = rhs when every other quantity has a known value.
   */
  classify(k, ctx) {
    this.ops++;
    const p = this.p, r = this.r;
    const A = r.A[k], B = r.B[k], C = r.C[k];
    const a = this.part(A, ctx), b = this.part(B, ctx), c = this.part(C, ctx);
    if (!a.ui.length && !b.ui.length) {
      const allKnown = !a.nsym && !b.nsym && !c.nsym;
      const rhs2 = allKnown ? mod(a.known * b.known - c.known, p) : null;
      if (!c.ui.length) return rhs2 !== null && rhs2 !== 0n ? DEAD : NONE;
      return this.rowFrom([{ lc: C, ui: c.ui, scale: 1n }], rhs2);
    }
    if (a.ui.length && b.ui.length) return QUAD;
    const mIsA = !a.ui.length;
    const M = mIsA ? A : B, N = mIsA ? B : A;
    const m = mIsA ? a : b, nn = mIsA ? b : a;
    let mval = m.nsym ? null : m.known;
    let nzUnknown = false;
    if (mval === null) {
      const fact = this.formFact(M, ctx);
      if (fact === 0) mval = 0n;
      else if (fact === 1) nzUnknown = true;
      else return mIsA ? COND_A : COND_B;
    }
    if (nzUnknown) {
      if (c.ui.length) return NONE;
      return this.rowFrom([{ lc: N, ui: nn.ui, scale: 1n }], null);
    }
    if (mval === 0n) {
      const rhs2 = c.nsym ? null : mod(-c.known, p);
      if (!c.ui.length) return rhs2 !== null && rhs2 !== 0n ? DEAD : NONE;
      return this.rowFrom([{ lc: C, ui: c.ui, scale: 1n }], rhs2);
    }
    const rhs = nn.nsym || c.nsym ? null : mod(c.known - mval * nn.known, p);
    const parts = [{ lc: N, ui: nn.ui, scale: mval }];
    if (c.ui.length) parts.push({ lc: C, ui: c.ui, scale: p - 1n });
    const row = this.rowFrom(parts, rhs);
    if (!row.wires.length) return rhs !== null && rhs !== 0n ? DEAD : NONE;
    return row;
  }
  // ---------------------------------------------------------------- state updates
  enqueue(k) {
    if (this.inQueue[k]) return;
    this.inQueue[k] = 1;
    this.queue[this.qTail] = k;
    this.qTail = (this.qTail + 1) % this.queue.length;
    this.qLen++;
  }
  determine(x, ctx, local) {
    if (!ctx.parent) {
      if (this.det[x]) return;
      this.det[x] = 1;
      const isDom = this.dom2k[x] >= 0;
      for (let i = this.occStart[x]; i < this.occStart[x + 1]; i++) {
        const k = this.occ[i];
        const u = --this.unk[k];
        const nd = isDom ? this.nonDom[k] : --this.nonDom[k];
        if (u <= 1 || nd === 0) this.enqueue(k);
      }
    } else {
      if (ctx.isDet(x)) return;
      ctx.det.add(x);
      if (ctx.targets && ctx.targets.has(x)) ctx.remaining--;
      for (let i = this.occStart[x]; i < this.occStart[x + 1]; i++) local.push(this.occ[i]);
    }
  }
  setVal(x, v, ctx, local) {
    if (!ctx.parent) {
      if (this.hasVal[x]) return;
      this.hasVal[x] = 1;
      this.val.set(x, v);
      for (let i = this.occStart[x]; i < this.occStart[x + 1]; i++) this.enqueue(this.occ[i]);
    } else {
      if (ctx.getVal(x) !== void 0) return;
      ctx.val.set(x, v);
      for (let i = this.occStart[x]; i < this.occStart[x + 1]; i++) local.push(this.occ[i]);
    }
  }
  /** Apply the direct rules to one constraint. Returns true when it determined something. */
  apply(k, ctx, local) {
    const cls = this.classify(k, ctx);
    if (cls.kind === "dead") {
      if (ctx.dead < 0) ctx.dead = k;
      return false;
    }
    if (cls.kind !== "row") return false;
    const { wires, coefs, rhs } = cls;
    const p = this.p;
    if (wires.length === 0) {
      if (rhs !== null && rhs !== 0n && ctx.dead < 0) ctx.dead = k;
      return false;
    }
    if (wires.length === 1) {
      const x = wires[0];
      ctx.steps.push({ t: "lin", k, x });
      this.rules.lin++;
      this.determine(x, ctx, local);
      if (rhs !== null) this.setVal(x, mod(rhs * modInv(coefs[0], p), p), ctx, local);
      return true;
    }
    if (wires.length > 1024) return false;
    const weights = new Array(wires.length);
    const d = new Array(wires.length);
    for (let i = 0; i < wires.length; i++) {
      const dk = this.dom2k[wires[i]];
      if (dk < 0) return false;
      const [r1, r2] = this.dom2.get(wires[i]);
      weights[i] = mod(coefs[i] * (r2 - r1), p);
      d[i] = dk;
    }
    const scale = findSuperIncreasingScale(weights, p);
    if (scale === null) return false;
    ctx.steps.push({ t: "bits", k, xs: wires.slice(), d, s: scale.toString() });
    this.rules.bits++;
    for (const x of wires) this.determine(x, ctx, local);
    return true;
  }
  drain() {
    while (this.qLen) {
      const k = this.queue[this.qHead];
      this.qHead = (this.qHead + 1) % this.queue.length;
      this.qLen--;
      this.inQueue[k] = 0;
      if (this.unk[k] === 0 && !this.cwHasNewValue(k)) continue;
      this.apply(k, this.top, null);
    }
  }
  /** At top level a constraint with no undetermined wire can teach nothing. */
  cwHasNewValue(_k) {
    return false;
  }
  // ---------------------------------------------------------------- single-root facts
  applyFixes() {
    for (let k = 0; k < this.r.nConstraints; k++) {
      if (this.cw[k].length !== 1) continue;
      const x = this.cw[k][0];
      if (this.det[x]) continue;
      const got = this.rootsOf(k);
      if (!got || got.roots.length !== 1) continue;
      this.top.steps.push({ t: "fix", k, x });
      this.rules.fix++;
      this.determine(x, this.top, null);
      this.setVal(x, got.roots[0], this.top, null);
    }
  }
  // ---------------------------------------------------------------- linear systems
  gaussPass() {
    const p = this.p, m = this.r.nConstraints;
    const rows = [];
    for (let k = 0; k < m; k++) {
      if (this.unk[k] < 2) continue;
      const cls = this.classify(k, this.top);
      if (cls.kind === "row" && cls.wires.length >= 2 && cls.wires.length <= 64)
        rows.push({ k, wires: cls.wires, coefs: cls.coefs });
    }
    if (!rows.length) return false;
    const parent = /* @__PURE__ */ new Map();
    const find = (x) => {
      let root = x;
      while (parent.get(root) !== root) root = parent.get(root);
      while (parent.get(x) !== root) {
        const nx = parent.get(x);
        parent.set(x, root);
        x = nx;
      }
      return root;
    };
    for (const row of rows) {
      for (const w of row.wires) if (!parent.has(w)) parent.set(w, w);
      const r0 = find(row.wires[0]);
      for (let i = 1; i < row.wires.length; i++) parent.set(find(row.wires[i]), r0);
    }
    const comps = /* @__PURE__ */ new Map();
    rows.forEach((row, i) => {
      const root = find(row.wires[0]);
      const list = comps.get(root);
      if (list) list.push(i);
      else comps.set(root, [i]);
    });
    let progress = false;
    for (const idxs of comps.values()) {
      if (idxs.length < 2) continue;
      const wireSet = /* @__PURE__ */ new Set();
      for (const i of idxs) for (const w of rows[i].wires) wireSet.add(w);
      if (wireSet.size > this.opts.gaussMaxWires || idxs.length > 4 * this.opts.gaussMaxWires) continue;
      const basis = /* @__PURE__ */ new Map();
      const addScaled = (dst, src, f) => {
        for (const [key, v] of src) {
          const nv = mod((dst.get(key) ?? 0n) + v * f, p);
          if (nv === 0n) dst.delete(key);
          else dst.set(key, nv);
        }
      };
      let work = 0;
      const cap = 4e6;
      let aborted = false;
      for (const i of idxs) {
        const vec = /* @__PURE__ */ new Map(), comb = /* @__PURE__ */ new Map([[i, 1n]]);
        rows[i].wires.forEach((w, j) => vec.set(w, rows[i].coefs[j]));
        for (const w of [...vec.keys()]) {
          const b = basis.get(w);
          if (!b) continue;
          const f = vec.get(w);
          if (f === void 0) continue;
          const neg = p - f;
          addScaled(vec, b.vec, neg);
          addScaled(comb, b.comb, neg);
          work += b.vec.size + b.comb.size;
        }
        if (!vec.size) continue;
        let pivot = -1;
        for (const w of vec.keys()) if (pivot < 0 || w < pivot) pivot = w;
        const inv2 = modInv(vec.get(pivot), p);
        for (const [key, v] of vec) vec.set(key, v * inv2 % p);
        for (const [key, v] of comb) comb.set(key, v * inv2 % p);
        for (const b of basis.values()) {
          const f = b.vec.get(pivot);
          if (f === void 0) continue;
          const neg = p - f;
          addScaled(b.vec, vec, neg);
          addScaled(b.comb, comb, neg);
          work += vec.size + comb.size;
        }
        basis.set(pivot, { vec, comb });
        if (work > cap) {
          aborted = true;
          break;
        }
      }
      if (aborted) continue;
      for (const [pivot, b] of basis) {
        if (b.vec.size !== 1 || this.det[pivot]) continue;
        const rk = [], mult = [];
        for (const [i, v] of b.comb) {
          rk.push(rows[i].k);
          mult.push(v.toString());
        }
        this.top.steps.push({ t: "gauss", x: pivot, rows: rk, mult });
        this.rules.gauss++;
        this.determine(pivot, this.top, null);
        progress = true;
      }
    }
    return progress;
  }
  // ---------------------------------------------------------------- one-hot families
  /**
   * Selector families. Members are constraints with a determined, non-constant
   * multiplicand whose other multiplicand has exactly one undetermined wire and
   * whose right-hand side has none. Members whose multiplicands differ only by
   * a constant belong to one family.
   */
  oneHotPass() {
    const m = this.r.nConstraints;
    const families = /* @__PURE__ */ new Map();
    for (let k = 0; k < m; k++) {
      if (this.unk[k] !== 1) continue;
      const cls = this.classify(k, this.top);
      if (cls.kind !== "cond") continue;
      const M = cls.side === "A" ? this.r.A[k] : this.r.B[k];
      const N = cls.side === "A" ? this.r.B[k] : this.r.A[k];
      const n2 = this.part(N, this.top), c = this.part(this.r.C[k], this.top);
      if (n2.ui.length !== 1 || c.ui.length !== 0) continue;
      const nf = this.normForm(M, this.top);
      if (!nf) continue;
      const key = nf.wires.join(",") + "|" + nf.coefs.join(",");
      const member = { k, side: cls.side, s: N.w[n2.ui[0]], c0: nf.c0 };
      const list = families.get(key);
      if (list) list.push(member);
      else families.set(key, [member]);
    }
    let progress = false;
    for (const members of families.values()) {
      if (members.length < 2) continue;
      const byWire = /* @__PURE__ */ new Map();
      for (const mem of members) if (!this.det[mem.s] && !byWire.has(mem.s)) byWire.set(mem.s, mem);
      if (byWire.size < 2) continue;
      const tried = /* @__PURE__ */ new Set();
      for (const start of byWire.keys()) {
        if (this.det[start]) continue;
        for (let i = this.occStart[start]; i < this.occStart[start + 1]; i++) {
          const k = this.occ[i];
          if (tried.has(k)) continue;
          tried.add(k);
          const cls = this.classify(k, this.top);
          if (cls.kind !== "row" || cls.wires.length < 2) continue;
          if (!cls.wires.every((w) => byWire.has(w))) continue;
          const mem = cls.wires.map((w) => byWire.get(w));
          if (new Set(mem.map((x) => x.c0)).size !== mem.length) continue;
          this.top.steps.push({ t: "onehot", k, m: mem.map((x) => [x.k, x.side]) });
          this.rules.onehot++;
          for (const w of cls.wires) this.determine(w, this.top, null);
          progress = true;
          break;
        }
      }
    }
    return progress;
  }
  // ---------------------------------------------------------------- case analysis
  /**
   * Run the direct rules inside a branch. `seeds` are processed first, together
   * with everything they unlock; `lazy` (typically every constraint mentioning
   * a wire whose value the branch learned) is consumed only when that work runs
   * dry, so a widely used wire cannot starve the relevant follow-ups.
   *
   * The branch stops as soon as every target wire is determined: whatever lies
   * downstream is cheaper to derive once at the parent level than twice here.
   */
  closure(ctx, seeds, lazy, budget) {
    const local = seeds.slice();
    let i = 0, j = 0;
    const done = () => ctx.dead >= 0 || ctx.targets !== null && ctx.remaining <= 0;
    const pump = (limit) => {
      for (; ; ) {
        if (done()) return;
        let k;
        if (i < local.length) k = local[i++];
        else if (j < lazy.length) k = lazy[j++];
        else return;
        if (++ctx.visits > limit) {
          ctx.exhausted = true;
          return;
        }
        ctx.touched.add(k);
        this.apply(k, ctx, local);
      }
    };
    pump(budget);
    if (done() || ctx.depth >= this.opts.maxSplitDepth) return;
    let attempts = 0;
    for (let round = 0; round < 3 && !done(); round++) {
      let progress = false;
      const groups = /* @__PURE__ */ new Map();
      for (const k of ctx.touched) {
        let relevant = false;
        for (const w of this.cw[k]) if (ctx.targets.has(w) && !ctx.isDet(w)) {
          relevant = true;
          break;
        }
        if (!relevant) continue;
        const cls = this.classify(k, ctx);
        if (cls.kind !== "cond") continue;
        const nf = this.normForm(cls.side === "A" ? this.r.A[k] : this.r.B[k], ctx);
        if (!nf) continue;
        const key = nf.wires.join(",") + "|" + nf.coefs.join(",") + "|" + nf.c0;
        const g = groups.get(key);
        if (g) g.push({ k, side: cls.side });
        else groups.set(key, [{ k, side: cls.side }]);
      }
      for (const group of groups.values()) {
        if (done() || attempts >= 8 || ctx.visits > budget * 3) return;
        attempts++;
        ctx.visits += 4;
        if (this.trySplit(group[0].k, group[0].side, group, ctx, local, Math.max(48, budget >> 2)) === "ok") {
          progress = true;
          pump(budget * 3);
        }
      }
      if (!progress) return;
    }
  }
  /**
   * Case-split on the determined multiplicand of constraint k. Commits to
   * `ctx` every wire that both cases determine. `local` receives follow-up
   * constraints when ctx is itself a branch. On failure `blockers` collects
   * wires whose later determination could make a retry worthwhile.
   */
  trySplit(k, side, group, ctx, local, budget, blockers) {
    this.splitAttempts++;
    const form = side === "A" ? this.r.A[k] : this.r.B[k];
    const nf = this.normForm(form, ctx);
    if (!nf) return "fail";
    const seeds = group.map((g) => g.k);
    const targets = /* @__PURE__ */ new Set();
    for (const g of group) for (const w of this.cw[g.k]) if (!ctx.isDet(w)) targets.add(w);
    if (!targets.size) return "fail";
    const note = (c) => {
      if (!blockers) return;
      for (const kk of c.touched) {
        if (blockers.size >= 24) return;
        for (const w of this.cw[kk]) if (!ctx.isDet(w)) {
          blockers.add(w);
          if (blockers.size >= 24) return;
        }
      }
    };
    const Z = new Ctx(this, ctx, form, null, ctx.depth + 1);
    Z.targets = targets;
    Z.remaining = targets.size;
    const zLazy = [];
    if (nf.wires.length === 1) {
      const x = nf.wires[0];
      Z.val.set(x, mod(-nf.c0, this.p));
      const near = new Set(targets);
      let wide = false, scanned = 0;
      for (const t of targets) {
        if (wide) break;
        for (let i = this.occStart[t]; i < this.occStart[t + 1] && !wide; i++) {
          const ws = this.cw[this.occ[i]];
          scanned += ws.length;
          if (scanned > 4e4) {
            wide = true;
            break;
          }
          for (const w of ws) if (!ctx.isDet(w)) near.add(w);
          if (near.size > 8192) wide = true;
        }
      }
      for (let i = this.occStart[x]; i < this.occStart[x + 1]; i++) {
        const kk = this.occ[i];
        let useful = wide;
        if (!useful) {
          for (const w of this.cw[kk]) if (near.has(w)) {
            useful = true;
            break;
          }
        }
        if (useful) zLazy.push(kk);
      }
    }
    this.closure(Z, seeds, zLazy, budget);
    if (Z.dead < 0 && Z.remaining === targets.size) {
      note(Z);
      return Z.exhausted ? "fail-budget" : "fail";
    }
    const N = new Ctx(this, ctx, null, form, ctx.depth + 1);
    N.targets = targets;
    N.remaining = targets.size;
    this.closure(N, seeds, [], budget);
    if (N.dead < 0 && N.remaining === targets.size) {
      note(N);
      return N.exhausted ? "fail-budget" : "fail";
    }
    if (Z.dead >= 0 && N.dead >= 0) return "fail";
    const xs = [];
    const pick = Z.dead >= 0 ? N.det : N.dead >= 0 ? Z.det : null;
    if (pick) {
      for (const x of pick) if (!ctx.isDet(x)) xs.push(x);
    } else for (const x of Z.det) if (N.det.has(x) && !ctx.isDet(x)) xs.push(x);
    if (!xs.length) {
      note(Z);
      note(N);
      return Z.exhausted || N.exhausted ? "fail-budget" : "fail";
    }
    xs.sort((x, y) => x - y);
    const branch = (c) => c.dead >= 0 ? { steps: c.steps, dead: c.dead } : { steps: c.steps };
    ctx.steps.push({ t: "split", k, side, xs, zero: branch(Z), nonzero: branch(N) });
    this.rules.split++;
    for (const x of xs) this.determine(x, ctx, local);
    return "ok";
  }
  /**
   * Groups that failed: the wires whose determination would justify another
   * attempt, and the budget at which a budget-limited failure happened (0 when
   * the attempt ran out of work, in which case a larger budget cannot help).
   */
  failed = /* @__PURE__ */ new Map();
  splitPass(budget) {
    const m = this.r.nConstraints;
    const groups = /* @__PURE__ */ new Map();
    for (let k = 0; k < m; k++) {
      if (this.unk[k] === 0) continue;
      const cls = this.classify(k, this.top);
      if (cls.kind !== "cond") continue;
      const nf = this.normForm(cls.side === "A" ? this.r.A[k] : this.r.B[k], this.top);
      if (!nf) continue;
      const key = nf.wires.join(",") + "|" + nf.coefs.join(",") + "|" + nf.c0;
      const g = groups.get(key);
      if (g) g.push({ k, side: cls.side });
      else groups.set(key, [{ k, side: cls.side }]);
    }
    let progress = false;
    for (const [key, group] of groups) {
      if (performance.now() > this.deadline || this.ops > this.opts.maxOps) {
        this.timedOut = true;
        break;
      }
      const memo = this.failed.get(key);
      if (memo && !(memo.limitedAt > 0 && budget > memo.limitedAt) && !memo.blockers.some((w) => this.det[w])) continue;
      const live = group.filter((g) => {
        if (this.unk[g.k] === 0) return false;
        const cls = this.classify(g.k, this.top);
        return cls.kind === "cond" && cls.side === g.side;
      });
      if (!live.length) continue;
      const blockers = /* @__PURE__ */ new Set();
      const outcome = this.trySplit(live[0].k, live[0].side, live, this.top, null, budget, blockers);
      if (outcome === "ok") {
        progress = true;
        this.failed.delete(key);
        this.drain();
      } else this.failed.set(key, { blockers: [...blockers], limitedAt: outcome === "fail-budget" ? budget : 0 });
    }
    return progress;
  }
  // ---------------------------------------------------------------- driver
  run() {
    const t0 = performance.now();
    this.deadline = t0 + this.opts.timeBudgetMs;
    this.applyFixes();
    for (let k = 0; k < this.r.nConstraints; k++) this.enqueue(k);
    this.drain();
    const budgets = [64, 512, this.opts.branchBudget].filter((b, i, all) => b <= this.opts.branchBudget && all.indexOf(b) === i);
    let level = 0, rounds = 0;
    for (; ; ) {
      if (performance.now() > this.deadline || this.ops > this.opts.maxOps) {
        this.timedOut = true;
        break;
      }
      if (++rounds > 400) break;
      if (this.gaussPass()) {
        this.drain();
        continue;
      }
      if (this.oneHotPass()) {
        this.drain();
        continue;
      }
      if (this.splitPass(budgets[level])) {
        this.drain();
        level = 0;
        continue;
      }
      if (level + 1 < budgets.length) {
        level++;
        continue;
      }
      break;
    }
    let determined = 0;
    for (let w = 0; w < this.r.nWires; w++) determined += this.det[w];
    const twoValued = /* @__PURE__ */ new Map();
    for (const [w, roots] of this.dom2) twoValued.set(w, { k: this.dom2k[w], r: roots });
    return {
      determined: this.det,
      steps: this.top.steps,
      stats: {
        wires: this.r.nWires,
        constraints: this.r.nConstraints,
        determined,
        undetermined: this.r.nWires - determined,
        rules: { ...this.rules },
        splitAttempts: this.splitAttempts,
        time_ms: performance.now() - t0,
        timedOut: this.timedOut
      },
      twoValued,
      open: this.openItems()
    };
  }
  /** For each undetermined wire, why no rule fixed it. Bounded for reporting. */
  openItems(limit = 5e3) {
    const out = [];
    for (let w = 1; w < this.r.nWires && out.length < limit; w++) {
      if (this.det[w]) continue;
      const item = { wire: w, conditional: [], nonlinear: [], occurrences: this.occStart[w + 1] - this.occStart[w] };
      for (let i = this.occStart[w]; i < this.occStart[w + 1] && item.conditional.length + item.nonlinear.length < 8; i++) {
        const k = this.occ[i];
        const cls = this.classify(k, this.top);
        if (cls.kind === "cond") item.conditional.push({ k, side: cls.side });
        else if (cls.kind === "quad") item.nonlinear.push(k);
      }
      out.push(item);
    }
    return out;
  }
};
function prove(r, options = {}) {
  return new Engine(r, options).run();
}

// ../carrycert-core/src/determinism/check.ts
var md = (a, p) => {
  const r = a % p;
  return r < 0n ? r + p : r;
};
function inv(a, p) {
  let lo = md(a, p), hi = p, x = 1n, y = 0n;
  if (lo === 0n) throw new Error("zero has no inverse");
  while (hi !== 0n) {
    const q = lo / hi;
    [lo, hi] = [hi, lo - q * hi];
    [x, y] = [y, x - q * y];
  }
  if (lo !== 1n) throw new Error("modulus is not prime");
  return md(x, p);
}
function pw(b, e, p) {
  let out = 1n, base = md(b, p);
  for (let n2 = e; n2 > 0n; n2 >>= 1n) {
    if (n2 & 1n) out = out * base % p;
    base = base * base % p;
  }
  return out;
}
var Replay = class {
  constructor(r) {
    this.r = r;
    this.p = r.prime;
    this.det = new Uint8Array(r.nWires);
    this.det[0] = 1;
    this.val.set(0, 1n);
    for (let w = 1 + r.nPubOut; w < r.inputEnd; w++) this.det[w] = 1;
  }
  p;
  det;
  val = /* @__PURE__ */ new Map();
  frames = [];
  count = 0;
  isDet(w) {
    for (let i = this.frames.length - 1; i >= 0; i--) if (this.frames[i].det.has(w)) return true;
    return this.det[w] === 1;
  }
  value(w) {
    for (let i = this.frames.length - 1; i >= 0; i--) {
      const v = this.frames[i].val.get(w);
      if (v !== void 0) return v;
    }
    return this.val.get(w);
  }
  mark(w) {
    if (this.frames.length) this.frames[this.frames.length - 1].det.add(w);
    else this.det[w] = 1;
  }
  learn(w, v) {
    if (this.value(w) !== void 0) return;
    if (this.frames.length) this.frames[this.frames.length - 1].val.set(w, v);
    else this.val.set(w, v);
  }
  constraintOk(k) {
    return Number.isInteger(k) && k >= 0 && k < this.r.nConstraints;
  }
  wireOk(w) {
    return Number.isInteger(w) && w > 0 && w < this.r.nWires;
  }
  /** Split a linear combination into its undetermined part, known constant part and "has unvalued determined wires". */
  view(lc) {
    const open = /* @__PURE__ */ new Map();
    let known = 0n, symbolic = false;
    for (let i = 0; i < lc.w.length; i++) {
      const w = lc.w[i];
      if (!this.isDet(w)) {
        open.set(w, lc.c[i]);
        continue;
      }
      const v = this.value(w);
      if (v === void 0) symbolic = true;
      else known = md(known + lc.c[i] * v, this.p);
    }
    return { open, known, symbolic };
  }
  /** A determined linear form scaled so that its first unvalued wire has coefficient one. */
  normal(lc) {
    const terms = [];
    let c0 = 0n;
    for (let i = 0; i < lc.w.length; i++) {
      const v = this.value(lc.w[i]);
      if (v === void 0) terms.push([lc.w[i], lc.c[i]]);
      else c0 = md(c0 + lc.c[i] * v, this.p);
    }
    if (!terms.length) return null;
    const s = inv(terms[0][1], this.p);
    return terms.map(([w, c]) => w + ":" + c * s % this.p).join(",") + "|" + c0 * s % this.p;
  }
  /** "zero" / "nonzero" when a case fact on the frame stack applies to this form. */
  fact(lc) {
    const key = this.normal(lc);
    if (key === null) return null;
    for (let i = this.frames.length - 1; i >= 0; i--) {
      const f = this.frames[i];
      if (f.zero && this.normal(f.zero) === key) return "zero";
      if (f.nz && this.normal(f.nz) === key) return "nonzero";
    }
    return null;
  }
  reduce(k) {
    const p = this.p;
    const A = this.view(this.r.A[k]), B = this.view(this.r.B[k]), C = this.view(this.r.C[k]);
    const finish = (row2, rhs) => {
      for (const [w, c] of [...row2]) if (c === 0n) row2.delete(w);
      if (!row2.size) return rhs !== null && rhs !== 0n ? { kind: "dead" } : { kind: "none" };
      return { kind: "row", row: row2, rhs };
    };
    if (!A.open.size && !B.open.size) {
      const rhs = A.symbolic || B.symbolic || C.symbolic ? null : md(A.known * B.known - C.known, p);
      return finish(new Map(C.open), rhs);
    }
    if (A.open.size && B.open.size) return { kind: "quad" };
    const aDetermined = !A.open.size;
    const M = aDetermined ? A : B, N = aDetermined ? B : A;
    const Mlc = aDetermined ? this.r.A[k] : this.r.B[k];
    let m = M.symbolic ? null : M.known;
    if (m === null) {
      const f = this.fact(Mlc);
      if (f === "zero") m = 0n;
      else if (f === "nonzero") {
        if (C.open.size) return { kind: "none" };
        return finish(new Map(N.open), null);
      } else return { kind: "cond" };
    }
    if (m === 0n) return finish(new Map(C.open), C.symbolic ? null : md(-C.known, p));
    const row = /* @__PURE__ */ new Map();
    for (const [w, c] of N.open) row.set(w, md(c * m, p));
    for (const [w, c] of C.open) row.set(w, md((row.get(w) ?? 0n) - c, p));
    return finish(row, N.symbolic || C.symbolic ? null : md(C.known - m * N.known, p));
  }
  /** Roots of a constraint that mentions exactly one non-constant wire x. */
  roots(k, x) {
    const p = this.p;
    const co = (lc) => {
      let c1 = 0n, c0 = 0n;
      for (let i = 0; i < lc.w.length; i++) {
        if (lc.w[i] === 0) c0 = lc.c[i];
        else if (lc.w[i] === x) c1 = lc.c[i];
        else return null;
      }
      return [c1, c0];
    };
    const a = co(this.r.A[k]), b = co(this.r.B[k]), c = co(this.r.C[k]);
    if (!a || !b || !c) return null;
    const q2 = md(a[0] * b[0], p), q1 = md(a[0] * b[1] + a[1] * b[0] - c[0], p), q0 = md(a[1] * b[1] - c[1], p);
    const isRoot = (v) => md(q2 * v * v + q1 * v + q0, p) === 0n;
    if (q2 === 0n) {
      if (q1 === 0n) return null;
      return [md(-q0 * inv(q1, p), p)];
    }
    if (q0 === 0n) {
      if (q1 === 0n) return [0n];
      const other = md(-q1 * inv(q2, p), p);
      return isRoot(other) && other !== 0n ? [0n, other] : null;
    }
    const half = inv(2n * q2, p);
    const disc = md(q1 * q1 - 4n * q2 * q0, p);
    if (disc === 0n) return [md(-q1 * half, p)];
    if (pw(disc, (p - 1n) / 2n, p) !== 1n) return [];
    let s;
    if ((p & 3n) === 3n) s = pw(disc, (p + 1n) / 4n, p);
    else {
      let q = p - 1n, e = 0n;
      while ((q & 1n) === 0n) {
        q >>= 1n;
        e++;
      }
      let z = 2n;
      while (pw(z, (p - 1n) / 2n, p) !== p - 1n) {
        if (++z > 4096n) return null;
      }
      let mm = e, cc = pw(z, q, p), t = pw(disc, q, p);
      s = pw(disc, (q + 1n) / 2n, p);
      while (t !== 1n) {
        let i = 0n, t2 = t;
        while (t2 !== 1n) {
          t2 = t2 * t2 % p;
          i++;
          if (i >= mm) return null;
        }
        const bb = pw(cc, 1n << mm - i - 1n, p);
        mm = i;
        cc = bb * bb % p;
        t = t * cc % p;
        s = s * bb % p;
      }
    }
    const r1 = md((-q1 + s) * half, p), r2 = md((-q1 - s) * half, p);
    if (!isRoot(r1) || !isRoot(r2) || r1 === r2) return null;
    return [r1, r2];
  }
  superIncreasing(weights, scale) {
    const p = this.p;
    if (md(scale, p) === 0n) return false;
    const mags = weights.map((g) => {
      const v = md(g * scale, p);
      return v > p / 2n ? p - v : v;
    }).sort((x, y) => x < y ? -1 : x > y ? 1 : 0);
    let sum = 0n;
    for (const v of mags) {
      if (v <= sum) return false;
      sum += v;
    }
    return sum < p;
  }
  step(s) {
    this.count++;
    const p = this.p;
    if (!s || typeof s !== "object") return "malformed step";
    if (s.t === "lin") {
      if (!this.constraintOk(s.k) || !this.wireOk(s.x)) return "lin: bad index";
      const red = this.reduce(s.k);
      if (red.kind !== "row" || red.row.size !== 1 || !red.row.has(s.x))
        return `lin: constraint ${s.k} does not isolate wire ${s.x}`;
      this.mark(s.x);
      if (red.rhs !== null) this.learn(s.x, md(red.rhs * inv(red.row.get(s.x), p), p));
      return null;
    }
    if (s.t === "fix") {
      if (!this.constraintOk(s.k) || !this.wireOk(s.x)) return "fix: bad index";
      const roots = this.roots(s.k, s.x);
      if (!roots || roots.length !== 1) return `fix: constraint ${s.k} does not pin wire ${s.x} to one value`;
      this.mark(s.x);
      this.learn(s.x, roots[0]);
      return null;
    }
    if (s.t === "bits") {
      if (!this.constraintOk(s.k) || !Array.isArray(s.xs) || !Array.isArray(s.d) || s.xs.length !== s.d.length || s.xs.length < 2)
        return "bits: malformed";
      const red = this.reduce(s.k);
      if (red.kind !== "row" || red.row.size !== s.xs.length) return `bits: constraint ${s.k} is not a matching linear row`;
      if (typeof s.s !== "string" || !/^(0|[1-9][0-9]*)$/.test(s.s)) return "bits: scale must be a decimal string";
      const scale = BigInt(s.s);
      const weights = [];
      const seen = /* @__PURE__ */ new Set();
      for (let i = 0; i < s.xs.length; i++) {
        const x = s.xs[i], dk = s.d[i];
        if (!this.wireOk(x) || !this.constraintOk(dk) || seen.has(x)) return "bits: bad index";
        seen.add(x);
        const coef = red.row.get(x);
        if (coef === void 0) return `bits: wire ${x} is not open in constraint ${s.k}`;
        const roots = this.roots(dk, x);
        if (!roots || roots.length !== 2) return `bits: constraint ${dk} does not make wire ${x} two-valued`;
        weights.push(md(coef * (roots[1] - roots[0]), p));
      }
      if (!this.superIncreasing(weights, scale)) return `bits: weights of constraint ${s.k} are not injective under the given scale`;
      for (const x of s.xs) this.mark(x);
      return null;
    }
    if (s.t === "gauss") {
      if (!this.wireOk(s.x) || !Array.isArray(s.rows) || !Array.isArray(s.mult) || s.rows.length !== s.mult.length || !s.rows.length)
        return "gauss: malformed";
      const acc = /* @__PURE__ */ new Map();
      for (let i = 0; i < s.rows.length; i++) {
        if (!this.constraintOk(s.rows[i])) return "gauss: bad constraint index";
        const red = this.reduce(s.rows[i]);
        if (red.kind !== "row") return `gauss: constraint ${s.rows[i]} is not a linear row`;
        if (typeof s.mult[i] !== "string" || !/^(0|[1-9][0-9]*)$/.test(s.mult[i])) return "gauss: multiplier must be a decimal string";
        const f = md(BigInt(s.mult[i]), p);
        for (const [w, c] of red.row) acc.set(w, md((acc.get(w) ?? 0n) + c * f, p));
      }
      for (const [w, c] of acc) if (c !== 0n && w !== s.x) return `gauss: combination leaves wire ${w}`;
      if (!acc.get(s.x)) return `gauss: combination does not isolate wire ${s.x}`;
      this.mark(s.x);
      return null;
    }
    if (s.t === "onehot") {
      if (!this.constraintOk(s.k) || !Array.isArray(s.m) || s.m.length < 2) return "onehot: malformed";
      const row = this.reduce(s.k);
      if (row.kind !== "row" || row.row.size !== s.m.length) return `onehot: constraint ${s.k} is not a linear row over the family`;
      let base = null;
      const constants = /* @__PURE__ */ new Set();
      const wires = /* @__PURE__ */ new Set();
      for (const entry of s.m) {
        if (!Array.isArray(entry) || entry.length !== 2) return "onehot: malformed member";
        const [k, side] = entry;
        if (!this.constraintOk(k) || side !== "A" && side !== "B") return "onehot: bad member";
        const Mlc = side === "A" ? this.r.A[k] : this.r.B[k];
        const M = this.view(Mlc), N = this.view(side === "A" ? this.r.B[k] : this.r.A[k]), C = this.view(this.r.C[k]);
        if (M.open.size !== 0) return `onehot: multiplicand of constraint ${k} is not determined`;
        if (N.open.size !== 1 || C.open.size !== 0) return `onehot: constraint ${k} does not isolate one wire when its multiplicand is nonzero`;
        const key = this.normal(Mlc);
        if (key === null) return `onehot: multiplicand of constraint ${k} is constant here`;
        const cut = key.lastIndexOf("|");
        const sym = key.slice(0, cut), c0 = key.slice(cut + 1);
        if (base === null) base = sym;
        else if (base !== sym) return "onehot: members do not share one form";
        if (constants.has(c0)) return "onehot: two members have the same constant";
        constants.add(c0);
        const x = N.open.keys().next().value;
        if (wires.has(x)) return "onehot: a wire has two members";
        if (!row.row.has(x)) return `onehot: wire ${x} is not in the row`;
        wires.add(x);
      }
      for (const x of wires) this.mark(x);
      return null;
    }
    if (s.t === "split") {
      if (!this.constraintOk(s.k) || s.side !== "A" && s.side !== "B" || !Array.isArray(s.xs) || !s.xs.length)
        return "split: malformed";
      const form = s.side === "A" ? this.r.A[s.k] : this.r.B[s.k];
      for (const w of form.w) if (!this.isDet(w)) return `split: form of constraint ${s.k} uses undetermined wire ${w}`;
      const key = this.normal(form);
      if (key === null) return `split: form of constraint ${s.k} is constant here`;
      for (const x of s.xs) if (!this.wireOk(x)) return "split: bad wire";
      const run = (branch, zero) => {
        if (!branch || !Array.isArray(branch.steps)) return { err: "split: malformed branch", dead: false, ok: false };
        const frame = { det: /* @__PURE__ */ new Set(), val: /* @__PURE__ */ new Map(), zero: zero ? form : null, nz: zero ? null : form };
        this.frames.push(frame);
        try {
          if (zero) {
            const terms = [];
            let c0 = 0n;
            for (let i = 0; i < form.w.length; i++) {
              const v = this.value(form.w[i]);
              if (v === void 0) terms.push([form.w[i], form.c[i]]);
              else c0 = md(c0 + form.c[i] * v, p);
            }
            if (terms.length === 1) frame.val.set(terms[0][0], md(-c0 * inv(terms[0][1], p), p));
          }
          for (const sub of branch.steps) {
            const err = this.step(sub);
            if (err) return { err: (zero ? "zero" : "nonzero") + " case: " + err, dead: false, ok: false };
          }
          if (branch.dead !== void 0) {
            if (!this.constraintOk(branch.dead) || this.reduce(branch.dead).kind !== "dead")
              return { err: `split: constraint ${branch.dead} is not contradictory in the ${zero ? "zero" : "nonzero"} case`, dead: false, ok: false };
            return { err: null, dead: true, ok: true };
          }
          for (const x of s.xs) if (!this.isDet(x))
            return { err: `split: wire ${x} is not determined in the ${zero ? "zero" : "nonzero"} case`, dead: false, ok: false };
          return { err: null, dead: false, ok: true };
        } finally {
          this.frames.pop();
        }
      };
      const z = run(s.zero, true);
      if (z.err) return z.err;
      const n2 = run(s.nonzero, false);
      if (n2.err) return n2.err;
      if (z.dead && n2.dead) return "split: both cases contradictory";
      for (const x of s.xs) this.mark(x);
      return null;
    }
    return "unknown step type";
  }
};
function checkProof(r, steps) {
  const replay = new Replay(r);
  try {
    for (const s of steps) {
      const err = replay.step(s);
      if (err) return { ok: false, error: `step ${replay.count}: ${err}`, determined: replay.det, steps: replay.count };
    }
  } catch (e) {
    return { ok: false, error: `step ${replay.count}: ${e instanceof Error ? e.message : String(e)}`, determined: replay.det, steps: replay.count };
  }
  return { ok: true, determined: replay.det, steps: replay.count };
}
function firstViolation(r, w) {
  const p = r.prime;
  if (w.length !== r.nWires || w[0] !== 1n) return -2;
  const ev = (lc) => {
    let acc = 0n;
    for (let i = 0; i < lc.w.length; i++) acc += lc.c[i] * w[lc.w[i]];
    return md(acc, p);
  };
  for (let k = 0; k < r.nConstraints; k++)
    if (md(ev(r.A[k]) * ev(r.B[k]) - ev(r.C[k]), p) !== 0n) return k;
  return -1;
}
function checkCounterexample(r, a, b) {
  const p = r.prime;
  for (const w of [a, b]) {
    if (w.length !== r.nWires) return { ok: false, error: "assignment length differs from wire count", differingOutputs: [] };
    for (const v of w) if (typeof v !== "bigint" || v < 0n || v >= p) return { ok: false, error: "assignment value outside the field", differingOutputs: [] };
  }
  const va = firstViolation(r, a), vb = firstViolation(r, b);
  if (va === -2 || vb === -2) return { ok: false, error: "the constant wire must be one in both assignments", differingOutputs: [] };
  if (va >= 0) return { ok: false, error: `first assignment violates constraint ${va}`, differingOutputs: [] };
  if (vb >= 0) return { ok: false, error: `second assignment violates constraint ${vb}`, differingOutputs: [] };
  for (let w = 1 + r.nPubOut; w < r.inputEnd; w++)
    if (a[w] !== b[w]) return { ok: false, error: `assignments differ on input wire ${w}`, differingOutputs: [] };
  const diff = [];
  for (let w = 1; w <= r.nPubOut; w++) if (a[w] !== b[w]) diff.push(w);
  if (!diff.length) return { ok: false, error: "assignments agree on every output", differingOutputs: [] };
  return { ok: true, differingOutputs: diff };
}

// ../carrycert-core/src/determinism/cex.ts
function rng(seed) {
  let s = seed >>> 0 || 2654435769;
  return () => {
    s |= 0;
    s = s + 1831565813 | 0;
    let t = Math.imul(s ^ s >>> 15, 1 | s);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return (t ^ t >>> 14) >>> 0;
  };
}
var Index = class {
  constructor(r) {
    this.r = r;
    const n2 = r.nWires, m = r.nConstraints;
    const counts = new Int32Array(n2 + 1);
    const mark = new Int32Array(n2).fill(-1);
    this.cw = new Array(m);
    for (let k = 0; k < m; k++) {
      const list = [];
      for (const lc of [r.A[k], r.B[k], r.C[k]])
        for (const w of lc.w) if (w !== 0 && mark[w] !== k) {
          mark[w] = k;
          list.push(w);
        }
      this.cw[k] = Int32Array.from(list);
      for (const w of list) counts[w + 1]++;
    }
    for (let i = 0; i < n2; i++) counts[i + 1] += counts[i];
    this.occStart = counts;
    this.occ = new Int32Array(counts[n2]);
    const fill = counts.slice(0, n2);
    for (let k = 0; k < m; k++) for (const w of this.cw[k]) this.occ[fill[w]++] = k;
  }
  cw;
  occStart;
  occ;
};
function looseScale(weights, p) {
  const ok = (scale) => {
    const h = weights.map((g) => abs(balanced(g * scale, p))).sort((x, y) => x < y ? -1 : x > y ? 1 : 0);
    let prefix = 0n;
    for (const v of h) {
      if (v <= prefix) return false;
      prefix += v;
    }
    return true;
  };
  if (weights.some((g) => g === 0n)) return null;
  if (ok(1n)) return 1n;
  const order = weights.map((g, i) => ({ i, m: abs(balanced(g, p)) })).sort((x, y) => x.m < y.m ? -1 : x.m > y.m ? 1 : 0);
  for (let t = 0; t < Math.min(order.length, 16); t++) {
    const scale = modInv(weights[order[t].i], p);
    if (ok(scale)) return scale;
  }
  return null;
}
function subsetSolutions(weights, target, p, maxSolutions = 4) {
  const scale = looseScale(weights, p);
  if (scale === null) return null;
  const h = weights.map((g) => balanced(g * scale, p));
  const order = h.map((v, i) => i).sort((x, y) => abs(h[x]) > abs(h[y]) ? -1 : abs(h[x]) < abs(h[y]) ? 1 : 0);
  let pos = 0n, neg = 0n;
  for (const v of h) {
    if (v > 0n) pos += v;
    else neg += v;
  }
  const t0 = mod(target * scale, p);
  let j = (neg - t0) / p;
  while (t0 + j * p < neg) j++;
  while (t0 + (j - 1n) * p >= neg) j--;
  const out = [];
  for (; t0 + j * p <= pos; j++) {
    let tau = t0 + j * p;
    let restPos = pos, restNeg = neg;
    const beta = new Array(weights.length).fill(0);
    let ok = true;
    for (const i of order) {
      const v = h[i];
      if (v > 0n) restPos -= v;
      else restNeg -= v;
      const withIt = tau - v;
      const canTake = withIt >= restNeg && withIt <= restPos;
      const canSkip = tau >= restNeg && tau <= restPos;
      if (canTake) {
        beta[i] = 1;
        tau = withIt;
      } else if (!canSkip) {
        ok = false;
        break;
      }
    }
    if (ok && tau === 0n) {
      out.push(beta);
      if (out.length >= maxSolutions) break;
    }
  }
  return out;
}
var Solver = class _Solver {
  /**
   * `extra`, when given, adds the equation extra = 0 as a virtual constraint.
   * It is used to steer inputs into a degenerate case; the pair that results
   * is still judged against the original system only.
   */
  constructor(r, ix, dom2, domWires, undetermined, chooser, twoValuedFirst, maxChoices, extra = null) {
    this.r = r;
    this.ix = ix;
    this.dom2 = dom2;
    this.domWires = domWires;
    this.undetermined = undetermined;
    this.chooser = chooser;
    this.twoValuedFirst = twoValuedFirst;
    this.maxChoices = maxChoices;
    this.extra = extra;
    this.p = r.prime;
    this.m = r.nConstraints + (extra ? 1 : 0);
    this.w = new Array(r.nWires).fill(void 0);
    this.un = new Int32Array(this.m);
    this.done = new Uint8Array(this.m);
    this.queued = new Uint8Array(this.m);
    for (let k = 0; k < r.nConstraints; k++) this.un[k] = ix.cw[k].length;
    this.extraWires = extra ? new Set(extra.w.filter((x) => x !== 0)) : null;
    if (extra) this.un[r.nConstraints] = this.extraWires.size;
    this.inputPtr = 1 + r.nPubOut;
    this.w[0] = 1n;
  }
  p;
  w;
  un;
  done;
  queue = [];
  queued;
  multi = [];
  domPtr = 0;
  livePtr = 0;
  failed = false;
  choices = 0;
  /** Number of constraints including the optional virtual one (index r.nConstraints). */
  m;
  extraWires;
  inputPtr;
  static EMPTY = { w: [], c: [] };
  lcA(k) {
    return k < this.r.nConstraints ? this.r.A[k] : _Solver.EMPTY;
  }
  lcB(k) {
    return k < this.r.nConstraints ? this.r.B[k] : _Solver.EMPTY;
  }
  lcC(k) {
    return k < this.r.nConstraints ? this.r.C[k] : this.extra;
  }
  wiresOf(k) {
    return k < this.r.nConstraints ? this.ix.cw[k] : [...this.extraWires];
  }
  push(k) {
    if (!this.queued[k] && !this.done[k]) {
      this.queued[k] = 1;
      this.queue.push(k);
    }
  }
  assign(x, v) {
    if (this.w[x] !== void 0) {
      if (this.w[x] !== v) this.failed = true;
      return;
    }
    this.w[x] = v;
    for (let i = this.ix.occStart[x]; i < this.ix.occStart[x + 1]; i++) {
      const k = this.ix.occ[i];
      this.un[k]--;
      this.push(k);
    }
    if (this.extraWires && this.extraWires.has(x)) {
      this.un[this.r.nConstraints]--;
      this.push(this.r.nConstraints);
    }
  }
  pick(nOptions) {
    const c = this.chooser;
    const at = c.index++;
    let choice = 0;
    if (c.random) choice = c.random() % nOptions;
    else if (c.flip && c.flip.has(at)) choice = 1 % nOptions;
    c.log.push(choice);
    this.choices++;
    return choice;
  }
  freeValue() {
    const c = this.chooser;
    const at = c.index++;
    this.choices++;
    let v;
    if (c.random) {
      const roll = c.random() % 8;
      if (roll < 3) v = BigInt(c.random() % 4);
      else if (roll < 5) v = BigInt(c.random() % 65536);
      else {
        v = 0n;
        for (let i = 0; i < 9; i++) v = v << 32n | BigInt(c.random());
        v = mod(v, this.p);
      }
    } else v = c.flip && c.flip.has(at) ? 1n : 0n;
    c.log.push(Number(v % 1000000007n));
    return v;
  }
  evalLC(lc) {
    let val = 0n;
    let open = null;
    for (let i = 0; i < lc.w.length; i++) {
      const v = this.w[lc.w[i]];
      if (v === void 0) (open ??= /* @__PURE__ */ new Map()).set(lc.w[i], lc.c[i]);
      else val += lc.c[i] * v;
    }
    return { val: val % this.p, open };
  }
  /** Solve or classify one constraint. `allowChoice` enables multi-solution picks. */
  process(k, allowChoice) {
    if (this.done[k]) return;
    const p = this.p;
    const A = this.evalLC(this.lcA(k)), B = this.evalLC(this.lcB(k)), C = this.evalLC(this.lcC(k));
    if (A.open && B.open) {
      const wires = /* @__PURE__ */ new Set([...A.open.keys(), ...B.open.keys(), ...C.open ? C.open.keys() : []]);
      if (wires.size !== 1) return;
      const x = wires.values().next().value;
      const a1 = A.open.get(x) ?? 0n, b1 = B.open.get(x) ?? 0n, c1 = C.open?.get(x) ?? 0n;
      const q2 = mod(a1 * b1, p), q1 = mod(a1 * B.val + A.val * b1 - c1, p), q0 = mod(A.val * B.val - C.val, p);
      const roots = this.quadRoots(q2, q1, q0);
      if (roots === null) {
        this.done[k] = 1;
        return;
      }
      if (!roots.length) {
        this.failed = true;
        return;
      }
      if (roots.length === 1) {
        this.assign(x, roots[0]);
        return;
      }
      if (!allowChoice) {
        if (this.wiresOf(k).length !== 1) this.multi.push(k);
        return;
      }
      this.assign(x, roots[this.pick(2)]);
      return;
    }
    const row = /* @__PURE__ */ new Map();
    let rhs;
    if (!A.open && !B.open) {
      if (C.open) for (const [w, c] of C.open) row.set(w, c);
      rhs = mod(A.val * B.val - C.val, p);
    } else {
      const m = A.open ? B.val : A.val;
      const N = A.open ? A : B;
      for (const [w, c] of N.open) {
        const v = mod(c * m, p);
        if (v !== 0n) row.set(w, v);
      }
      if (C.open) for (const [w, c] of C.open) {
        const v = mod((row.get(w) ?? 0n) - c, p);
        if (v === 0n) row.delete(w);
        else row.set(w, v);
      }
      rhs = mod(C.val - m * N.val, p);
    }
    if (!row.size) {
      if (rhs !== 0n) {
        this.failed = true;
        return;
      }
      this.done[k] = 1;
      return;
    }
    if (row.size === 1) {
      const [x, c] = row.entries().next().value;
      this.assign(x, mod(rhs * modInv(c, p), p));
      return;
    }
    if (row.size > 600) return;
    const xs = [], weights = [];
    let target = rhs;
    for (const [x, c] of row) {
      const d = this.dom2.get(x);
      if (!d) return;
      xs.push(x);
      weights.push(mod(c * (d[1] - d[0]), p));
      target = mod(target - c * d[0], p);
    }
    const sols = subsetSolutions(weights, target, p);
    if (sols === null) return;
    if (!sols.length) {
      this.failed = true;
      return;
    }
    let sol = sols[0];
    if (sols.length > 1) {
      if (!allowChoice) {
        this.multi.push(k);
        return;
      }
      sol = sols[this.pick(sols.length)];
    }
    for (let i = 0; i < xs.length; i++) this.assign(xs[i], this.dom2.get(xs[i])[sol[i]]);
  }
  quadRoots(q2, q1, q0) {
    const p = this.p;
    if (q2 === 0n) {
      if (q1 === 0n) return q0 === 0n ? null : [];
      return [mod(-q0 * modInv(q1, p), p)];
    }
    const inv2a = modInv(2n * q2, p);
    const disc = mod(q1 * q1 - 4n * q2 * q0, p);
    if (disc === 0n) return [mod(-q1 * inv2a, p)];
    const s = modSqrt(disc, p);
    if (s === null) return [];
    const r1 = mod((-q1 + s) * inv2a, p), r2 = mod((-q1 - s) * inv2a, p);
    return r1 < r2 ? [r1, r2] : [r2, r1];
  }
  drain() {
    while (this.queue.length && !this.failed) {
      const k = this.queue.pop();
      this.queued[k] = 0;
      this.process(k, false);
    }
  }
  chooseTwoValued() {
    while (this.domPtr < this.domWires.length) {
      const x = this.domWires[this.domPtr];
      if (this.w[x] !== void 0) {
        this.domPtr++;
        continue;
      }
      const d = this.dom2.get(x);
      this.assign(x, d[this.pick(2)]);
      return true;
    }
    return false;
  }
  /** Lazy-input mode: give the next unassigned input its strategy value. */
  chooseInput(inputs) {
    while (this.inputPtr < this.r.inputEnd) {
      const x = this.inputPtr++;
      if (this.w[x] !== void 0) continue;
      this.assign(x, inputs.get(x) ?? 0n);
      return true;
    }
    return false;
  }
  chooseFromLive() {
    const m = this.m;
    while (this.livePtr < m) {
      const k = this.livePtr;
      if (this.done[k] || this.un[k] === 0) {
        this.livePtr++;
        continue;
      }
      let pickWire = -1;
      const ws = this.wiresOf(k);
      for (let i = 0; i < ws.length; i++) {
        const x = ws[i];
        if (this.w[x] !== void 0) continue;
        if (pickWire < 0) pickWire = x;
        if (this.undetermined && this.undetermined[x]) {
          pickWire = x;
          break;
        }
      }
      if (pickWire < 0) {
        this.livePtr++;
        continue;
      }
      this.assign(pickWire, this.freeValue());
      return true;
    }
    return false;
  }
  /**
   * `lazyInputs` leaves the inputs open so propagation can solve for the ones
   * a degenerate case forces; the rest take their strategy value when stuck.
   */
  run(inputs, lazyInputs = false) {
    if (!lazyInputs) for (const [x, v] of inputs) this.assign(x, v);
    for (let k = 0; k < this.m; k++) this.push(k);
    for (; ; ) {
      this.drain();
      if (this.failed) return null;
      if (this.choices > this.maxChoices) return null;
      if (lazyInputs && this.chooseInput(inputs)) continue;
      let acted = false;
      while (this.multi.length && !acted) {
        const k = this.multi.pop();
        const before = this.choices;
        this.process(k, true);
        if (this.failed) return null;
        acted = this.choices > before || this.queue.length > 0;
      }
      if (acted) continue;
      if (this.twoValuedFirst) {
        if (this.chooseTwoValued() || this.chooseFromLive()) continue;
      } else if (this.chooseFromLive() || this.chooseTwoValued()) continue;
      break;
    }
    for (let x = 1; x < this.r.nWires; x++) {
      if (this.w[x] !== void 0) continue;
      const d = this.dom2.get(x);
      this.assign(x, d ? d[this.pick(2)] : this.freeValue());
      this.drain();
      if (this.failed) return null;
    }
    return this.w;
  }
};
function inputStrategies(r, next, twoValued) {
  const first = 1 + r.nPubOut, n2 = r.inputEnd - first;
  const p = r.prime;
  const all = (f) => () => {
    const m = /* @__PURE__ */ new Map();
    for (let i = 0; i < n2; i++) {
      const d = twoValued.get(first + i);
      const v = mod(f(i), p);
      m.set(first + i, d ? v === d[0] || v === d[1] ? v : d[Number(v & 1n)] : v);
    }
    return m;
  };
  const field = () => {
    let v = 0n;
    for (let i = 0; i < 9; i++) v = v << 32n | BigInt(next());
    return mod(v, p);
  };
  return [
    { name: "zeros", gen: all(() => 0n) },
    { name: "ones", gen: all(() => 1n) },
    { name: "bits", gen: all(() => BigInt(next() & 1)) },
    { name: "small", gen: all(() => BigInt(next() % 16)) },
    { name: "equal-small", gen: (() => {
      const v = BigInt(next() % 16);
      return all(() => v);
    })() },
    { name: "bytes", gen: all(() => BigInt(next() % 256)) },
    { name: "u32", gen: all(() => BigInt(next())) },
    { name: "equal-field", gen: (() => {
      const v = field();
      return all(() => v);
    })() },
    { name: "field", gen: all(() => field()) }
  ];
}
function findCounterexample(r, proof, options = {}) {
  if (r.nPubOut === 0) return null;
  const t0 = performance.now();
  const budget = options.timeBudgetMs ?? 15e3;
  const next = rng(options.seed ?? 12587047);
  const ix = new Index(r);
  const dom2 = /* @__PURE__ */ new Map();
  for (const [w, v] of proof.twoValued) dom2.set(w, v.r);
  const domWires = [...dom2.keys()].sort((x, y) => x - y);
  const undet = new Uint8Array(r.nWires);
  for (let w = 0; w < r.nWires; w++) undet[w] = proof.determined[w] ? 0 : 1;
  const maxChoices = options.maxChoices ?? 2e4;
  let solves = 0;
  const maxSolves = options.maxSolves ?? Number.MAX_SAFE_INTEGER;
  const timeUp = () => performance.now() - t0 > budget || solves >= maxSolves;
  const solve = (inputs, chooser, twoValuedFirst) => {
    solves++;
    return new Solver(r, ix, dom2, domWires, undet, chooser, twoValuedFirst, maxChoices).run(inputs);
  };
  const outputsDiffer = (a, b) => {
    for (let w = 1; w <= r.nPubOut; w++) if (a[w] !== b[w]) return true;
    return false;
  };
  const confirm = (a, b, strategy) => {
    const res = checkCounterexample(r, a, b);
    return res.ok ? { a, b, differingOutputs: res.differingOutputs, strategy } : null;
  };
  const vary = (inputs, label) => {
    for (const twoValuedFirst of [true, false]) {
      if (timeUp()) return null;
      const base = { flip: null, random: null, index: 0, log: [] };
      const a = solve(inputs, base, twoValuedFirst);
      if (!a) continue;
      const points = base.index;
      if (!points) return null;
      const tag = twoValuedFirst ? "bits-first" : "live-first";
      const limit = Math.min(points, 48);
      for (let j = 0; j < limit && !timeUp(); j++) {
        const b = solve(inputs, { flip: /* @__PURE__ */ new Set([j]), random: null, index: 0, log: [] }, twoValuedFirst);
        if (b && outputsDiffer(a, b)) {
          const hit2 = confirm(a, b, `${label}/flip${j}/${tag}`);
          if (hit2) return hit2;
        }
      }
      for (let j = 0; j < 6 && !timeUp(); j++) {
        const b = solve(inputs, { flip: null, random: rng(next()), index: 0, log: [] }, twoValuedFirst);
        if (b && outputsDiffer(a, b)) {
          const hit2 = confirm(a, b, `${label}/random${j}/${tag}`);
          if (hit2) return hit2;
        }
      }
    }
    return null;
  };
  const generic = () => {
    for (const strat of inputStrategies(r, next, dom2)) {
      if (timeUp()) return null;
      const hit2 = vary(strat.gen(), strat.name);
      if (hit2) return hit2;
    }
    return null;
  };
  const directed = () => {
    const forms = [];
    const seen = /* @__PURE__ */ new Set();
    const add = (item) => {
      for (const c of item.conditional) {
        const key = c.k + c.side;
        if (!seen.has(key) && forms.length < 48) {
          seen.add(key);
          forms.push(c);
        }
      }
    };
    for (const item of proof.open) if (item.wire <= r.nPubOut) add(item);
    for (const item of proof.open) if (item.wire > r.nPubOut) add(item);
    const first = 1 + r.nPubOut;
    for (const f of forms) {
      const form = f.side === "A" ? r.A[f.k] : r.B[f.k];
      for (const strat of inputStrategies(r, next, dom2).filter((s) => ["zeros", "small", "bits", "field"].includes(s.name))) {
        if (timeUp()) return null;
        const wanted = strat.gen();
        solves++;
        const a = new Solver(r, ix, dom2, domWires, undet, { flip: null, random: null, index: 0, log: [] }, true, maxChoices, form).run(wanted, true);
        if (!a) continue;
        const inputs = /* @__PURE__ */ new Map();
        for (let w = first; w < r.inputEnd; w++) inputs.set(w, a[w]);
        const hit2 = vary(inputs, `directed(c${f.k}${f.side})/${strat.name}`);
        if (hit2) return hit2;
      }
    }
    return null;
  };
  let hit = generic();
  if (hit) return hit;
  hit = directed();
  if (hit) return hit;
  for (let round = 1; round < 6 && !timeUp(); round++) {
    hit = generic();
    if (hit) return hit;
  }
  return null;
}

// ../carrycert-core/src/determinism/index.ts
var DETERMINISM_SCHEMA = "colony.determinism/1";
var ENGINE_VERSION = "1.0.0";
function countSteps(steps) {
  let n2 = 0;
  for (const s of steps) {
    n2++;
    if (s.t === "split") n2 += countSteps(s.zero.steps) + countSteps(s.nonzero.steps);
  }
  return n2;
}
function formatLC(lc, prime, name, maxTerms = 6) {
  if (!lc.w.length) return "0";
  const parts = [];
  for (let i = 0; i < lc.w.length && i < maxTerms; i++) {
    const c = balanced(lc.c[i], prime);
    const mag = c < 0n ? -c : c;
    const sign = c < 0n ? "-" : "+";
    const body = lc.w[i] === 0 ? mag.toString() : (mag === 1n ? "" : (mag.toString().length > 12 ? "k" + (i + 1) : mag.toString()) + "*") + name(lc.w[i]);
    parts.push(parts.length ? ` ${sign} ${body}` : (sign === "-" ? "-" : "") + body);
  }
  if (lc.w.length > maxTerms) parts.push(` + ...(${lc.w.length - maxTerms} more)`);
  return parts.join("");
}
function analyzeParsed(base, options = {}) {
  const tStart = performance.now();
  const r = withAssumptions(base, options.assumptions);
  const binary = [...new Set(options.assumptions?.binary ?? [])].sort((x, y) => x - y);
  const sym = options.sym ? parseSym(options.sym) : null;
  const name = (w) => sym?.names.get(w) ?? (w === 0 ? "1" : `wire[${w}]`);
  const strict = Boolean(options.strict);
  const declaredInputs = base.nPubIn + base.nPrvIn;
  let complete, basis;
  if (base.inputLayout !== "label-map") {
    complete = false;
    basis = "the R1CS has no wire-to-label map, so its input wires cannot be established";
  } else if (base.inputsAllWired) {
    complete = true;
    basis = "every declared input has its own wire";
  } else {
    complete = false;
    basis = "some declared inputs have no wire (merged or substituted by compiler simplification)";
  }
  const tProve0 = performance.now();
  const proof = prove(r, options);
  const tProve = performance.now() - tProve0;
  const tReplay0 = performance.now();
  const replay = checkProof(r, proof.steps);
  const tReplay = performance.now() - tReplay0;
  const det = replay.ok ? replay.determined : new Uint8Array(r.nWires);
  let outDet = 0;
  const outUndet = [];
  for (let w = 1; w <= r.nPubOut; w++) {
    if (det[w]) outDet++;
    else if (outUndet.length < 64) outUndet.push({ wire: w, name: name(w) });
  }
  let wiresDet = 0;
  for (let w = 0; w < r.nWires; w++) wiresDet += det[w];
  const allOutputs = outDet === r.nPubOut;
  const allWires = wiresDet === r.nWires;
  const report = {
    schema: DETERMINISM_SCHEMA,
    engine: ENGINE_VERSION,
    verdict: "Unknown",
    property: strict ? "witness-uniqueness" : "output-determinism",
    claim: "",
    method: "r1cs-determinism-propagation",
    field: { prime: r.prime.toString(), bits: r.prime.toString(2).length },
    circuit: {
      wires: base.nWires,
      constraints: base.nConstraints,
      outputs: r.nPubOut,
      public_inputs: r.nPubIn,
      private_inputs: r.nPrvIn,
      private_input_wires: r.nPrvInWires,
      input_layout: r.inputLayout
    },
    outputs: { total: r.nPubOut, determined: outDet, undetermined: outUndet },
    wires: { total: r.nWires, determined: wiresDet },
    rules: proof.stats.rules,
    inputs: { declared: declaredInputs, wired: base.nPubIn + base.nPrvInWires, complete, basis },
    time_ms: { parse: 0, prove: tProve, replay: tReplay, counterexample: 0, total: 0 }
  };
  if (proof.stats.timedOut) report.timed_out = true;
  if (binary.length) report.assumptions = { binary_inputs: binary.map((w) => ({ wire: w, name: name(w) })) };
  const under = binary.length ? ` Assumes ${binary.length} input signal(s) are 0 or 1.` : "";
  if (!replay.ok) {
    report.reason = "internal: independent replay rejected the derivation (" + replay.error + ")";
    report.claim = "No claim.";
    report.time_ms.total = performance.now() - tStart;
    return report;
  }
  const includeProof = options.includeProof !== false;
  const proved = strict ? allWires : allOutputs && r.nPubOut > 0;
  if (proved) {
    report.verdict = "Certified";
    report.claim = strict ? "For every assignment of the input signals there is at most one satisfying assignment of all signals." : "For every assignment of the input signals, every satisfying witness has the same output signals.";
    report.claim += under;
    if (includeProof) report.proof = { steps: proof.steps, step_count: countSteps(proof.steps), replayed: true };
    report.time_ms.total = performance.now() - tStart;
    return report;
  }
  if (!strict && r.nPubOut === 0) {
    report.reason = "The circuit declares no output signals, so output determinism says nothing about it. " + (allWires ? "Every signal is determined by the inputs." : `${r.nWires - wiresDet} internal signal(s) are not fixed by the inputs; see 'open'.`);
    report.claim = "No claim.";
  }
  let tCex = 0;
  if (!strict && r.nPubOut > 0 && !complete) {
    report.reason = `${r.nPubOut - outDet} of ${r.nPubOut} output signal(s) are not shown to be fixed by the inputs. No counterexample search was run: ${basis}. Scan the .circom source, or an R1CS compiled with circom --O0.`;
  }
  if (!strict && r.nPubOut > 0 && complete && options.searchCounterexample !== false) {
    const t0 = performance.now();
    const cex = findCounterexample(r, proof, { timeBudgetMs: options.counterexampleBudgetMs, seed: options.seed, maxSolves: options.counterexampleMaxSolves });
    tCex = performance.now() - t0;
    if (cex) {
      const again = checkCounterexample(r, cex.a, cex.b);
      if (again.ok) {
        const inputs = {};
        for (let w = 1 + r.nPubOut; w < r.inputEnd; w++) inputs[name(w)] = cex.a[w].toString();
        let differing = 0;
        for (let w = 0; w < r.nWires; w++) if (cex.a[w] !== cex.b[w]) differing++;
        report.verdict = "Broken";
        report.claim = "Two satisfying witnesses share every input signal and differ on an output signal." + (binary.length ? " Both respect the declared binary-input assumptions." : "");
        report.method = "checked-counterexample";
        report.counterexample = {
          strategy: cex.strategy,
          inputs,
          differing_outputs: again.differingOutputs.map((w) => ({ wire: w, name: name(w), a: cex.a[w].toString(), b: cex.b[w].toString() })),
          differing_wires: differing,
          witness_a: cex.a.map((v) => v.toString()),
          witness_b: cex.b.map((v) => v.toString()),
          replayed: true
        };
      }
    }
  }
  report.time_ms.counterexample = tCex;
  if (report.verdict === "Unknown") {
    if (!report.claim) report.claim = "No claim.";
    if (!report.reason) {
      report.reason = strict ? `${r.nWires - wiresDet} signal(s) are not shown to be fixed by the inputs.` : `${r.nPubOut - outDet} of ${r.nPubOut} output signal(s) are not shown to be fixed by the inputs, and no counterexample was found.`;
    }
  }
  if (includeProof) report.proof = { steps: proof.steps, step_count: countSteps(proof.steps), replayed: true };
  const open = [];
  for (const item of proof.open) {
    if (det[item.wire]) continue;
    if (open.length >= 200) break;
    open.push({
      wire: item.wire,
      name: name(item.wire),
      role: wireRole(r, item.wire),
      fixed_if_nonzero: item.conditional.map((c) => ({
        constraint: c.k,
        form: formatLC(c.side === "A" ? r.A[c.k] : r.B[c.k], r.prime, name)
      })),
      nonlinear_constraints: item.nonlinear,
      occurrences: item.occurrences
    });
  }
  report.open = open;
  report.open_total = r.nWires - wiresDet;
  report.time_ms.total = performance.now() - tStart;
  return report;
}
function analyzeR1CS(bytes, options = {}) {
  const t0 = performance.now();
  const r = parseR1CS(bytes, options.limits);
  const tParse = performance.now() - t0;
  const report = analyzeParsed(r, options);
  report.time_ms.parse = tParse;
  report.time_ms.total += tParse;
  return report;
}
function verifyReport(bytes, report, limits) {
  if (!report || typeof report !== "object" || report.schema !== DETERMINISM_SCHEMA)
    return { ok: false, verdict: "Unknown", error: "unsupported report schema" };
  if (report.verdict !== "Certified" && report.verdict !== "Broken" && report.verdict !== "Unknown")
    return { ok: false, verdict: "Unknown", error: "unrecognised verdict" };
  if (report.verdict !== "Unknown" && report.property !== "output-determinism" && report.property !== "witness-uniqueness")
    return { ok: false, verdict: "Unknown", error: "unrecognised property" };
  const alias = report.input_alias_wires;
  if (alias !== void 0 && alias !== null && !(Array.isArray(alias) && alias.length === 0))
    return { ok: false, verdict: "Unknown", error: "a report may not declare extra input wires" };
  let base, r;
  try {
    const binary = (report.assumptions?.binary_inputs ?? []).map((b) => b.wire);
    if (binary.some((w) => !Number.isInteger(w))) throw new Error("assumption wires must be integers");
    base = parseR1CS(bytes, limits);
    r = withAssumptions(base, { binary });
  } catch (e) {
    return { ok: false, verdict: "Unknown", error: e instanceof Error ? e.message : String(e) };
  }
  if (report.verdict === "Certified") {
    if (!report.proof || !Array.isArray(report.proof.steps)) return { ok: false, verdict: "Unknown", error: "report carries no derivation" };
    const out = checkProof(r, report.proof.steps);
    if (!out.ok) return { ok: false, verdict: "Unknown", error: out.error };
    if (report.property === "witness-uniqueness") {
      for (let w = 0; w < r.nWires; w++) if (!out.determined[w]) return { ok: false, verdict: "Unknown", error: `wire ${w} is not determined by the derivation` };
    } else {
      if (r.nPubOut === 0) return { ok: false, verdict: "Unknown", error: "circuit has no outputs" };
      for (let w = 1; w <= r.nPubOut; w++) if (!out.determined[w]) return { ok: false, verdict: "Unknown", error: `output wire ${w} is not determined by the derivation` };
    }
    return { ok: true, verdict: "Certified" };
  }
  if (report.verdict === "Broken") {
    const cex = report.counterexample;
    if (!cex || !Array.isArray(cex.witness_a) || !Array.isArray(cex.witness_b)) return { ok: false, verdict: "Unknown", error: "report carries no counterexample" };
    if (report.property !== "output-determinism")
      return { ok: false, verdict: "Unknown", error: "a counterexample is a statement about output determinism" };
    if (base.inputLayout !== "label-map" || !base.inputsAllWired)
      return { ok: false, verdict: "Unknown", error: "not every declared input has a wire in this R1CS, so a witness pair is not a counterexample for the circuit" };
    const decimal = (v) => typeof v === "string" && /^(0|[1-9][0-9]*)$/.test(v);
    if (!cex.witness_a.every(decimal) || !cex.witness_b.every(decimal))
      return { ok: false, verdict: "Unknown", error: "witness values must be decimal strings" };
    const a = cex.witness_a.map((v) => BigInt(v)), b = cex.witness_b.map((v) => BigInt(v));
    const out = checkCounterexample(r, a, b);
    if (!out.ok) return { ok: false, verdict: "Unknown", error: out.error };
    return { ok: true, verdict: "Broken" };
  }
  return { ok: true, verdict: "Unknown" };
}

// ../carrycert-core/src/determinism/scan-circom.ts
import { createHash } from "node:crypto";
import * as fs2 from "node:fs";
import * as path2 from "node:path";

// ../carrycert-core/src/determinism/circom.ts
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
function findCircom(explicit) {
  const candidates = [explicit, process.env.CIRCOM_BIN, process.env.CIRCOM, "circom"].filter(Boolean);
  for (const bin of candidates) {
    try {
      const out = spawnSync(bin, ["--version"], { encoding: "utf8", timeout: 15e3 });
      const m = /circom compiler\s+(\d+\.\d+\.\d+)/.exec((out.stdout || "") + (out.stderr || ""));
      if (out.status === 0 && m) return { bin, version: m[1] };
    } catch {
    }
  }
  return null;
}
function stripComments(src) {
  return src.replace(/\/\*[\s\S]*?\*\//g, "").replace(/\/\/.*$/gm, "");
}
function hasMainComponent(source) {
  return /\bcomponent\s+main\b/.test(stripComments(source));
}
function compileCircom(file, options = {}) {
  const found = findCircom(options.bin);
  if (!found)
    return { ok: false, stage: "locate", error: "circom compiler not found. Install circom 2.x (https://docs.circom.io), set CIRCOM_BIN, or scan the compiled .r1cs instead." };
  const abs2 = path.resolve(file);
  let source;
  try {
    source = fs.readFileSync(abs2, "utf8");
  } catch (e) {
    return { ok: false, stage: "source", error: "cannot read " + file + ": " + (e instanceof Error ? e.message : String(e)) };
  }
  const declared = hasMainComponent(source);
  if (!declared && !options.main)
    return { ok: false, stage: "source", error: 'no main component. A library file has no constraint system of its own; pass --main "Template(args)" to instantiate one.' };
  if (declared && options.main)
    return { ok: false, stage: "source", error: "the file already declares a main component; --main applies to library files only." };
  const outDir = options.outDir ?? fs.mkdtempSync(path.join(os.tmpdir(), "speedrunpapi-circom-"));
  fs.mkdirSync(outDir, { recursive: true });
  const cleanup = () => {
    if (!options.outDir) fs.rmSync(outDir, { recursive: true, force: true });
  };
  try {
    let entry = abs2;
    let wrapper = null;
    if (options.main) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*\s*\([^;{}]*\)\s*$/.test(options.main.trim())) {
        cleanup();
        return { ok: false, stage: "source", error: "--main must look like Template(arg, ...)" };
      }
      const pragma = /^\s*pragma\s+circom\s+[^;]+;/m.exec(stripComments(source))?.[0]?.trim() ?? "pragma circom 2.0.0;";
      wrapper = `${pragma}
include ${JSON.stringify(abs2)};
component main = ${options.main.trim()};
`;
      entry = path.join(outDir, path.basename(abs2, path.extname(abs2)) + "__main.circom");
      fs.writeFileSync(entry, wrapper);
    }
    const args = [entry, "--r1cs", "--sym", "-o", outDir];
    if (options.opt) args.push("--" + options.opt);
    if (options.prime) args.push("-p", options.prime);
    const include = [...options.include ?? []];
    if (wrapper) include.push(path.dirname(abs2));
    for (const dir of include) args.push("-l", path.resolve(dir));
    const run = spawnSync(found.bin, args, { encoding: "utf8", timeout: options.timeoutMs ?? 6e5, maxBuffer: 64 << 20 });
    const log = ((run.stdout || "") + (run.stderr || "")).replace(/\x1b\[[0-9;]*m/g, "");
    if (run.error || run.status !== 0) {
      cleanup();
      return { ok: false, stage: "compile", error: run.error ? run.error.message : "circom exited with status " + run.status, log: log.slice(0, 4e3) };
    }
    const base = path.basename(entry, path.extname(entry));
    const r1csPath = path.join(outDir, base + ".r1cs"), symPath = path.join(outDir, base + ".sym");
    if (!fs.existsSync(r1csPath)) {
      cleanup();
      return { ok: false, stage: "output", error: "circom produced no .r1cs", log: log.slice(0, 4e3) };
    }
    const r1cs = new Uint8Array(fs.readFileSync(r1csPath));
    const sym = fs.existsSync(symPath) ? new Uint8Array(fs.readFileSync(symPath)) : new Uint8Array(0);
    const shown = ["--r1cs", "--sym"];
    if (options.opt) shown.push("--" + options.opt);
    if (options.prime) shown.push("-p", options.prime);
    cleanup();
    return { ok: true, r1cs, sym, compiler: "circom " + found.version, args: shown, opt: options.opt ?? "default", entry: path.basename(abs2), wrapper, log };
  } catch (e) {
    cleanup();
    return { ok: false, stage: "compile", error: e instanceof Error ? e.message : String(e) };
  }
}

// ../carrycert-core/src/determinism/scan-circom.ts
var sha256 = (data) => "sha256:" + createHash("sha256").update(data).digest("hex");
function patternToRegex(pattern) {
  const body = pattern.trim().replace(/^main\./, "");
  const esc = body.replace(/[.+?^${}()|\\]/g, "\\$&").replace(/\[/g, "\\[").replace(/\]/g, "\\]").replace(/\*/g, ".*");
  return new RegExp("^main\\." + esc + (/[\]*]$/.test(body) ? "" : "(\\[.*\\])?") + "$");
}
function resolveBinaryInputs(r, symText, patterns) {
  if (!patterns.length) return [];
  const { names } = parseSym(symText);
  const wires = /* @__PURE__ */ new Set();
  for (const pattern of patterns) {
    const re = patternToRegex(pattern);
    let hit = 0;
    for (let w = 1 + r.nPubOut; w < r.inputEnd; w++) {
      const name = names.get(w);
      if (name && re.test(name)) {
        wires.add(w);
        hit++;
      }
    }
    if (!hit) throw new Error(`--assume-binary ${JSON.stringify(pattern)} matches no input signal that has a wire`);
  }
  return [...wires].sort((x, y) => x - y);
}
function scanCircomFile(file, options = {}) {
  let sourceBytes;
  try {
    sourceBytes = new Uint8Array(fs2.readFileSync(path2.resolve(file)));
  } catch (e) {
    return { ok: false, stage: "source", error: "cannot read " + file + ": " + (e instanceof Error ? e.message : String(e)) };
  }
  const levels = options.opt ? [options.opt] : ["O0", "O1"];
  const tried = [];
  let first = null;
  for (const level of levels) {
    const compiled = compileCircom(file, { bin: options.bin, include: options.include, prime: options.prime, main: options.main, timeoutMs: options.timeoutMs, opt: level });
    if (!compiled.ok) {
      if (first) break;
      return { ok: false, stage: compiled.stage, error: compiled.error, log: compiled.log };
    }
    let report;
    try {
      const r = parseR1CS(compiled.r1cs, options.analyze?.limits);
      const binary = resolveBinaryInputs(r, compiled.sym, options.assumeBinary ?? []);
      report = analyzeParsed(r, {
        ...options.analyze,
        sym: compiled.sym,
        assumptions: { binary }
      });
    } catch (e) {
      if (first) break;
      return { ok: false, stage: "analyze", error: e instanceof Error ? e.message : String(e) };
    }
    const result = {
      ok: true,
      report,
      r1cs: compiled.r1cs,
      sym: compiled.sym,
      binding: {
        source: compiled.entry,
        source_sha256: sha256(sourceBytes),
        main: options.main ?? null,
        compiler: compiled.compiler,
        flags: compiled.args,
        r1cs_sha256: sha256(compiled.r1cs)
      }
    };
    if (report.verdict !== "Unknown") {
      if (tried.length) result.binding.also_tried = tried;
      return result;
    }
    tried.push({ flags: compiled.args, verdict: report.verdict });
    if (!first) first = result;
  }
  if (first && tried.length > 1) first.binding.also_tried = tried.slice(1);
  return first;
}

// src/cli.ts
var VERSION = "0.7.1";
function usage() {
  console.log(`speedrunpapi ${VERSION}: output-determinism analysis for Circom circuits and R1CS

Usage:
  speedrunpapi scan <file...> [options]
  speedrunpapi scan --batch files.json [options]
  speedrunpapi verify <report.json> --source <circuit.r1cs>
  speedrunpapi version

What scan decides, per file:
  Certified  every satisfying witness with the same inputs has the same outputs.
             Backed by a derivation that an independent checker has replayed.
  Broken     two satisfying witnesses share all inputs and differ on an output.
             Both witnesses are re-evaluated against every constraint.
  Unknown    neither was established. The open signals are listed.

Inputs:
  .circom    compiled with the circom compiler (must be installed), then analysed
  .r1cs      analysed directly; a sibling .sym supplies signal names

Options:
  --json                    print the result as JSON (add --full for the derivation or witnesses)
  --report <path>           write the full report, for verify (a directory when scanning several files)
  --main "T(args)"          instantiate a library template as the main component
  -l, --include <dir>       circom library directory (repeatable)
  --circom <bin>            circom binary (default: $CIRCOM_BIN, then PATH)
  --opt O0|O1|O2            force one simplification level (default: --O0, then --O1 where exact)
  --prime <name>            circom -p value (bn128, bls12381, goldilocks, ...)
  --assume-binary <pattern> treat matching input signals as bits, e.g. in, "sel[*]" or "*" (repeatable)
  --strict                  require every signal, not just outputs, to be fixed by the inputs
  --sym <file>              .sym for an .r1cs input
  --timeout <seconds>       proof search limit (default 600)
  --cex-timeout <seconds>   counterexample search budget (default 15)
  --sarif <file>            write Broken results as SARIF
  --key <key> | --api <url> | --require-signed   request a signed certificate (uses one credit)

Exit status: 0 all Certified, 2 any Broken, 3 any Unknown, 1 error.
Compute is local. Nothing is uploaded unless a key is supplied.
`);
}
var sha2562 = (data) => "sha256:" + createHash2("sha256").update(data).digest("hex");
function scanOne(file, flags) {
  const abs2 = path3.resolve(file);
  const id = path3.basename(file).replace(/\.[^.]+$/, "");
  const ext = path3.extname(file).toLowerCase();
  const bytes = new Uint8Array(fs3.readFileSync(abs2));
  const source_checksum = sha2562(bytes);
  const analyze = { strict: flags.strict, timeBudgetMs: flags.timeoutMs, counterexampleBudgetMs: flags.cexTimeoutMs };
  if (ext === ".circom") {
    const res = scanCircomFile(abs2, {
      bin: flags.circom,
      include: flags.include,
      main: flags.main,
      opt: flags.opt,
      prime: flags.prime,
      assumeBinary: flags.assumeBinary,
      analyze
    });
    if (!res.ok) {
      return {
        file,
        id,
        verdict: "Unknown",
        method: "circom_" + res.stage + "_failed",
        time_ms: 0,
        source_checksum,
        reason: res.error,
        error: res.log
      };
    }
    return {
      file,
      id,
      verdict: res.report.verdict,
      method: res.report.method,
      reason: res.report.reason,
      time_ms: res.report.time_ms.total,
      source_checksum,
      binding: res.binding,
      report: res.report,
      r1cs: res.r1cs
    };
  }
  if (ext === ".r1cs") {
    const symPath = flags.sym ?? abs2.replace(/\.r1cs$/i, ".sym");
    const sym = fs3.existsSync(symPath) ? new Uint8Array(fs3.readFileSync(symPath)) : void 0;
    try {
      const parsed = parseR1CS(bytes);
      const binary = flags.assumeBinary.length ? (() => {
        if (!sym) throw new Error("--assume-binary needs signal names; pass --sym");
        return resolveBinaryInputs(parsed, sym, flags.assumeBinary);
      })() : [];
      const report = analyzeR1CS(bytes, { ...analyze, sym, assumptions: { binary } });
      return {
        file,
        id,
        verdict: report.verdict,
        method: report.method,
        reason: report.reason,
        time_ms: report.time_ms.total,
        source_checksum,
        binding: { r1cs_sha256: source_checksum, ...sym ? { sym_sha256: sha2562(sym) } : {} },
        report,
        r1cs: bytes
      };
    } catch (e) {
      return {
        file,
        id,
        verdict: "Unknown",
        method: "r1cs_rejected",
        time_ms: 0,
        source_checksum,
        reason: e instanceof Error ? e.message : String(e)
      };
    }
  }
  const legacy = scanPasted(new TextDecoder().decode(bytes), { id, filename: file });
  return {
    file,
    id,
    verdict: legacy.verdict,
    method: legacy.method,
    reason: legacy.reason,
    time_ms: legacy.time_ms,
    source_checksum,
    legacy
  };
}
function fullReport(s) {
  return { ...s.report, binding: s.binding, source_checksum: s.source_checksum, tool: "speedrunpapi " + VERSION };
}
function view(s, full) {
  if (!s.report) {
    return {
      file: s.file,
      id: s.id,
      verdict: s.verdict,
      method: s.method,
      reason: s.reason,
      source_checksum: s.source_checksum,
      ...s.legacy ? { domain: s.legacy.domain, theorem: s.legacy.theorem, certificate: s.legacy.certificate } : {},
      ...s.error ? { compiler_output: s.error } : {},
      time_ms: s.time_ms
    };
  }
  const r = s.report;
  const out = {
    file: s.file,
    id: s.id,
    verdict: r.verdict,
    property: r.property,
    claim: r.claim,
    method: r.method,
    ...r.reason ? { reason: r.reason } : {},
    source_checksum: s.source_checksum,
    binding: s.binding,
    schema: r.schema,
    engine: r.engine,
    field: r.field,
    circuit: r.circuit,
    inputs: r.inputs,
    ...r.assumptions ? { assumptions: r.assumptions } : {},
    outputs: r.outputs,
    wires: r.wires,
    rules: r.rules,
    ...r.timed_out ? { timed_out: true } : {}
  };
  if (r.proof) out.proof = full ? r.proof : { step_count: r.proof.step_count, replayed: r.proof.replayed };
  if (r.counterexample) {
    const c = r.counterexample;
    out.counterexample = full ? c : {
      strategy: c.strategy,
      inputs: c.inputs,
      differing_outputs: c.differing_outputs,
      differing_wires: c.differing_wires,
      replayed: c.replayed
    };
  }
  if (r.open) {
    out.open = full ? r.open : r.open.slice(0, 20);
    out.open_total = r.open_total;
  }
  out.time_ms = r.time_ms;
  return out;
}
var n = (v) => v.toLocaleString("en-US");
var ms = (v) => (v < 10 ? v.toFixed(2) : v < 1e3 ? v.toFixed(0) : (v / 1e3).toFixed(2) + " s").replace(/(\d)$/, v < 1e3 ? "$1 ms" : "$1");
function printHuman(s) {
  console.log(`${s.verdict}  ${s.file}`);
  const r = s.report;
  if (!r) {
    if (s.reason) console.log("  reason   " + s.reason);
    if (s.error) console.log(s.error.split("\n").filter(Boolean).slice(0, 12).map((l) => "  | " + l).join("\n"));
    return;
  }
  console.log("  claim    " + r.claim);
  const b = s.binding;
  const how = b?.compiler ? `${b.compiler} ${(b.flags || []).filter((f) => /^--O|^-p$|^[a-z0-9]+$/.test(f)).join(" ")} \xB7 ` : "";
  console.log(`  system   ${how}${n(r.circuit.constraints)} constraints \xB7 ${n(r.circuit.wires)} wires \xB7 ${n(r.circuit.outputs)} outputs \xB7 ${n(r.circuit.public_inputs + r.circuit.private_inputs)} inputs`);
  if (r.assumptions) console.log(`  assumes  ${r.assumptions.binary_inputs.length} input signal(s) are 0 or 1: ${r.assumptions.binary_inputs.slice(0, 6).map((x) => x.name).join(", ")}${r.assumptions.binary_inputs.length > 6 ? ", ..." : ""}`);
  if (r.verdict === "Certified") {
    const used = Object.entries(r.rules).filter(([, v]) => v).map(([k, v]) => `${k} ${n(v)}`).join(" \xB7 ");
    console.log(`  proof    ${n(r.proof?.step_count ?? 0)} steps (${used}), replayed by the independent checker`);
  } else if (r.verdict === "Broken") {
    const c = r.counterexample;
    const ins = Object.entries(c.inputs);
    console.log("  inputs   " + ins.slice(0, 8).map(([k, v]) => `${k} = ${v.length > 24 ? v.slice(0, 10) + "\u2026" + v.slice(-6) : v}`).join(", ") + (ins.length > 8 ? `, ... (${ins.length} inputs)` : ""));
    for (const d of c.differing_outputs.slice(0, 6)) {
      const short = (v) => v.length > 24 ? v.slice(0, 10) + "\u2026" + v.slice(-6) : v;
      console.log(`  differs  ${d.name}: ${short(d.a)} vs ${short(d.b)}`);
    }
    if (c.differing_outputs.length > 6) console.log(`           ... ${c.differing_outputs.length - 6} more output(s)`);
    console.log("  checked  both witnesses satisfy all " + n(r.circuit.constraints) + " constraints");
  } else {
    if (r.reason) console.log("  reason   " + r.reason);
    console.log(`  outputs  ${n(r.outputs.determined)} of ${n(r.outputs.total)} shown to be fixed by the inputs`);
    if (r.open?.length) {
      console.log(`  open     ${n(r.open_total ?? r.open.length)} signal(s) not shown to be fixed by the inputs. First:`);
      for (const o of r.open.slice(0, 8)) {
        const why = o.fixed_if_nonzero.length ? `fixed by constraint ${o.fixed_if_nonzero[0].constraint} only where (${o.fixed_if_nonzero[0].form}) != 0` : o.nonlinear_constraints.length ? `appears nonlinearly in constraint ${o.nonlinear_constraints[0]}` : o.occurrences ? "no constraint isolates it" : "appears in no constraint";
        console.log(`    ${o.name}  (${o.role.replace("_", " ")}): ${why}`);
      }
    }
  }
  console.log(`  time     prove ${ms(r.time_ms.prove)} \xB7 replay ${ms(r.time_ms.replay)}${r.time_ms.counterexample ? " \xB7 search " + ms(r.time_ms.counterexample) : ""}`);
}
async function requestCertificate(api, key, s) {
  if (!s.report || !s.r1cs) throw new Error("Only Circom and R1CS results can be signed");
  if (s.report.verdict === "Unknown") throw new Error("An Unknown result makes no claim and cannot be signed");
  const body = {
    format: "r1cs",
    source_base64: Buffer.from(s.r1cs).toString("base64"),
    filename: path3.basename(s.file),
    result: s.report.verdict,
    report: fullReport(s),
    gadget_id: s.id,
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
function toSarif(file, s) {
  return {
    tool: { driver: {
      name: "speedrunpapi",
      version: VERSION,
      informationUri: "https://colony.technology",
      rules: [{ id: "output-not-determined", shortDescription: { text: "An output signal is not fixed by the inputs" } }]
    } },
    results: s.verdict === "Broken" ? [{
      ruleId: "output-not-determined",
      level: "error",
      message: { text: `${s.id}: ` + (s.report?.counterexample?.differing_outputs.slice(0, 4).map((d) => d.name).join(", ") ?? "") + " take different values in two satisfying witnesses with the same inputs" },
      locations: [{ physicalLocation: { artifactLocation: { uri: file } } }]
    }] : []
  };
}
async function main() {
  const args = process.argv.slice(2);
  const cmd = args[0];
  if (!cmd || cmd === "-h" || cmd === "--help" || cmd === "help") return usage();
  if (cmd === "version" || cmd === "--version" || cmd === "-V") return void console.log("speedrunpapi " + VERSION);
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
  if (cmd === "verify") {
    const sourceIdx = args.indexOf("--source");
    const sourcePath = sourceIdx >= 0 ? args[sourceIdx + 1] : void 0;
    const reportPath = args.slice(1).find((a, i, all) => !a.startsWith("--") && all[i - 1] !== "--source");
    if (!reportPath || !sourcePath) {
      console.error("Usage: speedrunpapi verify <report.json> --source <circuit.r1cs>");
      process.exit(1);
    }
    const report = JSON.parse(fs3.readFileSync(reportPath, "utf8"));
    const bytes = new Uint8Array(fs3.readFileSync(path3.resolve(sourcePath)));
    const digest = sha2562(bytes);
    const bound = report?.binding?.r1cs_sha256;
    let res;
    if (report?.schema !== "colony.determinism/1")
      res = { ok: false, verdict: "Unknown", error: "not a determinism report (results from versions before 0.7.1 were not proofs and cannot be verified; scan again)" };
    else if (bound && bound !== digest)
      res = { ok: false, verdict: "Unknown", error: `report is bound to ${bound}, but ${sourcePath} is ${digest}` };
    else res = verifyReport(bytes, report);
    const claimed = report?.verdict ?? "?";
    const pass = res.ok && res.verdict === claimed;
    console.log(JSON.stringify({
      ok: pass,
      verdict: pass ? res.verdict : "Unknown",
      claimed,
      claim_verified: pass && claimed !== "Unknown",
      r1cs_sha256: digest,
      ...res.error ? { error: res.error } : {}
    }, null, 2));
    process.exit(pass ? 0 : 1);
  }
  if (cmd === "scan") {
    const files = [];
    let batchManifest, sarifPath, reportPath;
    let api = process.env.EXACTLAB_API || process.env.COLONY_API || "https://api.colony.technology";
    let key = process.env.EXACTLAB_API_KEY || process.env.COLONY_API_KEY;
    let json = false, full = false, requireSigned = false;
    const flags = { include: [], assumeBinary: [], strict: false, timeoutMs: 6e5, cexTimeoutMs: 15e3 };
    const valued = /* @__PURE__ */ new Set([
      "--sarif",
      "--api",
      "--key",
      "--batch",
      "--report",
      "--main",
      "-l",
      "--include",
      "--circom",
      "--opt",
      "--prime",
      "--assume-binary",
      "--sym",
      "--timeout",
      "--cex-timeout"
    ]);
    for (let i = 1; i < args.length; i++) {
      const arg = args[i];
      if (arg === "--json") json = true;
      else if (arg === "--full") full = true;
      else if (arg === "--strict") flags.strict = true;
      else if (arg === "--require-signed") requireSigned = true;
      else if (arg === "--references") {
      } else if (valued.has(arg)) {
        const value = args[++i];
        if (value === void 0) throw new Error("Missing value for " + arg);
        if (arg === "--sarif") sarifPath = value;
        else if (arg === "--api") api = value;
        else if (arg === "--key") key = value;
        else if (arg === "--batch") batchManifest = value;
        else if (arg === "--report") reportPath = value;
        else if (arg === "--main") flags.main = value;
        else if (arg === "-l" || arg === "--include") flags.include.push(value);
        else if (arg === "--circom") flags.circom = value;
        else if (arg === "--opt") {
          if (!/^O[012]$/.test(value)) throw new Error("--opt takes O0, O1 or O2");
          flags.opt = value;
        } else if (arg === "--prime") flags.prime = value;
        else if (arg === "--assume-binary") flags.assumeBinary.push(value);
        else if (arg === "--sym") flags.sym = value;
        else if (arg === "--timeout") flags.timeoutMs = Math.max(1, Number(value)) * 1e3;
        else if (arg === "--cex-timeout") flags.cexTimeoutMs = Math.max(0, Number(value)) * 1e3;
      } else if (arg.startsWith("-")) throw new Error("Unknown scan option: " + arg);
      else files.push(arg);
    }
    if (batchManifest) {
      const abs2 = path3.resolve(batchManifest);
      const text = fs3.readFileSync(abs2, "utf8");
      let list;
      if (text.trimStart().startsWith("[") || text.trimStart().startsWith("{")) {
        const decoded = JSON.parse(text);
        list = Array.isArray(decoded) ? decoded : decoded.files;
      } else list = text.split(/\r?\n/).map((x) => x.trim()).filter((x) => x && !x.startsWith("#"));
      if (!Array.isArray(list) || !list.length || !list.every((x) => typeof x === "string" && x.length))
        throw new Error("Batch manifest needs a nonempty array of file paths");
      files.unshift(...list.map((x) => path3.isAbsolute(x) ? x : path3.resolve(path3.dirname(abs2), x)));
    }
    if (!files.length) throw new Error("Provide at least one source file or --batch manifest");
    if (requireSigned && !key) throw new Error("--require-signed needs --key or COLONY_API_KEY");
    const started = performance.now();
    const results = [];
    const extra = /* @__PURE__ */ new Map();
    const counts = { Certified: 0, Broken: 0, Unknown: 0 };
    const multi = files.length > 1 || Boolean(batchManifest);
    if (reportPath && multi) fs3.mkdirSync(reportPath, { recursive: true });
    for (const file of files) {
      const s = scanOne(file, flags);
      counts[s.verdict]++;
      if (reportPath && s.report) {
        const target = multi ? path3.join(reportPath, s.id + ".report.json") : reportPath;
        fs3.writeFileSync(target, JSON.stringify(fullReport(s)));
        if (s.r1cs && path3.extname(file).toLowerCase() === ".circom")
          fs3.writeFileSync(target.replace(/(\.report)?\.json$/i, "") + ".r1cs", s.r1cs);
      }
      if (key && s.report && s.verdict !== "Unknown") {
        const registered = await requestCertificate(api, key, s);
        const certificate = registered.certificate;
        extra.set(s, {
          certificate_id: certificate?.id,
          signed: Boolean(certificate?.signature && certificate.signature_algorithm === "Ed25519"),
          signature_algorithm: certificate?.signature_algorithm,
          remaining: registered.remaining
        });
      }
      if (requireSigned && !extra.get(s)?.signed)
        throw new Error("Signed certificate required for " + file + " (" + s.verdict + ")");
      results.push(s);
    }
    if (sarifPath) fs3.writeFileSync(sarifPath, JSON.stringify({
      $schema: "https://json.schemastore.org/sarif-2.1.0.json",
      version: "2.1.0",
      runs: results.map((s) => toSarif(s.file, s))
    }, null, 2));
    if (json) {
      const display = results.map((s) => ({ ...view(s, full), ...extra.get(s) ?? {} }));
      console.log(JSON.stringify(multi ? {
        schema: "speedrunpapi.scan-batch.v2",
        version: VERSION,
        summary: { files: results.length, ...counts, wall_ms: performance.now() - started },
        results: display
      } : display[0], null, 2));
    } else {
      for (const s of results) {
        printHuman(s);
        const e = extra.get(s);
        if (e?.certificate_id) console.log("  cert     " + e.certificate_id + (e.signed ? " (Ed25519)" : ""));
        if (reportPath && s.report) console.log("  report   " + (multi ? path3.join(reportPath, s.id + ".report.json") : reportPath));
      }
      if (multi) console.log(`
scanned ${results.length}: ${counts.Certified} Certified / ${counts.Broken} Broken / ${counts.Unknown} Unknown; ${ms(performance.now() - started)} wall`);
    }
    process.exit(counts.Broken ? 2 : counts.Unknown ? 3 : 0);
  }
  usage();
  process.exit(1);
}
var hostedCommands = /* @__PURE__ */ new Set(["run", "quote", "solve", "optimize", "status", "result", "check"]);
if (process.argv[2] === "jobs") process.argv.splice(2, 1);
if (process.argv[2] === "verify-onnx") {
  const arguments2 = process.argv.slice(3);
  if (arguments2.length !== 2) {
    console.error("Usage: speedrunpapi verify-onnx <source.onnx> <artifacts-dir>");
    process.exitCode = 2;
  } else {
    Promise.all([import("node:child_process"), import("node:fs"), import("node:url")]).then(([child, fileSystem, url]) => {
      const locations = ["../verifiers/onnx/independent_plan.py", "./verifiers/onnx/independent_plan.py"];
      const verifier = locations.map((p) => url.fileURLToPath(new URL(p, import.meta.url))).find((p) => fileSystem.existsSync(p));
      if (!verifier) throw new Error("Independent ONNX checker is missing from this installation");
      const python = process.env.COLONY_PYTHON || process.env.PYTHON || "python3";
      const checked = child.spawnSync(
        python,
        [verifier, "--source", arguments2[0], "--artifacts", arguments2[1]],
        { stdio: "inherit" }
      );
      if (checked.error) throw new Error("Python checker failed: " + checked.error.message);
      process.exitCode = checked.status === null ? 1 : checked.status;
    }).catch((e) => {
      console.error(e.message);
      process.exitCode = 1;
    });
  }
} else if (hostedCommands.has(process.argv[2])) {
  import("./colony-jobs.mjs").catch((e) => {
    console.error(e);
    process.exitCode = 1;
  });
} else {
  main().catch((e) => {
    console.error(e);
    process.exitCode = 1;
  });
}
