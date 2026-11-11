#!/usr/bin/env python3
"""Independent verifier for Colony determinism reports (schema colony.determinism/1).

    python3 determinism_check.py <circuit.r1cs> <report.json>

A determinism report makes a claim about a rank-1 constraint system (iden3 binary
.r1cs, as written by circom).  With w the vector of wire values, w[0] = 1, every
constraint k demands  (A_k . w) * (B_k . w) = C_k . w  over the prime field F_p.
Wires 1..nPubOut are the outputs; the input wires follow them.

  Certified  any two satisfying assignments that agree on every input wire agree
             on every output wire ("output-determinism") or on every wire
             ("witness-uniqueness").  The report carries a derivation: a list of
             small inference steps.  This program replays it and accepts only if
             every single step follows from the constraints it cites.
  Broken     the report carries two full assignments.  This program accepts only
             if both satisfy every constraint, agree on every input wire and
             differ on an output wire.
  Unknown    no claim; nothing to verify.

This file shares no code with the engine that writes the reports.  It is written
to fail closed: a report that is malformed where it matters is rejected, never
guessed at.  Rejecting a valid report is a bug; accepting an invalid one must not
happen.

Everything a verdict rests on is recomputed from the R1CS bytes: which wires are
inputs, the derivation or the witness pair, whether every declared input has a
wire.  Nothing in a report can widen the set of wires taken as given: that set is
the constant wire and the input range of the R1CS, and a report that names extra
input wires (`input_alias_wires`) is rejected outright, because listing the
outputs there would let an empty derivation "certify" any circuit.

Output: one JSON object on stdout.
  ok                 the report was verified (or it claims nothing: verdict Unknown)
  verdict            what this program vouches for: "Certified" / "Broken" only when
                     that claim was verified, otherwise "Unknown"
  claim_verified     true exactly when a Certified or Broken claim was verified
  error              why verification failed, else null
  r1cs_sha256        "sha256:<hex>" of the .r1cs bytes that were checked
  steps              derivation steps replayed (nested steps included)
  outputs            number of output wires in the R1CS
  determined_outputs output wires the replayed derivation shows to be determined
  inputs_all_wired   every private input the R1CS header declares has a wire
                     (computed from the R1CS; false if the R1CS could not be read)
  relies_on_declared_provenance
                     true exactly when a Broken verdict was accepted only because
                     the report declares the R1CS was compiled without
                     simplification (see below)
  claimed_verdict    the verdict the report states (null if it states none)
  property           the property the report is about
  assumed_binary_inputs
                     input wires the report assumes to hold 0 or 1 (see below)
  input_layout       how the input range was found: "label-map" (read off the
                     wire-to-label section) or "header" (no such section)
Exit status: 0 when ok, 1 when verification failed, 2 on usage or I/O errors.

What a verified claim is conditional on
---------------------------------------
* assumed_binary_inputs.  A report may assume input wires to be 0 or 1.  The
  claim is then about the system extended by x * (x - 1) = 0 for each of them,
  and says nothing about callers that break the assumption.  Only input wires
  can be assumed.
* relies_on_declared_provenance.  circom drops a private input that occurs in no
  constraint from the witness but still counts it in the header; with
  simplification (--O1, --O2) it can also merge an input into another signal or
  substitute it by a combination of other wires.  In the second case two
  assignments of the R1CS can differ on that input without differing on any
  input wire, and are then no counterexample for the circuit.  The R1CS cannot
  tell the cases apart.  So when some declared private input has no wire, a
  Broken verdict is accepted only if the report declares `inputs.complete: true`
  (a statement by whoever produced the report that the R1CS was compiled at
  --O0, where an input without a wire is unused), and the output flags it.  That
  declaration comes from the report itself and cannot be checked here: a caller
  who cannot vouch for it must treat such a result as unverified.

Standard library only; Python 3.9+.
"""

from __future__ import annotations

import functools
import hashlib
import json
import struct
import sys

SCHEMA = "colony.determinism/1"
VERDICTS = ("Certified", "Broken", "Unknown")
PROPERTIES = ("output-determinism", "witness-uniqueness")

# Resource limits (the same orders of magnitude the report writer uses).
MAX_R1CS_BYTES = 1 << 30
MAX_WIRES = 1 << 26
MAX_CONSTRAINTS = 1 << 26
MAX_TERMS = 1 << 28
MAX_REPORT_BYTES = 1 << 30
# Case analysis nests a few levels at most; the bound keeps a hostile report
# from exhausting the Python stack.
MAX_SPLIT_DEPTH = 64
# Longest decimal string accepted for a scale or multiplier.
MAX_INT_CHARS = 2048


class R1CSError(Exception):
    """The .r1cs bytes are not a constraint system this program can reason about."""


class ReportError(Exception):
    """The report is malformed or its claim does not follow."""


# --------------------------------------------------------------------------- #
# Prime-field helpers
# --------------------------------------------------------------------------- #

_SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
                 61, 67, 71, 73, 79, 83, 89, 97)
# Below this bound the strong-probable-prime test to the bases 2..41 is a proof
# of primality (Sorenson and Webster, 2015).
_DETERMINISTIC_MILLER_RABIN_BOUND = 3317044064679887385961981


@functools.lru_cache(maxsize=64)
def is_prime(n: int) -> bool:
    """Primality of the modulus.

    Every rule below uses field facts: a nonzero element has an inverse, a
    product is zero only if a factor is, a quadratic has at most two roots.
    They are false modulo a composite (x * x = 0 has the roots 0, 3 and 6
    modulo 9), so a system over a composite modulus must be refused rather
    than reasoned about.

    The test is Miller-Rabin: exact for n below 3.3e24, and for larger n it
    adds 64 bases derived from n by a hash, so that whoever picks n cannot
    know the bases in advance.  A composite survives one such base with
    probability at most 1/4.
    """
    if n < 2:
        return False
    for q in _SMALL_PRIMES:
        if n % q == 0:
            return n == q
    d, s = n - 1, 0
    while d & 1 == 0:
        d >>= 1
        s += 1

    def strong_probable_prime(a: int) -> bool:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return True
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                return True
        return False

    for a in _SMALL_PRIMES:
        if not strong_probable_prime(a):
            return False
    if n < _DETERMINISTIC_MILLER_RABIN_BOUND:
        return True
    width = (n.bit_length() + 7) // 8 + 8
    seed = n.to_bytes(width, "little")
    for i in range(64):
        digest = hashlib.shake_256(seed + bytes([i])).digest(width)
        a = 2 + int.from_bytes(digest, "little") % (n - 3)
        if not strong_probable_prime(a):
            return False
    return True


def sqrt_mod(a: int, p: int):
    """A square root of a modulo the odd prime p, or None when a has none (Tonelli-Shanks).

    Callers re-check the result by substitution, so this function only needs
    to be right, not trusted.
    """
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) >> 1, p) != 1:
        return None
    if p & 3 == 3:
        return pow(a, (p + 1) >> 2, p)
    q, e = p - 1, 0
    while q & 1 == 0:
        q >>= 1
        e += 1
    z = 2
    while pow(z, (p - 1) >> 1, p) != p - 1:
        z += 1
    m, c, t, r = e, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) >> 1, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
            if i == m:
                return None  # unreachable for a prime modulus
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


# --------------------------------------------------------------------------- #
# R1CS reader
# --------------------------------------------------------------------------- #

class R1CS:
    """A parsed constraint system.

    A linear combination is a pair (wires, coefficients) of equal-length tuples
    with strictly increasing wire indices and coefficients in [1, p).  Wire 0
    is the constant one.  The input wires are [1 + n_pub_out, input_end).
    """

    __slots__ = ("prime", "field_bytes", "n_wires", "n_pub_out", "n_pub_in", "n_prv_in",
                 "n_prv_in_wires", "input_end", "input_layout", "inputs_all_wired",
                 "n_constraints", "A", "B", "C")


_EMPTY_LC = ((), ())


def parse_r1cs(data: bytes) -> R1CS:
    """Read an iden3 binary R1CS (version 1).

    The reader is exact about meaning and tolerant about encoding: duplicate
    wires inside one linear combination are summed, coefficients are reduced
    modulo the prime, zero terms are dropped.  Files with custom-gate sections
    are refused because their constraints are not rank-1 products.
    """
    total = len(data)
    if total > MAX_R1CS_BYTES:
        raise R1CSError("R1CS exceeds the size limit")
    if total < 12:
        raise R1CSError("Truncated R1CS")
    if data[0:4] != b"r1cs":
        raise R1CSError("Invalid R1CS magic")
    version, n_sections = struct.unpack_from("<II", data, 4)
    if version != 1:
        raise R1CSError("Unsupported R1CS version")
    if not 2 <= n_sections <= 64:
        raise R1CSError("Invalid R1CS section count")

    # Section table: (type, size) records, each followed by its payload.
    sections = {}
    pos = 12
    for _ in range(n_sections):
        if pos + 12 > total:
            raise R1CSError("Truncated R1CS")
        kind, size = struct.unpack_from("<IQ", data, pos)
        pos += 12
        if size > total - pos:
            raise R1CSError("Invalid R1CS section length")
        if kind in sections:
            raise R1CSError("Duplicate R1CS section")
        sections[kind] = (pos, size)
        pos += size
    if pos != total:
        raise R1CSError("Trailing bytes after R1CS sections")
    if 4 in sections or 5 in sections:
        raise R1CSError("R1CS custom gates are outside the rank-1 analysis scope")
    if 1 not in sections or 2 not in sections:
        raise R1CSError("Missing required R1CS section")

    # Header.
    h, h_size = sections[1]
    h_end = h + h_size
    if h + 4 > h_end:
        raise R1CSError("Truncated R1CS header")
    (field_bytes,) = struct.unpack_from("<I", data, h)
    h += 4
    if field_bytes < 8 or field_bytes > 128 or field_bytes % 8 != 0:
        raise R1CSError("Unsupported R1CS field size")
    if h + field_bytes + 28 > h_end:
        raise R1CSError("Truncated R1CS header")
    prime = int.from_bytes(data[h:h + field_bytes], "little")
    h += field_bytes
    n_wires, n_pub_out, n_pub_in, n_prv_in, n_labels, n_constraints = struct.unpack_from("<IIIIQI", data, h)
    h += 28
    if h != h_end:
        raise R1CSError("Unexpected R1CS header length")
    if prime < 3 or prime % 2 == 0:
        raise R1CSError("Unsupported R1CS modulus")
    if (n_wires < 1 or n_wires > MAX_WIRES or n_constraints > MAX_CONSTRAINTS
            or 1 + n_pub_out + n_pub_in > n_wires or n_labels > (1 << 53) - 1):
        raise R1CSError("Invalid R1CS dimensions")
    if not is_prime(prime):
        raise R1CSError("R1CS modulus is not prime; the inference rules are only sound over a field")

    # Which wires are private inputs.  circom orders wires as: one, outputs,
    # public inputs, the private inputs that still have a wire, internals.  It
    # drops a private input that occurs in no constraint but keeps counting it
    # in the header, so the header count cannot locate the input wires.  The
    # wire-to-label map can: main's outputs and inputs own the labels 1..nIO,
    # so a wire after the public inputs is a private input exactly when its
    # label is at most nIO.  The range found this way never extends past the
    # range the header itself declares.  Without the map there is only the
    # header to go by, and every declared private input is taken to be wired.
    n_io = n_pub_out + n_pub_in + n_prv_in
    first_prv = 1 + n_pub_out + n_pub_in
    if 3 in sections:
        l_start, l_size = sections[3]
        if l_size != n_wires * 8:
            raise R1CSError("Invalid R1CS wire-to-label map size")
        count = 0
        in_run = True
        wire = 0
        for (label,) in struct.iter_unpack("<Q", memoryview(data)[l_start:l_start + l_size]):
            if wire == 0:
                if label != 0:
                    raise R1CSError("Invalid R1CS wire-to-label map")
            elif wire < first_prv:
                if not 1 <= label <= n_io:
                    raise R1CSError("R1CS output/public-input wire has a non-I/O label")
            elif label <= n_io:
                if not in_run:
                    raise R1CSError("R1CS input wires are not contiguous")
                count += 1
            else:
                in_run = False
            wire += 1
        if count > n_prv_in:
            raise R1CSError("R1CS has more private-input wires than declared")
        n_prv_in_wires = count
        input_layout = "label-map"
    else:
        if first_prv + n_prv_in > n_wires:
            raise R1CSError("R1CS has no label map and its header exceeds the wire count")
        n_prv_in_wires = n_prv_in
        input_layout = "header"

    # Constraints: for each one three linear combinations A, B, C, each a
    # term count followed by (wire: u32, coefficient: field_bytes LE) terms.
    pos, c_size = sections[2]
    c_end = pos + c_size
    if n_constraints * 12 > c_size:   # three term counts per constraint, before anything is allocated
        raise R1CSError("Truncated R1CS constraint")
    term_bytes = 4 + field_bytes
    u32_at = struct.Struct("<I").unpack_from
    one_term = struct.Struct("<I%ds" % field_bytes)
    packed = {}          # term count -> Struct for a whole linear combination
    coefficient = {}     # raw bytes -> reduced int (most coefficients repeat)
    A = [_EMPTY_LC] * n_constraints
    B = [_EMPTY_LC] * n_constraints
    C = [_EMPTY_LC] * n_constraints
    n_terms = 0
    for k in range(n_constraints):
        for side in (A, B, C):
            if pos + 4 > c_end:
                raise R1CSError("Truncated R1CS constraint")
            n = u32_at(data, pos)[0]
            pos += 4
            if n == 0:
                continue
            if n * term_bytes > c_end - pos:
                raise R1CSError("Invalid R1CS linear-combination length")
            n_terms += n
            if n_terms > MAX_TERMS:
                raise R1CSError("R1CS exceeds the term limit")
            if n <= 64:
                layout = packed.get(n)
                if layout is None:
                    layout = packed[n] = struct.Struct("<" + ("I%ds" % field_bytes) * n)
                flat = layout.unpack_from(data, pos)
                wires, raws = flat[0::2], flat[1::2]
            else:
                pairs = list(one_term.iter_unpack(memoryview(data)[pos:pos + n * term_bytes]))
                wires = tuple(pair[0] for pair in pairs)
                raws = [pair[1] for pair in pairs]
            pos += n * term_bytes
            coefs = []
            canonical = True
            previous = -1
            for w, raw in zip(wires, raws):
                if w >= n_wires:
                    raise R1CSError("R1CS term references a wire outside the circuit")
                v = coefficient.get(raw)
                if v is None:
                    v = coefficient[raw] = int.from_bytes(raw, "little") % prime
                if w <= previous or v == 0:
                    canonical = False
                previous = w
                coefs.append(v)
            if canonical:
                side[k] = (wires, tuple(coefs))
            else:
                merged = {}
                for w, v in zip(wires, coefs):
                    merged[w] = (merged.get(w, 0) + v) % prime
                keep = sorted(w for w, v in merged.items() if v)
                side[k] = (tuple(keep), tuple(merged[w] for w in keep)) if keep else _EMPTY_LC
    if pos != c_end:
        raise R1CSError("Trailing bytes in R1CS constraint section")

    r = R1CS()
    r.prime = prime
    r.field_bytes = field_bytes
    r.n_wires = n_wires
    r.n_pub_out = n_pub_out
    r.n_pub_in = n_pub_in
    r.n_prv_in = n_prv_in
    r.n_prv_in_wires = n_prv_in_wires
    r.input_end = first_prv + n_prv_in_wires
    r.input_layout = input_layout
    r.inputs_all_wired = n_prv_in_wires == n_prv_in
    r.n_constraints = n_constraints
    r.A, r.B, r.C = A, B, C
    return r


def with_binary_assumptions(r: R1CS, wires) -> R1CS:
    """The system a report with assumptions is about: r plus x * (x - 1) = 0 per assumed wire.

    The added constraints come after the original ones, in increasing wire
    order, so derivation steps can cite them by index.  Only input wires may be
    assumed binary: an assumption narrows the set of assignments the claim
    quantifies over, which is a precondition a caller can meet for an input and
    for nothing else.
    """
    for w in wires:
        if type(w) is not int or w <= r.n_pub_out or w >= r.input_end:
            raise ReportError("assumption on a wire that is not an input wire: only input wires can be assumed binary")
    binary = sorted(set(wires))
    if not binary:
        return r
    out = R1CS()
    for name in R1CS.__slots__:
        setattr(out, name, getattr(r, name))
    p = r.prime
    out.A = r.A + [((w,), (1,)) for w in binary]
    out.B = r.B + [((0, w), (p - 1, 1)) for w in binary]
    out.C = r.C + [_EMPTY_LC for _ in binary]
    out.n_constraints = r.n_constraints + len(binary)
    return out


# --------------------------------------------------------------------------- #
# Derivation replay
# --------------------------------------------------------------------------- #

# What one constraint says about the undetermined wires under the current facts.
NONE, DEAD, QUAD, COND, ROW = "none", "dead", "quad", "cond", "row"
_NO_INFO = (NONE, None, None)
_CONTRADICTION = (DEAD, None, None)
_QUADRATIC = (QUAD, None, None)
_CONDITIONAL = (COND, None, None)


class _Case:
    """One level of case analysis: the facts that hold only inside the case."""

    __slots__ = ("det", "val", "form", "is_zero")

    def __init__(self, form, is_zero):
        self.det = set()        # wires determined inside this case
        self.val = {}           # wires with a known value inside this case
        self.form = form        # the linear form the case is about ...
        self.is_zero = is_zero  # ... and whether it is zero or nonzero here


class Replay:
    """Replays a derivation step by step.

    Throughout, "pair" means two satisfying assignments w, w' of the system
    that agree on every input wire, and d = w - w' is their difference.  The
    replay maintains two sets of facts:

      determined  wires x with d[x] = 0 for every pair.
      val         wires with a known constant value: w[x] = val[x] for every
                  satisfying assignment w.  Every valued wire is determined.

    Initially wire 0 (the constant one) is determined with value 1 and the
    input wires are determined by the definition of a pair.  Nothing else is
    taken as given, and nothing outside this class can add to it: the input
    range comes from the R1CS, never from a report.  Each step may add facts,
    and is accepted only if the new facts follow from the old ones and from the
    constraints the step cites.  So after any accepted prefix of a derivation,
    every wire marked determined really is equal in both members of every pair,
    which is the certified property once all outputs are marked.

    Inside a case of a `split` step the same invariants hold relative to the
    case: "every pair" / "every assignment" then range over the assignments in
    which the case's condition (a linear form being zero, or nonzero) holds.
    Case-local facts live on a stack and are discarded when the case ends.
    """

    def __init__(self, r: R1CS):
        self.r = r
        self.p = r.prime
        self.A, self.B, self.C = r.A, r.B, r.C
        self.n_wires = r.n_wires
        self.n_constraints = r.n_constraints
        self.det = bytearray(r.n_wires)
        self.det[0] = 1
        self.val = {0: 1}
        for w in range(1 + r.n_pub_out, r.input_end):
            self.det[w] = 1
        self.cases = []
        self.count = 0

    # ---- facts ---------------------------------------------------------- #

    def is_det(self, w: int) -> bool:
        for case in reversed(self.cases):
            if w in case.det:
                return True
        return self.det[w] == 1

    def value(self, w: int):
        for case in reversed(self.cases):
            v = case.val.get(w)
            if v is not None:
                return v
        return self.val.get(w)

    def _mark(self, w: int) -> None:
        if self.cases:
            self.cases[-1].det.add(w)
        else:
            self.det[w] = 1

    def _learn(self, w: int, v: int) -> None:
        if self.value(w) is not None:
            return
        if self.cases:
            self.cases[-1].val[w] = v
        else:
            self.val[w] = v

    def _constraint_ok(self, k) -> bool:
        # type(...) is int: a JSON true/false is a Python bool, and bool is an int subclass.
        return type(k) is int and 0 <= k < self.n_constraints

    def _wire_ok(self, w) -> bool:
        return type(w) is int and 0 < w < self.n_wires

    # ---- reading a constraint under the current facts ------------------- #

    def _view(self, lc):
        """Split L . w into its undetermined part, its known constant part, and the rest.

        Returns (open, known, symbolic): `open` maps each undetermined wire of
        L to its coefficient (None when there is none); `known` is the sum of
        coefficient * value over the valued wires, not reduced; `symbolic` says
        whether L also has a determined wire whose value is not a known constant.
        """
        wires, coefs = lc
        opened = None
        known = 0
        symbolic = False
        if self.cases:
            is_det, value = self.is_det, self.value
            for w, c in zip(wires, coefs):
                if is_det(w):
                    v = value(w)
                    if v is None:
                        symbolic = True
                    else:
                        known += c * v
                else:
                    if opened is None:
                        opened = {}
                    opened[w] = c
        else:
            det, val = self.det, self.val
            for w, c in zip(wires, coefs):
                if det[w]:
                    v = val.get(w)
                    if v is None:
                        symbolic = True
                    else:
                        known += c * v
                else:
                    if opened is None:
                        opened = {}
                    opened[w] = c
        return opened, known, symbolic

    def _normal(self, lc):
        """Canonical name of a determined linear form under the current values.

        Substituting the known values leaves  sum c_i x_i + c0  over the wires
        without a value; dividing by the first coefficient gives a key that two
        forms share exactly when one is a nonzero constant multiple of the
        other, so that one is zero iff the other is.  None when nothing but a
        constant is left.
        """
        p = self.p
        terms = []
        c0 = 0
        for w, c in zip(*lc):
            v = self.value(w)
            if v is None:
                terms.append((w, c))
            else:
                c0 += c * v
        if not terms:
            return None
        scale = pow(terms[0][1], -1, p)
        return tuple((w, c * scale % p) for w, c in terms), c0 * scale % p

    def _fact(self, lc):
        """True / False when an enclosing case says this determined form is zero / nonzero, else None."""
        key = self._normal(lc)
        if key is None:
            return None
        for case in reversed(self.cases):
            if self._normal(case.form) == key:
                return case.is_zero
        return None

    def _reduce(self, k: int):
        """What constraint k says about the undetermined wires: (kind, row, rhs).

        ROW   sum(row[x] * x) = rhs for every satisfying assignment when rhs is
              a number; when rhs is None the right-hand side is some quantity
              that is equal in both members of a pair, and the row then only
              says  sum(row[x] * d[x]) = 0.  Either way the row constrains d.
        DEAD  the constraint reads 0 = (nonzero constant): no assignment
              satisfies the system under the current facts.
        NONE, QUAD, COND  nothing usable: no information, a product of two
              undetermined forms, or a determined multiplier that is neither a
              known constant nor covered by a case fact.
        """
        p = self.p
        a_open, a_known, a_sym = self._view(self.A[k])
        b_open, b_known, b_sym = self._view(self.B[k])
        c_open, c_known, c_sym = self._view(self.C[k])
        if not a_open and not b_open:
            # A and B have no undetermined wire, so A*B is equal in both members
            # of a pair, hence so is C: the undetermined part of C has d-sum 0.
            # If everything else is a known constant, that part equals A*B - C_known.
            rhs = None if (a_sym or b_sym or c_sym) else (a_known * b_known - c_known) % p
            if not c_open:
                return _CONTRADICTION if rhs else _NO_INFO
            return ROW, c_open, rhs
        if a_open and b_open:
            return _QUADRATIC
        # Exactly one multiplicand is determined: M.  N is the other one.
        if not a_open:
            m_known, m_sym, m_lc = a_known, a_sym, self.A[k]
            n_open, n_known, n_sym = b_open, b_known, b_sym
        else:
            m_known, m_sym, m_lc = b_known, b_sym, self.B[k]
            n_open, n_known, n_sym = a_open, a_known, a_sym
        if m_sym:
            fact = self._fact(m_lc)
            if fact is None:
                return _CONDITIONAL
            if fact is False:
                # M is nonzero and equal in both members of a pair.  If C has no
                # undetermined wire, C is equal in both too, so M * (N - N') = 0
                # and N's undetermined part has d-sum 0.  (With undetermined
                # wires in C the relation is not linear with known coefficients.)
                if c_open:
                    return _NO_INFO
                return ROW, n_open, None
            m = 0
        else:
            m = m_known % p
        if m == 0:
            # 0 * N = C: the undetermined part of C equals minus its known part.
            if not c_open:
                if c_sym:
                    return _NO_INFO
                return _CONTRADICTION if c_known % p else _NO_INFO
            return ROW, c_open, None if c_sym else -c_known % p
        # M is the known nonzero constant m:  m * N = C  is linear.
        row = {w: c * m % p for w, c in n_open.items()}
        if c_open:
            for w, c in c_open.items():
                merged = (row.get(w, 0) - c) % p
                if merged:
                    row[w] = merged
                else:
                    row.pop(w, None)
        rhs = None if (n_sym or c_sym) else (c_known - m * n_known) % p
        if not row:
            return _CONTRADICTION if rhs else _NO_INFO
        return ROW, row, rhs

    def _roots(self, k: int, x: int):
        """All values wire x can take according to constraint k alone.

        Applies when constraint k mentions no wire other than x (and the
        constant): then it is q2 x^2 + q1 x + q0 = 0, a fact about x that holds
        in every satisfying assignment whatever the case.  Returns the tuple of
        its roots, or None when the constraint mentions another wire or does
        not restrict x.  Over a field a nonzero polynomial of degree at most
        two has at most two roots, so the tuple is complete.
        """
        p = self.p
        parts = []
        for lc in (self.A[k], self.B[k], self.C[k]):
            c1 = c0 = 0
            for w, c in zip(*lc):
                if w == 0:
                    c0 = c
                elif w == x:
                    c1 = c
                else:
                    return None
            parts.append((c1, c0))
        (a1, a0), (b1, b0), (c1, c0) = parts
        q2 = a1 * b1 % p
        q1 = (a1 * b0 + a0 * b1 - c1) % p
        q0 = (a0 * b0 - c0) % p
        if q2 == 0:
            if q1 == 0:
                return None  # 0 = q0: says nothing about x (or is contradictory)
            return ((-q0 * pow(q1, -1, p)) % p,)
        if q0 == 0:
            # x * (q2 x + q1) = 0
            if q1 == 0:
                return (0,)
            roots = (0, (-q1 * pow(q2, -1, p)) % p)
        else:
            half = pow(2 * q2, -1, p)
            disc = (q1 * q1 - 4 * q2 * q0) % p
            if disc == 0:
                return ((-q1 * half) % p,)
            s = sqrt_mod(disc, p)
            if s is None:
                return ()
            roots = ((-q1 + s) * half % p, (-q1 - s) * half % p)
        # Two distinct values that both satisfy a quadratic are all of its roots.
        if roots[0] == roots[1]:
            return None
        for v in roots:
            if (q2 * v * v + q1 * v + q0) % p != 0:
                return None
        return roots

    def _super_increasing(self, weights, scale: int) -> bool:
        """A sufficient test that sum(weights_i * e_i) = 0 mod p with e_i in {-1, 0, 1} forces e = 0.

        Let h_i be the representative of scale * weights_i of least absolute
        value.  If the |h_i|, sorted, each exceed the sum of all smaller ones,
        and their total is below p, then for e != 0 the integer sum(h_i e_i) is
        nonzero (the largest index with e_i != 0 dominates the rest) and of
        absolute value below p, so it is not a multiple of p; and scale is
        invertible, so sum(weights_i e_i) is not zero mod p either.  True means
        proven; False only means this scale does not show it.

        (Each |h_i| is at most (p - 1) / 2, so a super-increasing sequence
        already has a total below twice its largest term, hence below p; the
        explicit bound is kept because the argument above leans on it.)
        """
        p = self.p
        if scale % p == 0:
            return False
        magnitudes = []
        for g in weights:
            v = g * scale % p
            magnitudes.append(min(v, p - v))
        magnitudes.sort()
        total = 0
        for v in magnitudes:
            if v <= total:  # also refuses a zero weight
                return False
            total += v
        return total < p

    # ---- steps ---------------------------------------------------------- #

    def step(self, s):
        """Check one step.  Returns None if it is accepted, else the reason it is not.

        An accepted step records its conclusion.  A rejected step records
        nothing (only the step counter moves).
        """
        self.count += 1
        if type(s) is not dict:
            return "malformed step"
        t = s.get("t")
        if t == "lin":
            return self._lin(s)
        if t == "fix":
            return self._fix(s)
        if t == "bits":
            return self._bits(s)
        if t == "gauss":
            return self._gauss(s)
        if t == "onehot":
            return self._onehot(s)
        if t == "split":
            return self._split(s)
        return "unknown step type"

    def _lin(self, s):
        """lin: constraint k reduces to a linear row with a single undetermined wire x.

        Sound because the row says c * d[x] = 0 with c != 0, so d[x] = 0.  When
        the right-hand side is a known number, c * x = rhs gives x's value.
        """
        k, x = s.get("k"), s.get("x")
        if not self._constraint_ok(k) or not self._wire_ok(x):
            return "lin: bad index"
        kind, row, rhs = self._reduce(k)
        if kind != ROW or len(row) != 1 or x not in row:
            return "lin: constraint %d does not isolate wire %d" % (k, x)
        self._mark(x)
        if rhs is not None:
            self._learn(x, rhs * pow(row[x], -1, self.p) % self.p)
        return None

    def _fix(self, s):
        """fix: constraint k mentions only wire x and has exactly one root.

        Sound because every satisfying assignment gives x that root: x has a
        known value, and in particular is equal in both members of a pair.
        """
        k, x = s.get("k"), s.get("x")
        if not self._constraint_ok(k) or not self._wire_ok(x):
            return "fix: bad index"
        roots = self._roots(k, x)
        if roots is None or len(roots) != 1:
            return "fix: constraint %d does not pin wire %d to one value" % (k, x)
        self._mark(x)
        self._learn(x, roots[0])
        return None

    def _bits(self, s):
        """bits: a linear row whose undetermined wires xs are all two-valued, with injective weights.

        Constraint d[i] mentions only xs[i] and has exactly two roots r0, r1,
        so in a pair d[xs[i]] = e_i * (r1 - r0) with e_i in {-1, 0, 1}.  The
        row of constraint k has exactly the wires xs, so it says
        sum(coef_i * (r1 - r0)_i * e_i) = 0.  When those weights pass the
        super-increasing test the only solution is e = 0: every xs[i] is equal
        in both members of the pair.  The scale `s` is a hint; any nonzero
        scale that makes the test pass proves the same thing.
        """
        k, xs, d = s.get("k"), s.get("xs"), s.get("d")
        if (not self._constraint_ok(k) or type(xs) is not list or type(d) is not list
                or len(xs) != len(d) or len(xs) < 2):
            return "bits: malformed"
        kind, row, _rhs = self._reduce(k)
        if kind != ROW or len(row) != len(xs):
            return "bits: constraint %d is not a matching linear row" % k
        scale = _parse_integer(s.get("s"))
        if scale is None:
            return "bits: bad scale"
        p = self.p
        weights = []
        seen = set()
        for x, dk in zip(xs, d):
            if not self._wire_ok(x) or not self._constraint_ok(dk) or x in seen:
                return "bits: bad index"
            seen.add(x)
            coef = row.get(x)
            if coef is None:
                return "bits: wire %d is not open in constraint %d" % (x, k)
            roots = self._roots(dk, x)
            if roots is None or len(roots) != 2:
                return "bits: constraint %d does not make wire %d two-valued" % (dk, x)
            weights.append(coef * (roots[1] - roots[0]) % p)
        # len(row) == len(xs), the xs are distinct and each is in the row: the
        # row has no undetermined wire outside xs.
        if not self._super_increasing(weights, scale):
            return "bits: weights of constraint %d are not injective under the given scale" % k
        for x in xs:
            self._mark(x)
        return None

    def _gauss(self, s):
        """gauss: a linear combination of rows leaves the single undetermined wire x.

        Every row says sum(row[w] * d[w]) = 0, hence so does any combination of
        rows; if the combination's only nonzero coefficient is on x, d[x] = 0.
        """
        x, rows, mult = s.get("x"), s.get("rows"), s.get("mult")
        if (not self._wire_ok(x) or type(rows) is not list or type(mult) is not list
                or len(rows) != len(mult) or not rows):
            return "gauss: malformed"
        p = self.p
        acc = {}
        for rk, factor_text in zip(rows, mult):
            if not self._constraint_ok(rk):
                return "gauss: bad constraint index"
            kind, row, _rhs = self._reduce(rk)
            if kind != ROW:
                return "gauss: constraint %d is not a linear row" % rk
            factor = _parse_integer(factor_text)
            if factor is None:
                return "gauss: bad multiplier"
            factor %= p
            for w, c in row.items():
                acc[w] = (acc.get(w, 0) + c * factor) % p
        for w, c in acc.items():
            if c and w != x:
                return "gauss: combination leaves wire %d" % w
        if not acc.get(x):
            return "gauss: combination does not isolate wire %d" % x
        self._mark(x)
        return None

    def _onehot(self, s):
        """onehot: selectors s_i with s_i * (L - c_i) = C_i over one determined form L, tied by a linear row.

        Each member [constraint, side] names a constraint whose multiplicand on
        `side` has no undetermined wire and is a(L + c) for one linear form L
        shared by all members (same wires, same normalised coefficients) and a
        constant c that differs from member to member; whose other multiplicand
        has exactly one undetermined wire x; and whose C has none.  L has the
        same value in both members of a pair, and since the constants are
        pairwise distinct at most one of the multiplicands L + c is zero there.
        For every other member the multiplicand is the same nonzero number in
        both assignments and so is C, hence the other multiplicand is equal in
        both and d[x] = 0.  That leaves at most one member wire with d != 0.
        The row of constraint k has exactly the member wires as undetermined
        wires and says sum(row[x] * d[x]) = 0, so the last one has d = 0 too.
        Nothing is learned about values.
        """
        k, members = s.get("k"), s.get("m")
        if not self._constraint_ok(k) or type(members) is not list or len(members) < 2:
            return "onehot: malformed"
        kind, row, _rhs = self._reduce(k)
        if kind != ROW or len(row) != len(members):
            return "onehot: constraint %d is not a linear row over the family" % k
        shared_form = None
        constants = set()
        wires = set()
        for entry in members:
            if type(entry) is not list or len(entry) != 2:
                return "onehot: malformed member"
            mk, side = entry
            if not self._constraint_ok(mk) or type(side) is not str or side not in ("A", "B"):
                return "onehot: bad member"
            multiplicand, other = (self.A[mk], self.B[mk]) if side == "A" else (self.B[mk], self.A[mk])
            if self._view(multiplicand)[0]:
                return "onehot: multiplicand of constraint %d is not determined" % mk
            other_open = self._view(other)[0]
            if other_open is None or len(other_open) != 1 or self._view(self.C[mk])[0]:
                return "onehot: constraint %d does not isolate one wire when its multiplicand is nonzero" % mk
            key = self._normal(multiplicand)
            if key is None:
                return "onehot: multiplicand of constraint %d is constant here" % mk
            form, constant = key
            if shared_form is None:
                shared_form = form
            elif form != shared_form:
                return "onehot: members do not share one form"
            if constant in constants:
                return "onehot: two members have the same constant"
            constants.add(constant)
            (x,) = other_open
            if x in wires:
                return "onehot: a wire has two members"
            if x not in row:
                return "onehot: wire %d is not in the row" % x
            wires.add(x)
        # len(row) == len(members), the member wires are distinct and each is
        # in the row: the row has no undetermined wire outside the family.
        for x in wires:
            self._mark(x)
        return None

    def _split(self, s):
        """split: case analysis on a determined linear form L being zero or nonzero.

        L is side A or B of constraint k and every wire of L is determined, so
        L has the same value in both members of a pair: the two members are
        always in the same case.  Each case is replayed with the extra fact
        "L = 0" (or "L != 0").  A case may end in a contradiction (`dead`: some
        constraint cannot hold there, so no pair lives in it); otherwise it
        must determine every wire in xs.  If every pair lies in a case where
        the xs are determined, the xs are determined.  Facts learned inside a
        case are dropped when it ends; only the xs are kept.
        """
        k, side, xs = s.get("k"), s.get("side"), s.get("xs")
        if (not self._constraint_ok(k) or type(side) is not str or side not in ("A", "B")
                or type(xs) is not list or not xs):
            return "split: malformed"
        if len(self.cases) >= MAX_SPLIT_DEPTH:
            return "split: case analysis nested too deeply"
        form = (self.A if side == "A" else self.B)[k]
        for w in form[0]:
            if not self.is_det(w):
                return "split: form of constraint %d uses undetermined wire %d" % (k, w)
        if self._normal(form) is None:
            return "split: form of constraint %d is constant here" % k
        for x in xs:
            if not self._wire_ok(x):
                return "split: bad wire"
        err, zero_dead = self._run_case(s.get("zero"), form, True, xs)
        if err:
            return err
        err, nonzero_dead = self._run_case(s.get("nonzero"), form, False, xs)
        if err:
            return err
        if zero_dead and nonzero_dead:
            # Then no assignment satisfies the current facts at all.  Nothing
            # false would follow, but a derivation has no business being here.
            return "split: both cases contradictory"
        for x in xs:
            self._mark(x)
        return None

    def enter_case(self, form, is_zero: bool) -> None:
        """Open a case in which the form is zero (or nonzero).

        The caller must have checked that every wire of the form is determined
        and that the form is not constant under the current values (_split does).
        """
        case = _Case(form, is_zero)
        self.cases.append(case)
        if is_zero:
            # If all wires of L but one have known values, L = 0 reads
            # c * x + c0 = 0 and gives the remaining wire its value.
            p = self.p
            terms = []
            c0 = 0
            for w, c in zip(*form):
                v = self.value(w)
                if v is None:
                    terms.append((w, c))
                else:
                    c0 += c * v
            if len(terms) == 1:
                case.val[terms[0][0]] = -c0 * pow(terms[0][1], -1, p) % p

    def leave_case(self) -> None:
        self.cases.pop()

    def _run_case(self, branch, form, is_zero: bool, xs):
        """Replay one branch of a split.  Returns (error or None, the case is contradictory)."""
        if type(branch) is not dict or type(branch.get("steps")) is not list:
            return "split: malformed branch", False
        name = "zero" if is_zero else "nonzero"
        self.enter_case(form, is_zero)
        try:
            for sub in branch["steps"]:
                err = self.step(sub)
                if err:
                    return name + " case: " + err, False
            if "dead" in branch:
                dead = branch["dead"]
                if not self._constraint_ok(dead) or self._reduce(dead)[0] != DEAD:
                    return "split: the cited constraint is not contradictory in the %s case" % name, False
                return None, True
            for x in xs:
                if not self.is_det(x):
                    return "split: wire %d is not determined in the %s case" % (x, name), False
            return None, False
        finally:
            self.leave_case()


def _parse_integer(text):
    """A decimal integer written as a JSON string (optional leading minus), else None."""
    if type(text) is not str or not 0 < len(text) <= MAX_INT_CHARS:
        return None
    digits = text[1:] if text[0] == "-" else text
    if not digits or not digits.isascii() or not digits.isdigit():
        return None
    return int(text)


def replay_derivation(r: R1CS, steps):
    """Replay a whole derivation.  Returns (error or None, the Replay with its final facts)."""
    replay = Replay(r)
    if type(steps) is not list:
        return "derivation is not a list of steps", replay
    for s in steps:
        err = replay.step(s)
        if err:
            return "step %d: %s" % (replay.count, err), replay
    return None, replay


# --------------------------------------------------------------------------- #
# Counterexample check
# --------------------------------------------------------------------------- #

def _evaluate(lc, w) -> int:
    total = 0
    for wire, c in zip(*lc):
        total += c * w[wire]
    return total


def first_violation(r: R1CS, w) -> int:
    """Index of the first constraint the full assignment w violates, or -1."""
    p = r.prime
    A, B, C = r.A, r.B, r.C
    for k in range(r.n_constraints):
        if (_evaluate(A[k], w) * _evaluate(B[k], w) - _evaluate(C[k], w)) % p:
            return k
    return -1


def check_counterexample(r: R1CS, a, b):
    """Why (a, b) is not a counterexample to output determinism, or None when it is one.

    A counterexample is two full assignments that both satisfy the system
    (including the constant wire being one), agree on every input wire and
    differ on an output wire.  Whether the input wires are all of the
    circuit's inputs is the caller's concern (see verify_report).
    """
    p = r.prime
    for w in (a, b):
        if len(w) != r.n_wires:
            return "assignment length differs from wire count"
        for v in w:
            if type(v) is not int or not 0 <= v < p:
                return "assignment value outside the field"
    for name, w in (("first", a), ("second", b)):
        if w[0] != 1:
            return "%s assignment does not set the constant wire to one" % name
        k = first_violation(r, w)
        if k >= 0:
            return "%s assignment violates constraint %d" % (name, k)
    for w in range(1 + r.n_pub_out, r.input_end):
        if a[w] != b[w]:
            return "assignments differ on input wire %d" % w
    for w in range(1, r.n_pub_out + 1):
        if a[w] != b[w]:
            return None
    return "assignments agree on every output"


# --------------------------------------------------------------------------- #
# Report verification
# --------------------------------------------------------------------------- #

def _parse_witness(values, p: int):
    """Decode a witness: a list of canonical decimal strings, each a field element."""
    width = len(str(p))
    out = []
    for text in values:
        if type(text) is not str or not 0 < len(text) <= width or not text.isascii() or not text.isdigit():
            raise ReportError("malformed witness values")
        out.append(int(text))
    return out


def _digest_matches(stated, digest_hex: str) -> bool:
    if type(stated) is not str:
        return False
    stated = stated.strip().lower()
    if stated.startswith("sha256:"):
        stated = stated[len("sha256:"):]
    return stated == digest_hex


def verify_report(r1cs_bytes: bytes, report: dict) -> dict:
    """Verify `report` (parsed JSON) against the R1CS it is about.

    Returns the result object described in the module docstring.  Never raises:
    whatever goes wrong, the answer is a rejection with a reason.
    """
    result = {
        "ok": False, "verdict": "Unknown", "claim_verified": False, "error": None,
        "r1cs_sha256": None, "steps": 0, "outputs": 0, "determined_outputs": 0,
        "inputs_all_wired": False, "relies_on_declared_provenance": False,
        "claimed_verdict": None, "property": None, "assumed_binary_inputs": [], "input_layout": None,
    }
    try:
        if type(r1cs_bytes) is bytes:
            data = r1cs_bytes
        elif isinstance(r1cs_bytes, (bytearray, memoryview)):
            data = bytes(r1cs_bytes)
        else:
            raise R1CSError("the R1CS must be given as bytes")
        result["r1cs_sha256"] = "sha256:" + hashlib.sha256(data).hexdigest()
        verdict = _judge(data, report, result)
        result["ok"] = True
        result["verdict"] = verdict
        result["claim_verified"] = verdict != "Unknown"
    except (ReportError, R1CSError) as e:
        result["error"] = str(e)
    except Exception as e:  # fail closed: an unexpected condition is a rejection, never a traceback
        result["error"] = "internal error: %s: %s" % (type(e).__name__, e)
    return result


def _judge(data: bytes, report, result: dict) -> str:
    """Return the verified verdict, or raise ReportError / R1CSError."""
    # The R1CS is read first: what it says about itself does not depend on the report.
    base = parse_r1cs(data)
    result["outputs"] = base.n_pub_out
    result["inputs_all_wired"] = base.inputs_all_wired
    result["input_layout"] = base.input_layout

    if type(report) is not dict:
        raise ReportError("report is not a JSON object")
    if report.get("schema") != SCHEMA:
        raise ReportError("unsupported report schema")
    verdict = report.get("verdict")
    if type(verdict) is not str or verdict not in VERDICTS:
        raise ReportError("report states no recognised verdict")
    result["claimed_verdict"] = verdict
    prop = report.get("property")
    if type(prop) is not str or prop not in PROPERTIES:
        raise ReportError("report states no recognised property")
    result["property"] = prop

    # The wires taken as given are the constant wire and the input range of the
    # R1CS, nothing else.  A report that nominates further "input" wires is
    # refused whatever its verdict: if such a list were honoured, naming the
    # output wires in it would make an empty derivation a proof.
    alias = report.get("input_alias_wires")
    if alias is not None and not (type(alias) is list and not alias):
        raise ReportError("a report may not declare extra input wires (input_alias_wires)")

    # A report may name the file it is about.  If it does, it must be this file.
    digest_hex = result["r1cs_sha256"][len("sha256:"):]
    stated = []
    if "r1cs_sha256" in report:
        stated.append(report["r1cs_sha256"])
    if "binding" in report:
        binding = report["binding"]
        if type(binding) is not dict:
            raise ReportError("report binding is malformed")
        if "r1cs_sha256" in binding:
            stated.append(binding["r1cs_sha256"])
    for value in stated:
        if not _digest_matches(value, digest_hex):
            raise ReportError("report is bound to a different R1CS (r1cs_sha256 does not match this file)")

    # Declared preconditions: input wires assumed to hold 0 or 1.
    binary = []
    assumptions = report.get("assumptions")
    if assumptions is not None:
        if type(assumptions) is not dict:
            raise ReportError("report assumptions are malformed")
        entries = assumptions.get("binary_inputs")
        if entries is not None:
            if type(entries) is not list:
                raise ReportError("report assumptions are malformed")
            for entry in entries:
                if type(entry) is not dict:
                    raise ReportError("report assumptions are malformed")
                binary.append(entry.get("wire"))
    r = with_binary_assumptions(base, binary)
    result["assumed_binary_inputs"] = sorted(set(binary))

    if verdict == "Unknown":
        return "Unknown"

    if verdict == "Certified":
        proof = report.get("proof")
        if type(proof) is not dict or type(proof.get("steps")) is not list:
            raise ReportError("report carries no derivation")
        if prop == "output-determinism" and r.n_pub_out == 0:
            raise ReportError("circuit has no outputs")
        err, replay = replay_derivation(r, proof["steps"])
        det = replay.det
        result["steps"] = replay.count
        result["determined_outputs"] = sum(det[1:1 + r.n_pub_out])
        if err is not None:
            raise ReportError(err)
        if prop == "witness-uniqueness":
            w = det.find(0)
            if w >= 0:
                raise ReportError("wire %d is not determined by the derivation" % w)
        else:
            w = det.find(0, 1, 1 + r.n_pub_out)
            if w >= 0:
                raise ReportError("output wire %d is not determined by the derivation" % w)
        return "Certified"

    # Broken.
    cex = report.get("counterexample")
    if type(cex) is not dict or type(cex.get("witness_a")) is not list or type(cex.get("witness_b")) is not list:
        raise ReportError("report carries no counterexample")
    if not base.inputs_all_wired:
        # Some declared private input has no wire.  It may be unused, or the
        # compiler may have merged it into another signal or substituted it by
        # a combination of other wires; then two assignments of this system can
        # differ on that input without differing on any input wire, and are no
        # counterexample for the circuit.  The R1CS cannot tell which.  The
        # pair is accepted only on the report's declaration that the R1CS was
        # compiled without simplification, and the result says so.
        inputs = report.get("inputs")
        if type(inputs) is not dict or inputs.get("complete") is not True:
            raise ReportError(
                "the R1CS has a wire for only %d of its %d declared private inputs and the report does not declare"
                " inputs.complete, so a pair of assignments is not a counterexample for the circuit"
                % (base.n_prv_in_wires, base.n_prv_in))
    if len(cex["witness_a"]) != r.n_wires or len(cex["witness_b"]) != r.n_wires:
        raise ReportError("assignment length differs from wire count")
    a = _parse_witness(cex["witness_a"], r.prime)
    b = _parse_witness(cex["witness_b"], r.prime)
    err = check_counterexample(r, a, b)
    if err is not None:
        raise ReportError(err)
    result["relies_on_declared_provenance"] = not base.inputs_all_wired
    return "Broken"


# --------------------------------------------------------------------------- #
# Command line
# --------------------------------------------------------------------------- #

def _reject_constant(name):
    raise ValueError("non-standard JSON constant " + name)


def _unique_keys(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError("duplicate key %r in a JSON object" % key[:40])
        out[key] = value
    return out


def load_report(raw: bytes):
    """Parse report JSON strictly: UTF-8, no NaN/Infinity, no duplicate object keys.

    Duplicate keys are refused because JSON readers disagree on which one wins,
    and a report must mean the same thing to every reader.
    """
    if len(raw) > MAX_REPORT_BYTES:
        raise ReportError("report exceeds the size limit")
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=_unique_keys, parse_constant=_reject_constant)
    except (ValueError, RecursionError) as e:
        raise ReportError("report is not valid JSON: %s" % (str(e)[:200] or type(e).__name__))


USAGE = "usage: determinism_check.py <circuit.r1cs> <report.json>"


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else list(argv)
    if len(argv) == 1 and argv[0] in ("-h", "--help"):
        sys.stdout.write(__doc__.strip() + "\n")
        return 0

    def give_up(message: str) -> int:
        failed = verify_report(b"", None)
        failed["r1cs_sha256"] = None
        failed["error"] = message
        sys.stdout.write(json.dumps(failed) + "\n")
        sys.stderr.write(message + "\n")
        return 2

    if len(argv) != 2 or any(arg.startswith("-") for arg in argv):
        return give_up(USAGE)
    try:
        with open(argv[0], "rb") as f:
            r1cs_bytes = f.read()
        with open(argv[1], "rb") as f:
            report_bytes = f.read()
    except OSError as e:
        return give_up("cannot read input: %s" % e)

    try:
        report = load_report(report_bytes)
    except ReportError as e:
        result = verify_report(r1cs_bytes, None)
        result["error"] = str(e)
    else:
        result = verify_report(r1cs_bytes, report)
    sys.stdout.write(json.dumps(result) + "\n")
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
