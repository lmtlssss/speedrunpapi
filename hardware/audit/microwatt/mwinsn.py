# The floating-point instructions of Microwatt's FPU: their encodings, and the decode attributes the core
# passes to the unit, read from the core's own decode1.vhdl (set MICROWATT to the checkout's directory).
import os
import re

DECODE = os.path.join(os.environ.get("MICROWATT", "microwatt"), "decode1.vhdl")
RNN = ["nearest", "zero", "+inf", "-inf"]
KIND = {"OP_FP_ARITH": 0, "OP_FP_CMP": 1, "OP_FP_MISC": 2, "OP_FP_MOVE": 3}

# name: (form, primary opcode, extended opcode)
INSN = {}
for base, xo in (("fadd", 21), ("fsub", 20), ("fmul", 25), ("fdiv", 18), ("fsqrt", 22), ("fmadd", 29),
                 ("fmsub", 28), ("fnmadd", 31), ("fnmsub", 30)):
    INSN[base] = ("A", 63, xo)
    INSN[base + "s"] = ("A", 59, xo)
INSN.update({
    "frsp": ("X", 63, 12),
    "fctid": ("X", 63, 814), "fctidz": ("X", 63, 815), "fctidu": ("X", 63, 942), "fctiduz": ("X", 63, 943),
    "fctiw": ("X", 63, 14), "fctiwz": ("X", 63, 15), "fctiwu": ("X", 63, 142), "fctiwuz": ("X", 63, 143),
    "fcfid": ("X", 63, 846), "fcfidu": ("X", 63, 974), "fcfids": ("X", 59, 846), "fcfidus": ("X", 59, 974),
    "frin": ("X", 63, 392), "friz": ("X", 63, 424), "frip": ("X", 63, 456), "frim": ("X", 63, 488),
    "fcmpu": ("X", 63, 0), "fcmpo": ("X", 63, 32),
    "fmr": ("X", 63, 72), "fneg": ("X", 63, 40), "fabs": ("X", 63, 264), "fnabs": ("X", 63, 136),
    "fcpsgn": ("X", 63, 8), "fsel": ("A", 63, 23),
})
# mtfsf with L = 1 writes the whole FPSCR from FRB; mffs reads it
MTFSF = (63 << 26) | (1 << 25) | (3 << 11) | (711 << 1)
MFFS = (63 << 26) | (1 << 21) | (583 << 1)


def decode_rows():
    rows = {}
    text = open(DECODE, encoding="utf-8", errors="replace").read()
    for name, body in re.findall(r"INSN_(\w+)\s*=>\s*\(([^)]*)\)", text):
        f = [x.strip().strip("'") for x in body.split(",")]
        if len(f) < 27 or f[0] != "FPU":
            continue
        rows[name] = dict(kind=KIND.get(f[2]), a=f[3] == "FRA", b=f[4] == "FRB", c=f[6] == "FRC",
                          out_cr=int(f[11]), single=int(f[21]), signed=int(f[22]))
    return rows


ROWS = decode_rows()


def encode(name):
    """-> (K, instruction word, FLAGS) as tb_mw.vhd reads them"""
    form, op, xo = INSN[name][:3]
    d = ROWS[name]
    # the target is FPR 1, or CR field 1 for a compare, whose two bits below the field are reserved
    word = (op << 26) | ((1 << 23) if d["kind"] == 1 else (1 << 21)) | ((2 << 16) if d["a"] else 0) \
        | ((3 << 11) if d["b"] else 0) | (xo << 1)
    if form == "A" and d["c"]:
        word |= 4 << 6
    flags = (d["single"] << 7) | (d["signed"] << 6) | (d["a"] << 5) | (d["b"] << 4) | (d["c"] << 3) | (d["out_cr"] << 2)
    return d["kind"], word, flags
