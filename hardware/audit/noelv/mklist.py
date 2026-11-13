# Prints "library path" lines, in analysis order, for the GRLIB sources the NOEL-V core needs.
# It reads the release's own manifests (vhdlsyn.txt, vhdlsim.txt) as data and runs nothing of its build system.
# usage: python3 mklist.py GRLIB/lib [PATCHED_NANOFPUNV.vhd]
import os
import sys

ROOT = sys.argv[1]
NANOFPU = sys.argv[2] if len(sys.argv) > 2 else None

# (library, directory, manifests, files kept from them; None keeps all)
SETS = [
    ("grlib", "grlib/stdlib", ["vhdlsyn.txt", "vhdlsim.txt"], None),
    ("grlib", "grlib/util", ["vhdlsim.txt"], None),
    ("grlib", "grlib/sparc", ["vhdlsyn.txt"], None),
    ("grlib", "grlib/riscv", ["vhdlsyn.txt", "vhdlsim.txt"], None),
    ("grlib", "grlib/modgen", ["vhdlsyn.txt"], None),
    ("grlib", "grlib/amba", ["vhdlsyn.txt"], ["amba.vhd", "devices.vhd"]),
    ("grlib", "grlib/dftlib", ["vhdlsyn.txt"], None),
    ("techmap", "techmap/gencomp", ["vhdlsyn.txt"], None),
    ("techmap", "techmap/alltech", ["vhdlsyn.txt"], None),
    ("techmap", "techmap/inferred", ["vhdlsyn.txt"], ["memory_inferred.vhd"]),
    ("techmap", "techmap/maps", ["vhdlsyn.txt"],
     ["memrwcol.vhd", "syncram.vhd", "syncram_2p.vhd", "syncram_dp.vhd", "syncrambw.vhd", "syncram_2pbw.vhd",
      "syncram64.vhd", "syncramlb.vhd", "regfile_3p.vhd", "scanreg.vhd", "grgates.vhd", "clkand.vhd", "clkmux.vhd",
      "clkinv.vhd", "syncreg.vhd", "techbuf.vhd", "cdcbus.vhd"]),
    ("bsc", "bsc/sparrow", ["vhdlsyn.txt"], None),
    ("gaisler", "gaisler/l5nv/shared", ["vhdlsyn.txt"], ["busif5_types.vhd", "l5nv_shared.vhd"]),
    ("gaisler", "gaisler/uart", ["vhdlsyn.txt"], ["uart.vhd"]),
    ("gaisler", "gaisler/plic", ["vhdlsyn.txt"], ["plic.vhd"]),
    ("gaisler", "gaisler/aplic", ["vhdlsyn.txt"], ["aplic.vhd"]),
    ("gaisler", "gaisler/noelv/pkg", None,
     ["noelv_cfg_64.vhd", "noelv.vhd", "noelv_cfg_types.vhd", "noelv_cpu_cfg_custom.vhd", "noelv_cpu_cfg.vhd",
      "noelv_pma_cfg.vhd"]),
    ("gaisler", "gaisler/l5nv/shared", ["vhdlsyn.txt"],
     ["l5tsc.vhd", "busif5x.vhd", "busif5rdb.vhd", "busif5.vhd", "tcmwrap5.vhd", "cachemem5.vhd", "snoopmem5.vhd"]),
    ("gaisler", "gaisler/noelv/core", ["vhdlsyn.txt"], None),
]

# structural and optional variants the simulation does not use
SKIP = {"cpucorenvbc_str.vhd", "cpucorenvb_str.vhd", "cpucorenv_str.vhd", "cpucorenvb_strnpkg.vhd", "noelvadvint.vhd",
        "inst_text.vhd", "crypto.vhd", "nvirqcdc.vhd", "nvdbgcdc.vhd"}


def tokens(path):
    out = []
    if os.path.exists(path):
        for line in open(path, encoding="latin-1"):
            out += [t for t in line.split("#")[0].split() if t.endswith(".vhd")]
    return out


seen = set()
for lib, d, manifests, keep in SETS:
    if manifests is None:
        names = list(keep)
    else:
        names = []
        for m in manifests:
            names += tokens(os.path.join(ROOT, d, m))
        if keep is not None:
            names = [n for n in keep if n in names]
    for n in names:
        p = os.path.normpath(os.path.join(ROOT, d, n))
        if os.path.basename(p) in SKIP or p in seen or not os.path.exists(p):
            continue
        seen.add(p)
        if p.endswith(os.path.join("sparc", "sparc_disas.vhd")) or p.endswith(os.path.join("sparc", "cpu_disas.vhd")):
            continue
        if p.endswith(os.path.join("grlib", "stdlib", "config.vhd")):
            # the reference NOEL-V design replaces the library's default configuration with its own
            # (128-bit AHB data, little endian, synchronous reset on every register); so does this build
            p = os.path.normpath(os.path.join(ROOT, "..", "designs", "noelv-generic", "grlib_config.vhd"))
        if NANOFPU and p.endswith(os.path.join("noelv", "core", "nanofpunv.vhd")):
            p = os.path.abspath(NANOFPU)
        print(lib, p)
