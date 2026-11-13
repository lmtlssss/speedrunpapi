# Reads the bus writes a run of tb_core printed ("W address data size cycle") and reports what the program stored:
# the result at s0, the float flags at s0 + 8, or mcause and mepc at s0 + 16 and s0 + 24 after a trap.
# usage: python3 report.py prog.out
import sys

mem = {}
note = ""
for line in open(sys.argv[1]):
    t = line.split()
    if t[0] == "T":
        note = "   (" + " ".join(t[1:]) + ")"
        continue
    mem[int(t[1], 16) & 0xFFFF] = int(t[2], 16)
base = 0x8020                                    # s0 in both programs: 0xc0008020
word = lambda off: (mem.get(base + off + 4, 0) << 32) | mem.get(base + off, 0)
if base + 16 in mem:
    print("trap: mcause %x, mepc %x%s" % (word(16), word(24), note))
elif base in mem:
    print("result %016x flags %02x%s" % (word(0), word(8), note))
else:
    print("nothing stored%s" % note)
