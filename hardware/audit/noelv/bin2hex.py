# Little-endian binary -> one 32-bit hex word per line. usage: python3 bin2hex.py IN.bin OUT.hex
import struct
import sys

b = open(sys.argv[1], "rb").read()
b += b"\x13\x00\x00\x00"[: (-len(b)) % 4]
with open(sys.argv[2], "w") as f:
    for i in range(0, len(b), 4):
        f.write("%08x\n" % struct.unpack_from("<I", b, i)[0])
