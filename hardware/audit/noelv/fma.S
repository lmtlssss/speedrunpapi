# 16 - (1 + 2^-52) * (1 - 2^-52), rounded up, on NOEL-V.
# The exact value is 15 + 2^-104, so the answer is the next double above 15, 0x402e000000000001, inexact.
# The program stores the result at s0, the float flags at s0 + 8, and a stop marker at s1.
        .option norelax
        .text
        .globl _start
_start:
        jal     t0, main                # t0 = address of trap
trap:   csrr    a2, mcause
        csrr    a3, mepc
        sd      a2, 16(s0)
        sd      a3, 24(s0)
        sd      x0, 0(s1)
1:      j       1b

main:   csrw    mtvec, t0
        lui     t0, 0x6
        csrs    mstatus, t0             # float unit on
        auipc   s0, 0x8                 # results go 0x8000 past here
        andi    s0, s0, -16
        auipc   s1, 0xf                 # a write 0xf000 past here stops the run
        andi    s1, s1, -16
        li      t1, 0x3ff0000000000001
        fmv.d.x f1, t1                  # 1 + 2^-52
        li      t1, 0x3feffffffffffffe
        fmv.d.x f2, t1                  # 1 - 2^-52
        li      t1, 0x4030000000000000
        fmv.d.x f3, t1                  # 16.0
        li      t1, 0x60
        csrw    fcsr, t1                # round up, flags clear
        fnmsub.d f11, f1, f2, f3        # 16 - (1 + 2^-52) * (1 - 2^-52)
        fmv.x.d a0, f11
        csrr    a1, fflags
        sd      a0, 0(s0)
        sd      a1, 8(s0)
        sd      x0, 0(s1)
2:      j       2b
