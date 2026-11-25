# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# smc_basic.s -- peregrine self-modifying code through the write-back D$
# (TASK-001 stage 4, PRD P10), on the cached build (peregrine_top).
#
# Code is written with ordinary stores, so it sits DIRTY in amber; fetch
# reads memory through the I$.  Only fence.i (amber clean-all, then I$
# invalidate) makes the new code visible:
#   - without the D$ clean the I$ refills the old memory contents (zeros
#     the first time: an illegal instruction, so the trap handler fails);
#   - without the I$ invalidate the I$ keeps the old instructions.
#
#   1. Write a routine of N `addi a0, a0, 1` + `ret` across three cache
#      lines into codebuf, fence.i, call it: a0 must be N.
#   2. Call it again (now in the I$), rewrite every addi to
#      `addi a0, a0, 2`, fence.i, call it: a0 must be 2N.
#   3. Load a word of the routine first (the line is then Shared in
#      amber, so the store is an upgrade), rewrite the first addi to
#      `addi a0, a0, 7`, fence.i, call: a0 must be 2N + 5.
#   4. Data across a clean: byte, halfword and word stores over eight
#      lines, fence.i, read every word back (the lines stay valid and
#      clean, so these are hits).
#   5. Dirty evictions and a clean: WAYS + 2 lines mapping to one amber
#      set (stride SETS * LINE = 8 KiB) are written, so some are evicted
#      dirty before the clean writes back the rest; fence.i, read back.
#
# Any trap fails.  Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1, gp = the
# test number.

        .equ    N,          40              # addi words: 160 B, three lines
        .equ    INSN_ADD1,  0x00150513      # addi a0, a0, 1
        .equ    INSN_ADD2,  0x00250513      # addi a0, a0, 2
        .equ    INSN_ADD7,  0x00750513      # addi a0, a0, 7
        .equ    INSN_RET,   0x00008067      # jalr x0, 0(ra)
        .equ    EVBASE,     0x80040000      # test 5: one amber set
        .equ    EVSTRIDE,   0x2000          # SETS * LINE_BYTES
        .equ    EVLINES,    6               # WAYS + 2

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0

# Test 1: new code, written dirty, made visible by fence.i
        li      gp, 1
        la      t0, codebuf
        li      t1, N
        li      t2, INSN_ADD1
1:      sw      t2, 0(t0)
        addi    t0, t0, 4
        addi    t1, t1, -1
        bnez    t1, 1b
        li      t2, INSN_RET
        sw      t2, 0(t0)
        fence.i
        li      a0, 0
        la      t0, codebuf
        jalr    ra, 0(t0)
        li      t3, N
        bne     a0, t3, fail

# Test 2: rewrite code the I$ already holds
        li      gp, 2
        li      a0, 0
        la      t0, codebuf
        jalr    ra, 0(t0)               # run the old routine again (I$ hit)
        li      t3, N
        bne     a0, t3, fail
        la      t0, codebuf
        li      t1, N
        li      t2, INSN_ADD2
1:      sw      t2, 0(t0)
        addi    t0, t0, 4
        addi    t1, t1, -1
        bnez    t1, 1b
        fence.i
        li      a0, 0
        la      t0, codebuf
        jalr    ra, 0(t0)
        li      t3, 2 * N
        bne     a0, t3, fail

# Test 3: a store that upgrades a line a load brought in
        li      gp, 3
        la      t0, codebuf
        lw      t1, 0(t0)
        li      t2, INSN_ADD2
        bne     t1, t2, fail
        li      t2, INSN_ADD7
        sw      t2, 0(t0)
        fence.i
        li      a0, 0
        la      t0, codebuf
        jalr    ra, 0(t0)
        li      t3, 2 * N + 5
        bne     a0, t3, fail

# Test 4: data stores of every size survive a clean, and stay readable
        li      gp, 4
        la      t0, databuf
        li      t1, 128                 # words: eight 64 B lines
        li      t2, 0x11000000
1:      sw      t2, 0(t0)
        addi    t2, t2, 0x101
        addi    t0, t0, 4
        addi    t1, t1, -1
        bnez    t1, 1b
        la      t0, databuf
        li      t2, 0xA5
        sb      t2, 1(t0)               # word 0 byte 1
        li      t2, 0xBEEF
        sh      t2, 66(t0)              # word 16 (line 1) high half
        fence.i
        la      t0, databuf
        lw      t1, 0(t0)
        li      t2, 0x1100A500
        bne     t1, t2, fail
        lw      t1, 64(t0)
        li      t2, 0xBEEF0000 + ((0x11000000 + 16 * 0x101) & 0xFFFF)
        bne     t1, t2, fail
        addi    t0, t0, 4
        li      t1, 127
        li      t2, 0x11000101
        li      t4, 15                  # words left before word 16
1:      beqz    t4, 2f
        lw      t3, 0(t0)
        bne     t3, t2, fail
2:      addi    t4, t4, -1
        addi    t2, t2, 0x101
        addi    t0, t0, 4
        addi    t1, t1, -1
        bnez    t1, 1b

# Test 5: dirty evictions in one set, then a clean
        li      gp, 5
        li      t0, EVBASE
        li      t1, EVLINES
        li      t2, 0x5A000001
        li      t5, EVSTRIDE
1:      sw      t2, 0(t0)
        sw      t2, 60(t0)              # last word of the line too
        addi    t2, t2, 1
        add     t0, t0, t5
        addi    t1, t1, -1
        bnez    t1, 1b
        fence.i
        li      t0, EVBASE
        li      t1, EVLINES
        li      t2, 0x5A000001
1:      lw      t3, 0(t0)
        bne     t3, t2, fail
        lw      t3, 60(t0)
        bne     t3, t2, fail
        addi    t2, t2, 1
        add     t0, t0, t5
        addi    t1, t1, -1
        bnez    t1, 1b

        j       pass

fail:
        slli    t1, gp, 1
        ori     t1, t1, 1
        j       report
pass:
        li      t1, 1
report:
        la      t0, tohost
1:      sw      t1, 0(t0)
        j       1b

        .align 2
handler:
        j       fail

        .section .data
        .align 6
codebuf:
        .skip   256
databuf:
        .skip   512
        .align 3
        .globl tohost
tohost: .dword 0
        .globl fromhost
fromhost: .dword 0
