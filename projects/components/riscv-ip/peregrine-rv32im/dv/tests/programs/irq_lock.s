# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# irq_lock.s -- interrupts on loads and stores whose D$ request is waiting
# (TASK-001 stage 4, the core's interrupt lock).  Cached build only.
#
# The irq_basic.s protocol: the TB drives the interrupt pins from the last
# value stored to `irq_ctrl` (bit 1 MTIP, bit 3 auto timer: the TB re-raises
# MTIP some cycles after each store that clears bit 1).  amber accepts a
# miss at once and holds ready low only for a write hit's second cycle, so
# a request waits on ready for one cycle: the load right behind a store.
# The test's interrupt source holds each raise back until a store
# handshake, so the interrupt lands while that load waits.  A waiting
# request must not be dropped (the TB's D-side contract monitor) and the
# interrupted instruction must re-execute.
#
#   1. Seed NLINES lines of region A, one word each, through the uncached
#      I/O alias (memory only; amber does not hold them).
#   2. With the auto timer on, walk region A with loads (each a cold
#      miss) and region B with stores (each a write-allocate miss); in
#      between, a write hit to a hot line and a load of the same word
#      (the load waits a cycle behind the hit).  Sum the region A loads.
#   3. Auto timer off; the sum of the loads.
#   4. At least eight interrupts were taken.
#   5. Region B reads back.
#
# Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1.

        .equ    NLINES,  160
        .equ    REGA,    0x80080000
        .equ    REGA_IO, 0x10080000            # the same memory, uncached
        .equ    REGB,    0x800A0000

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        la      s0, irq_ctrl
        li      s3, 0
        li      t0, 0x80                # MTIE
        csrw    mie, t0

# Test 1: seed region A through the I/O window
        li      gp, 1
        li      t0, REGA_IO
        li      t1, NLINES
        li      t2, 1
1:      sw      t2, 0(t0)
        addi    t2, t2, 1
        addi    t0, t0, 64
        addi    t1, t1, -1
        bnez    t1, 1b

# Test 2: cold-miss loads and stores under timer interrupts
        li      gp, 2
        li      t0, 0xA                 # auto timer on, MTIP raised: the
        sw      t0, 0(s0)               # handler's clear arms the timer
        csrsi   mstatus, 8
        li      t0, REGA
        li      t5, REGB - 64           # the hot line, just below region B
        li      a1, REGB
        li      t1, NLINES
        li      t2, 0                   # sum of the loads
        li      t3, 0                   # store value
        sw      x0, 0(t5)               # region B's first line: now in amber
1:      lw      t4, 0(t0)
        add     t2, t2, t4
        sw      t3, 4(t5)               # a write hit, then a load that
        lw      t6, 4(t5)               # waits a cycle behind its HIT_WR
        bne     t6, t3, fail
        sw      t3, 0(a1)               # region B: a write-allocate miss
        addi    t3, t3, 1
        addi    t0, t0, 64
        addi    a1, a1, 64
        addi    t1, t1, -1
        bnez    t1, 1b
        csrci   mstatus, 8
        sw      x0, 0(s0)               # auto timer off

# Test 3: the sum of the loads
        li      gp, 3
        li      t0, NLINES * (NLINES + 1) / 2
        bne     t2, t0, fail
# Test 4: at least eight interrupts were taken
        li      gp, 4
        li      t0, 8
        blt     s3, t0, fail
# Test 5: region B reads back
        li      gp, 5
        li      t5, REGB
        li      t1, NLINES
        li      t3, 0
1:      lw      t4, 0(t5)
        bne     t4, t3, fail
        addi    t3, t3, 1
        addi    t5, t5, 64
        addi    t1, t1, -1
        bnez    t1, 1b

pass:
        li      t0, 1
        la      t1, tohost
        sw      t0, 0(t1)
1:      j       1b

fail:
        slli    t0, gp, 1
        ori     t0, t0, 1
        la      t1, tohost
        sw      t0, 0(t1)
1:      j       1b

# --- handler: MTI only; clear MTIP in irq_ctrl (re-arms the auto timer) ---
        .balign 4
handler:
        csrr    s4, mcause
        bgez    s4, fail                # a synchronous exception: fail
        li      s5, 0x80000007
        bne     s4, s5, fail
        addi    s3, s3, 1
        lw      s6, 0(s0)
        andi    s6, s6, -3
        sw      s6, 0(s0)
        mret

        .section .data
        .balign 64
tohost: .word 0
        .balign 64
irq_ctrl:
        .word 0
