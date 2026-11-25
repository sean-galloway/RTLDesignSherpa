# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# io_basic.s -- peregrine's uncached I/O window (PRD P7, amended 2026-11-24:
# 0x1000_0000-0x1FFF_FFFF) on the cached build (TASK-001 stage 4).
#
# The TB memory aliases modulo its size, so IO = 0x100C_0000 and
# RAM = 0x800C_0000 are the same memory words; one goes through the
# uncached port, the other through amber.
#
#   1. Lanes and sizes: word, halfword and byte stores to both 32-bit lanes
#      of a 64-bit beat through the uncached port; read back with every
#      load size and sign.
#   2. The window bypasses the D$: a RAM-alias load sees what the I/O
#      stores wrote (first touch, amber fills from memory); a RAM-alias
#      store sits dirty in amber, so an I/O load still reads the old
#      memory word; after fence.i (amber clean) it reads the new one.
#   3. A response captured while the core is held: an uncached load
#      placed so that, while it is in MEM, fetch crosses into a line the
#      I$ has never held; the refill holds the core while the load's
#      response arrives (at three offsets, so one of them lines up).
#
# Any trap fails.  Pass: tohost = 1.  Fail: tohost = (gp << 1) | 1.

        .equ    IO,     0x100C0000
        .equ    RAM,    0x800C0000

        .section .text
        .globl _start
_start:
        la      t0, handler
        csrw    mtvec, t0
        li      s0, IO
        li      s1, RAM

# Test 1: lanes and sizes through the uncached port
        li      gp, 1
        li      t1, 0x11223344
        sw      t1, 0(s0)               # lane 0
        li      t1, 0x55667788
        sw      t1, 4(s0)               # lane 1
        li      t1, 0xA1B2
        sh      t1, 2(s0)               # lane 0, high half
        li      t1, 0xC3
        sb      t1, 5(s0)               # lane 1, byte 1
        li      t1, 0xD4
        sb      t1, 7(s0)               # lane 1, byte 3
        lw      t2, 0(s0)
        li      t3, 0xA1B23344
        bne     t2, t3, fail
        lw      t2, 4(s0)
        li      t3, 0xD466C388
        bne     t2, t3, fail
        lhu     t2, 2(s0)
        li      t3, 0xA1B2
        bne     t2, t3, fail
        lh      t2, 2(s0)
        li      t3, 0xFFFFA1B2
        bne     t2, t3, fail
        lbu     t2, 5(s0)
        li      t3, 0xC3
        bne     t2, t3, fail
        lb      t2, 7(s0)
        li      t3, 0xFFFFFFD4
        bne     t2, t3, fail
        lhu     t2, 6(s0)
        li      t3, 0xD466
        bne     t2, t3, fail

# Test 2: the I/O window does not go through amber
        li      gp, 2
        sw      x0, 8(s0)               # memory word 0 (a rerun after reset
                                        # finds the last run's value there)
        lw      t2, 4(s1)               # RAM alias, first touch: a fill
        li      t3, 0xD466C388
        bne     t2, t3, fail
        li      t1, 0x0BADF00D
        sw      t1, 8(s1)               # dirty in amber only
        lw      t2, 8(s1)
        bne     t2, t1, fail            # amber has it
        lw      t2, 8(s0)               # memory does not
        bnez    t2, fail
        fence.i                         # amber clean-all
        lw      t2, 8(s0)
        bne     t2, t1, fail

# Test 3: an uncached load's response while the core is held for a refill
        li      gp, 3
        li      t3, 0xD466C388
        j       blk0
        .align 6
blk0:   .rept   12
        nop
        .endr
        lw      t1, 4(s0)               # offset 48
        .align 6
        bne     t1, t3, fail
        j       blk1
        .align 6
blk1:   .rept   13
        nop
        .endr
        lw      t1, 4(s0)               # offset 52
        .align 6
        bne     t1, t3, fail
        j       blk2
        .align 6
blk2:   .rept   14
        nop
        .endr
        lw      t1, 4(s0)               # offset 56
        .align 6
        bne     t1, t3, fail
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
        .align 3
        .globl tohost
tohost: .dword 0
        .globl fromhost
fromhost: .dword 0
