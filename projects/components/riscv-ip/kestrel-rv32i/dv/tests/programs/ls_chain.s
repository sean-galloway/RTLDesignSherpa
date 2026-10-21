# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_chain
# Purpose: Store-then-load-back dependent chain at every access size, each
#          load immediately after its store, plus a store-to-store-to-load
#          overwrite.  Pins that a store is visible to the very next
#          instruction's load (2026-10-20: the cross-word vectors became
#          aligned ones when kestrel began halting on misaligned access).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x10, 0x100       # data base address

    # ---- Word store then load back ----
    li    x11, 0x89ABCDEF
    sw    x11, 4(x10)      # word store at 0x104
    lw    x1,  4(x10)      # load it back immediately: full value

    # ---- Halfword store into the upper half, then load back ----
    li    x12, 0xABCD
    sh    x12, 6(x10)      # halfword store at 0x106 (lanes 2-3 of 0x104)
    lh    x2,  6(x10)      # signed load back
    lhu   x3,  6(x10)      # unsigned load back
    lw    x6,  4(x10)      # the merged word: 0xABCDCDEF

    # ---- Store, overwrite, load: the second store wins ----
    li    x14, 0x11111111
    li    x15, 0x22222222
    sw    x14, 8(x10)
    sw    x15, 8(x10)
    lw    x7,  8(x10)      # 0x22222222

    # ---- Aligned byte store then load back ----
    li    x13, 0x80
    sb    x13, 2(x10)      # byte store at offset 2
    lb    x4,  2(x10)      # signed load back
    lbu   x5,  2(x10)      # unsigned load back

    ecall                  # halt, cause 1
    .size _start, . - _start
