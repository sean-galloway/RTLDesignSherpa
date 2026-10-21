# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_misaligned
# Purpose: Byte-lane rotation at every naturally aligned offset (bytes in
#          all four lanes, halves in both), then a misaligned load, which
#          halts with cause 4 (HALT_LALIGN) and writes nothing (2026-10-20:
#          kestrel traps misaligned data accesses).
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

    # ---- SB into each lane of word 0x104, byte loads back ----
    li    x13, 0xA1
    sb    x13, 4(x10)      # lane 0
    li    x14, 0xB2
    sb    x14, 5(x10)      # lane 1
    li    x15, 0xC3
    sb    x15, 6(x10)      # lane 2
    li    x16, 0xD4
    sb    x16, 7(x10)      # lane 3
    lb    x4,  4(x10)      # x4 = 0xFFFFFFA1
    lbu   x5,  5(x10)      # x5 = 0x000000B2
    lb    x6,  6(x10)      # x6 = 0xFFFFFFC3
    lbu   x7,  7(x10)      # x7 = 0x000000D4
    lw    x1,  4(x10)      # x1 = 0xD4C3B2A1

    # ---- SH into both halves of word 0x108, half loads back ----
    li    x17, 0x8234
    sh    x17, 8(x10)      # lanes 0-1
    li    x18, 0x5678
    sh    x18, 10(x10)     # lanes 2-3
    lh    x8,  8(x10)      # x8 = 0xFFFF8234
    lhu   x9,  8(x10)      # x9 = 0x00008234
    lh    x2,  10(x10)     # x2 = 0x00005678
    lw    x3,  8(x10)      # x3 = 0x56788234

    # ---- misaligned halfword load: halts, cause 4, x20 not written ----
    li    x20, 0x0BAD
    lh    x20, 9(x10)
    ecall                  # not reached
