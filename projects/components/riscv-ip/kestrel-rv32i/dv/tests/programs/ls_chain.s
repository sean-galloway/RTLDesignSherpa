# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_chain
# Purpose: Store-then-load-back dependent chain, including a cross-word
#          store followed immediately by a cross-word load.  Pins the
#          two-cycle memory semantics and the full assembled value.
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

    # ---- Cross-word word store then load back ----
    li    x11, 0x89ABCDEF
    sw    x11, 6(x10)      # word store crossing 0x104/0x108
    lw    x1,  6(x10)      # load it back immediately: full value

    # ---- Cross-word halfword store then load back ----
    li    x12, 0xABCD
    sh    x12, 7(x10)      # halfword store crossing 0x104/0x108
    lh    x2,  7(x10)      # signed load back
    lhu   x3,  7(x10)      # unsigned load back

    # ---- Aligned byte store then load back ----
    li    x13, 0x80
    sb    x13, 2(x10)      # byte store at offset 2
    lb    x4,  2(x10)      # signed load back
    lbu   x5,  2(x10)      # unsigned load back

    ecall                  # halt, cause 1
    .size _start, . - _start
