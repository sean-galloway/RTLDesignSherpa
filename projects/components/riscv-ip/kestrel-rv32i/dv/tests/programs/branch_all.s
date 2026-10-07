# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: branch_all
# Purpose: Exercise every RV32I branch condition (BEQ/BNE/BLT/BGE/BLTU/BGEU)
#          in both taken and not-taken directions, with rs1/rs2 pairs that
#          discriminate signed vs unsigned comparisons. Includes the classic
#          BLT-vs-BLTU-at-0x80000000 case and the regfile x0-discard check.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    # ---- Review-carry M3: x0 discard at integration level ----
    addi  x0, x0, 5        # discarded write to x0
    addi  x1, x0, 7        # x1 <- 7 (x0 must read as zero after discard)

    # ---- BEQ ----
    li    x2, 5
    beq   x1, x2, beq_fail # 7 != 5 -> not taken
    addi  x3, x0, 1        # x3 <- 1 (fall-through path)
beq_fail:
    beq   x1, x1, beq_taken # 7 == 7 -> taken
    addi  x4, x0, 1        # should not execute
beq_taken:

    # ---- BNE ----
    bne   x1, x1, bne_fail # 7 == 7 -> not taken
    addi  x5, x0, 1        # x5 <- 1 (fall-through path)
bne_fail:
    bne   x1, x2, bne_taken # 7 != 5 -> taken
    addi  x6, x0, 1        # should not execute
bne_taken:

    # ---- BLT / BGE signed vs unsigned at 0x80000000 ----
    li    x7, 0x80000000   # signed: -2147483648, unsigned: 2147483648
    li    x8, 0

    blt   x7, x8, blt_taken # -2147483648 < 0 -> taken
    addi  x9, x0, 1        # should not execute
blt_taken:
    blt   x8, x7, blt_fail  # 0 < -2147483648 -> false -> not taken
    addi  x10, x0, 1       # x10 <- 1 (fall-through path)
blt_fail:

    bge   x7, x8, bge_fail  # -2147483648 >= 0 -> false -> not taken
    addi  x11, x0, 1       # x11 <- 1 (fall-through path)
bge_fail:
    bge   x8, x7, bge_taken # 0 >= -2147483648 -> true -> taken
    addi  x12, x0, 1       # should not execute
bge_taken:

    bltu  x7, x8, bltu_fail # 0x80000000 < 0 -> false -> not taken
    addi  x13, x0, 1       # x13 <- 1 (fall-through path)
bltu_fail:
    bltu  x8, x7, bltu_taken # 0 < 0x80000000 -> true -> taken
    addi  x14, x0, 1       # should not execute
bltu_taken:

    bgeu  x7, x8, bgeu_taken # 0x80000000 >= 0 -> true -> taken
    addi  x15, x0, 1       # should not execute
bgeu_taken:
    bgeu  x8, x7, bgeu_fail # 0 >= 0x80000000 -> false -> not taken
    addi  x16, x0, 1       # x16 <- 1 (fall-through path)
bgeu_fail:

    ecall                  # halt, cause 1
    .size _start, . - _start
