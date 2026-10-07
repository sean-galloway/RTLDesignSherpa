# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: jal_jalr
# Purpose: Exercise JAL forward and backward, JALR through an auipc+addi
#          computed register target (rs1 != 0), JALR with rs1 == rd, and a
#          JALR whose computed target has LSB set (must land at the even
#          address per the ISA LSB-clear rule).
#
#          Because the build flow uses objcopy on an unlinked object, no
#          relocation is available; absolute target offsets are hard-coded
#          as 12-bit JALR immediates (programs start at 0x0, so byte offsets
#          in the dump are the addresses).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    # ---- JAL forward ----
    jal   x1, mid          # x1 <- pc+4, jump forward to mid
    addi  x2, x0, 1        # should not execute

back_target:
    # ---- backward target: reached by the JAL backward below ----
    addi  x3, x0, 1        # x3 <- 1
    jal   x4, after        # x4 <- pc+4, jump forward to after
    addi  x5, x0, 1        # should not execute

mid:
    # ---- JAL backward (target back_target precedes this jump) ----
    addi  x6, x0, 1        # x6 <- 1
    jal   x7, back_target  # x7 <- pc+4, jump backward to back_target
    addi  x8, x0, 1        # should not execute

after:
    # ---- JALR through auipc+addi register target (rs1 != 0) ----
    auipc x8, 0            # x8 <- pc of auipc
    addi  x8, x8, 0x10     # x8 <- address of jalr_target
    jalr  x9, x8, 0        # x9 <- pc+4, jump to *x8
    addi  x10, x0, 1       # should not execute

jalr_target:
    # ---- JALR with rs1 == rd ----
    auipc x11, 0           # x11 <- pc of auipc
    addi  x11, x11, 0x10   # x11 <- address of rs1rd_target
    jalr  x11, x11, 0      # x11 <- pc+4, jump to *x11 (rs1 == rd)
    addi  x12, x0, 1       # should not execute

rs1rd_target:
    # ---- JALR with computed target LSB set ----
    auipc x13, 0           # x13 <- pc of auipc
    addi  x13, x13, 0x11   # x13 <- address of odd_target + 1
    jalr  x14, x13, 0      # x14 <- pc+4, target 0x...1 -> LSB cleared
    addi  x15, x0, 1       # should not execute

odd_target:
    ecall                  # halt, cause 1
    .size _start, . - _start
