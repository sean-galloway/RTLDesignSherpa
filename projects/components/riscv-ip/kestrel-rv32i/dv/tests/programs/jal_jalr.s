# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: jal_jalr
# Purpose: Exercise JAL forward/backward, JALR through a register target,
#          and a JALR whose computed target has LSB set (must land at the
#          even address per the ISA LSB-clear rule).
#
#          Because the build flow uses objcopy on an unlinked object, no
#          relocation is available; absolute target addresses are hard-coded
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
    jal   x1, forward        # x1 <- pc+4, jump to forward
    addi  x2, x0, 1          # should not execute
forward:

    # ---- JAL backward ----
    jal   x3, backward       # x3 <- pc+4, jump to backward
    addi  x4, x0, 1          # should not execute
backward:

    # ---- JALR via register target (x0 base + immediate) ----
    jalr  x6, x0, 0x18       # x6 <- pc+4, jump to 0x18 (jalr_target)
    addi  x7, x0, 1          # should not execute
jalr_target:

    # ---- JALR with computed target LSB set ----
    jalr  x9, x0, 0x21       # x9 <- pc+4, target 0x21 -> LSB cleared -> 0x20
    addi  x10, x0, 1         # should not execute
odd_target:

    ecall                    # halt, cause 1
    .size _start, . - _start
