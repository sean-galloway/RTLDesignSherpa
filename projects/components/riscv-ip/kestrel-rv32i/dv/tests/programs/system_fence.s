# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: system_fence
# Purpose: FENCE and FENCE.I must retire as pure NOPs: the golden trace shows
#          the retire beats with no register-file, memory, or PC side effects
#          (Review Focus 5).  The surrounding addi/xor vectors pin that the
#          datapath state around the fences is unaffected.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x1, 0x11
    fence                      # MISC-MEM funct3=000: retire as NOP
    addi  x2, x1, 0x22         # x2 = 0x33 (datapath alive across fence)
    fence.i                    # MISC-MEM funct3=001: retire as NOP
    xor   x3, x2, x1           # x3 = 0x22
    fence  iorw, iorw          # FENCE with nonzero pred/succ: still a NOP
    add   x4, x3, x2           # x4 = 0x55
    ecall                      # halt, cause 1
    .size _start, . - _start
