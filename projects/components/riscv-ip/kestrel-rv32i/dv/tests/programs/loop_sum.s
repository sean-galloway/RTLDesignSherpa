# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: loop_sum
# Purpose: Compute 1+2+...+10 in a loop. Exercises taken-branch timing,
#          forward/backward branch targets, and the pc_wdata sequence.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    addi  x1, x0, 0          # sum <- 0
    addi  x2, x0, 1          # i <- 1
    addi  x3, x0, 11         # limit <- 11
loop:
    bge   x2, x3, done       # exit when i >= 11
    add   x1, x1, x2         # sum <- sum + i
    addi  x2, x2, 1          # i <- i + 1
    jal   x0, loop           # repeat
    addi  x4, x0, 1          # should not execute
done:
    ecall                    # halt, cause 1; x1 should be 55
    .size _start, . - _start
