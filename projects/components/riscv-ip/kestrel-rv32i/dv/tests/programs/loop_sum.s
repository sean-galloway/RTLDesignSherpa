# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: loop_sum
# Purpose: Compute 10+9+...+1 in a loop. Exercises a TAKEN BACKWARD branch
#          (bne x2, x0, loop) that is repeatedly taken and finally falls
#          through, plus a forward taken branch at loop exit. Verifies the
#          pc_wdata sequence around negative and positive B-immediates.
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
    addi  x2, x0, 10         # counter <- 10
loop:
    beq   x2, x0, done       # exit when counter == 0 (forward, fall-through then taken)
    add   x1, x1, x2         # sum <- sum + counter
    addi  x2, x2, -1         # counter <- counter - 1
    bne   x2, x0, loop       # repeat while counter != 0 (taken backward edge)
    addi  x3, x0, 1          # should not execute
done:
    ecall                    # halt, cause 1; x1 should be 55
    .size _start, . - _start
