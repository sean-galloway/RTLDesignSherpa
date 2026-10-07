# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: focus
# Purpose: Review Focus pins for kestrel_core Task 5: writes to x0 are
#          discarded and back-to-back dependent ALU ops forward in time.
#          addi x1,x0,5 ; addi x2,x1,7 ; add x3,x2,x1 — terminated by ECALL.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    addi  x1, x0, 5        # x1 <- 5          (x0 reads as zero)
    addi  x2, x1, 7        # x2 <- 12         (back-to-back dependence on x1)
    add   x3, x2, x1       # x3 <- 17         (back-to-back dependence on x2)
    ecall                  # halt, cause 1
    .size _start, . - _start
