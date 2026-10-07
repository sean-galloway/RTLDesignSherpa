# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: system_ecall
# Purpose: ECALL raises halt with cause 1 and holds it: imem_addr freezes,
#          rvfi_valid stays low, no further retirement (Review Focus 4).
#          The TB checks the hold for several cycles after the halt beat.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x1, 0x5a
    addi  x2, x1, 0x01         # x2 = 0x5b (pre-halt state for the trace diff)
    ecall                      # halt, cause 1
    .size _start, . - _start
