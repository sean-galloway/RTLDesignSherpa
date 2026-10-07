# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: system_ebreak
# Purpose: EBREAK raises halt with cause 2 and holds it exactly like ECALL
#          (cause 1): imem_addr freeze, rvfi_valid low, no further retire.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x1, 0xa5
    addi  x2, x1, -0x01        # x2 = 0xa4 (pre-halt state for the trace diff)
    ebreak                     # halt, cause 2
    .size _start, . - _start
