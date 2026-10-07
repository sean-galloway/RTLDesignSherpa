# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: system_illegal
# Purpose: An illegal instruction (all-ones word: no matching decode row)
#          halts the core with cause 0xF, emits the rvfi_trap beat, and
#          freezes fetch.  The TB checks cause/hold directly; the golden
#          interpreter is intentionally not used here (M2: it raises
#          NotImplementedError on encodings it does not implement).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x1, 0x123
    addi  x2, x1, 0x001        # x2 = 0x124 (pre-halt state pinned by the TB)
    .word 0xFFFFFFFF           # illegal instruction: halt, cause 0xF
    .size _start, . - _start
