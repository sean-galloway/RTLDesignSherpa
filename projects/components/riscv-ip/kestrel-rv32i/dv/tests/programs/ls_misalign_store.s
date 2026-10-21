# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_misalign_store
# Purpose: A misaligned word store halts with cause 5 (HALT_SALIGN) and
#          performs no write: the trap beat reports an empty write mask
#          (2026-10-20: kestrel traps misaligned data accesses).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-20

    .section .text
    .globl _start
_start:
    li    x10, 0x100       # data base address
    li    x11, 0x11223344
    sw    x11, 4(x10)      # aligned: word 0x104
    lw    x1,  4(x10)      # x1 = 0x11223344
    li    x12, 0xDEADBEEF
    sw    x12, 6(x10)      # misaligned: halts, cause 5, no write
    ecall                  # not reached
