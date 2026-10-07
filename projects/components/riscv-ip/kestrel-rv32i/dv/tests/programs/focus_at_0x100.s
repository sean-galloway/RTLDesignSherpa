# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: focus_at_0x100
# Purpose: Same focus program relocated to 0x100 via .org. Loaded with a
#          TB parameter override RESET_ADDR=0x100 to pin Review Focus 3:
#          the first fetched (and first retired) PC is exactly RESET_ADDR.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
    .org 0x100             # program image starts at byte address 0x100
_start:
    addi  x1, x0, 5        # x1 <- 5
    addi  x2, x1, 7        # x2 <- 12
    add   x3, x2, x1       # x3 <- 17
    ecall                  # halt, cause 1
    .size _start, . - _start
