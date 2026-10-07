# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_chain
# Purpose: Store-then-load-back dependent chain.  Each store retires in cycle
#          N and the following load in cycle N+1, pinning the single-cycle
#          memory semantics of the kestrel datapath.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x10, 0x100       # data base address

    li    x11, 0x89ABCDEF
    sw    x11, 0(x10)      # word store
    lw    x1,  0(x10)      # load it back immediately

    li    x12, 0x1234
    sh    x12, 0(x10)      # halfword store at offset 0
    lh    x2,  0(x10)      # load back

    li    x13, 0xAB
    sb    x13, 2(x10)      # byte store at offset 2
    lbu   x3,  2(x10)      # load back unsigned

    li    x14, 0x80
    sb    x14, 3(x10)      # byte store at offset 3 (sign-extension boundary)
    lb    x4,  3(x10)      # load back signed

    ecall                  # halt, cause 1
    .size _start, . - _start
