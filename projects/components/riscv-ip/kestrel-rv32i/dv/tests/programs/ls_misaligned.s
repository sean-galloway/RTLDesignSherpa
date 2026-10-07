# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_misaligned
# Purpose: Review Focus 6: in-word rotated-strobe misaligned accesses.
#          SW at addr%4==2 then LW back; SH at addr%4==3; SB at all four
#          offsets around a word boundary; LH/LHU at offset 2.
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

    # ---- SW at addr%4==2 (crosses lanes 2/3 inside the word), then LW back ----
    # Word address accessed = 0x104, byte offset inside word = 2.
    li    x11, 0xDEADBEEF
    sw    x11, 6(x10)      # wstrb = 0b1100 -> writes bytes 2,3 of word 0x104
    lw    x1,  6(x10)      # rdata_shifted = word >> 16 -> x1 = 0x0000BEEF

    # ---- SH at addr%4==3 (rotated into lane 3, high byte drops) ----
    li    x12, 0xCAFE
    sh    x12, 7(x10)      # wstrb = 0b1000 -> writes byte 3 of word 0x104
    lh    x2,  7(x10)      # x2 = 0x000000FE (low byte of 0xCAFE, high byte dropped)
    lhu   x3,  7(x10)      # x3 = 0x000000FE

    # ---- SB at all four offsets around the word boundary 0x103/0x104 ----
    li    x13, 0xA1
    sb    x13, 3(x10)      # byte 3 of word 0x100
    li    x14, 0xB2
    sb    x14, 4(x10)      # byte 0 of word 0x104
    li    x15, 0xC3
    sb    x15, 5(x10)      # byte 1 of word 0x104
    li    x16, 0xD4
    sb    x16, 6(x10)      # byte 2 of word 0x104

    lb    x4,  3(x10)      # x4 = 0xFFFFFFA1 (sign-extended)
    lbu   x5,  4(x10)      # x5 = 0x000000B2
    lb    x6,  5(x10)      # x6 = 0x000000C3
    lbu   x7,  6(x10)      # x7 = 0x000000D4

    # ---- LH/LHU at offset 2 inside a word ----
    li    x17, 0x1234
    sh    x17, 6(x10)      # wstrb = 0b1100 -> bytes 2,3 of word 0x104 = 0x1234
    lh    x8,  6(x10)      # x8 = 0x00001234
    lhu   x9,  6(x10)      # x9 = 0x00001234

    ecall                  # halt, cause 1
    .size _start, . - _start
