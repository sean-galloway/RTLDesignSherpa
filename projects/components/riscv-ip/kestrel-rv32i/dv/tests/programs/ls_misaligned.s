# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_misaligned
# Purpose: Review Focus 6: architectural cross-word misaligned L/S.
#          Every vector places nonzero, distinct bytes on both sides of a
#          32-bit word boundary and checks the full assembled value.
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

    # ---- SW at addr%4==2 (crosses 0x104/0x108), full-word load back ----
    li    x11, 0xDEADBEEF
    sw    x11, 6(x10)      # bytes 0x106..0x109: EF BE AD DE (little-endian)
    lw    x1,  6(x10)      # x1 = 0xDEADBEEF

    # ---- SH at addr%4==3 (crosses 0x104/0x108), halfword load back ----
    li    x12, 0xCAFE
    sh    x12, 7(x10)      # bytes 0x107=FE, 0x108=CA
    lh    x2,  7(x10)      # x2 = 0xFFFFCAFE (sign-extended)
    lhu   x3,  7(x10)      # x3 = 0x0000CAFE

    # ---- SB at all four offsets around the word boundary 0x103/0x104 ----
    li    x13, 0xA1
    sb    x13, 3(x10)      # 0x103: byte 3 of word 0x100
    li    x14, 0xB2
    sb    x14, 4(x10)      # 0x104: byte 0 of word 0x104
    li    x15, 0xC3
    sb    x15, 5(x10)      # 0x105: byte 1 of word 0x104
    li    x16, 0xD4
    sb    x16, 6(x10)      # 0x106: byte 2 of word 0x104

    lb    x4,  3(x10)      # x4 = 0xFFFFFFA1
    lbu   x5,  4(x10)      # x5 = 0x000000B2
    lb    x6,  5(x10)      # x6 = 0x000000C3
    lbu   x7,  6(x10)      # x7 = 0x000000D4

    # ---- LH/LHU at offset 2 (in-word misaligned, not crossing) ----
    li    x17, 0x1234
    sh    x17, 6(x10)      # bytes 0x106=34, 0x107=12
    lh    x8,  6(x10)      # x8 = 0x00001234
    lhu   x9,  6(x10)      # x9 = 0x00001234

    # ---- SW at addr%4==1 (crosses 0x104/0x108), full-word load back ----
    li    x18, 0x11223344
    sw    x18, 5(x10)      # bytes 0x105..0x108: 44 33 22 11
    lw    x19, 5(x10)      # x19 = 0x11223344

    ecall                  # halt, cause 1
    .size _start, . - _start
