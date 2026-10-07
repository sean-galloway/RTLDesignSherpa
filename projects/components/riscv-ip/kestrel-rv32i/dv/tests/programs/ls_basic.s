# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: ls_basic
# Purpose: Store word/halfword/byte patterns and load them back with every
#          size/sign combination at aligned offsets.  Pins LB/LBU/LH/LHU/LW
#          extraction and the sign-extension boundary at 0x80/0x8000.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    li    x10, 0x100       # data base address (in dmem, separate from imem)

    # ---- Word pattern: every byte distinct, MSB byte = 0x12 (sign bit clear) ----
    li    x11, 0x12345678
    sw    x11, 0(x10)      # mem[0x100..0x103] = 78 56 34 12 (little-endian)

    lb    x1,  0(x10)      # x1  = 0x00000078
    lbu   x2,  0(x10)      # x2  = 0x00000078
    lb    x3,  1(x10)      # x3  = 0x00000056
    lbu   x4,  1(x10)      # x4  = 0x00000056
    lb    x5,  2(x10)      # x5  = 0x00000034
    lbu   x6,  2(x10)      # x6  = 0x00000034
    lb    x7,  3(x10)      # x7  = 0x00000012
    lbu   x8,  3(x10)      # x8  = 0x00000012

    lh    x9,  0(x10)      # x9  = 0x00005678
    lhu   x12, 0(x10)      # x12 = 0x00005678
    lh    x13, 2(x10)      # x13 = 0x00001234
    lhu   x14, 2(x10)      # x14 = 0x00001234

    lw    x15, 0(x10)      # x15 = 0x12345678

    # ---- Sign-extension boundary: byte 0x80 and halfword 0x8000 ----
    li    x16, 0x80
    sb    x16, 0(x10)
    lb    x17, 0(x10)      # x17 = 0xFFFFFF80
    lbu   x18, 0(x10)      # x18 = 0x00000080

    li    x19, 0x8000
    sh    x19, 0(x10)
    lh    x20, 0(x10)      # x20 = 0xFFFF8000
    lhu   x21, 0(x10)      # x21 = 0x00008000

    ecall                  # halt, cause 1
    .size _start, . - _start
