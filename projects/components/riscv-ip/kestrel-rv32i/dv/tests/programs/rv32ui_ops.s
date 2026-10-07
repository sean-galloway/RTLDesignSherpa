# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: rv32ui_ops
# Purpose: One vector per RV32I OP/OP-IMM operation enabled by the Task 5
#          vertical slice, plus LUI/AUIPC and x0-discard checks. Runs on the
#          kestrel_core golden-trace TB; every write lands in a distinct
#          register so the RVFI diff pins each opcode independently.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    # ---- OP-IMM vectors (funct3 sweep, x1 = -5 throughout) ----
    addi  x1,  x0, -5      # x1  <- 0xFFFF_FFFB  (sign-extended immediate)
    addi  x2,  x1, 7       # x2  <- 2            (back-to-back dependence)
    slti  x3,  x1, 6       # x3  <- 1            (signed: -5 < 6)
    sltiu x4,  x1, 6       # x4  <- 0            (unsigned: 0xFB > 6)
    xori  x5,  x2, 0x55    # x5  <- 2 ^ 0x55
    ori   x6,  x2, 0x1F0   # x6  <- 2 | 0x1F0
    andi  x7,  x1, 0x7F0   # x7  <- 0xFB & 0x7F0 (imm is 12-bit: 0x7F0)
    slli  x8,  x2, 4       # x8  <- 2 << 4
    srli  x9,  x1, 4       # x9  <- logical shift of a negative value
    srai  x10, x1, 4       # x10 <- arithmetic shift of a negative value
    # ---- OP vectors (register-register, funct3/funct7 sweep) ----
    add   x11, x2, x1      # x11 <- 2 + (-5)
    sub   x12, x2, x1      # x12 <- 2 - (-5)   (funct7 = 0x20)
    sll   x13, x2, x2      # x13 <- 2 << 2
    slt   x14, x1, x2      # x14 <- 1          (signed)
    sltu  x15, x1, x2      # x15 <- 0          (unsigned)
    xor   x16, x1, x5      # x16 <- x1 ^ x5
    srl   x17, x1, x2      # x17 <- logical shift of a negative value
    sra   x18, x1, x2      # x18 <- arithmetic shift of a negative value
    or    x19, x1, x2      # x19 <- x1 | x2
    and   x20, x1, x2      # x20 <- x1 & x2
    # ---- U-type vectors ----
    lui   x21, 0xABCDE     # x21 <- 0xABCDE000 (writeback muxed from imm_gen)
    auipc x22, 0x1         # x22 <- pc + 0x1000 (ALU src_a = PC)
    # ---- x0 discard via RVFI (Review Focus 1) ----
    addi  x0,  x0, 5       # writes x0: retire record shows rd=x0, x0 reads stay 0
    add   x0,  x1, x2      # same via the OP path
    ecall                  # halt, cause 1
    .size _start, . - _start
