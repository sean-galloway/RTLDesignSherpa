# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: system_misalign_jmp
# Purpose: Task 9 directed test for the instruction-address-misaligned halt.
#          An ALIGNED JAL must still work (regression), then a JAL to a
#          +2-offset (non-4-aligned) target must halt with cause 3, retiring
#          the rvfi_trap beat with the misaligned target on pc_wdata.
#          Assembled at address 0 (build_progs.sh, unlinked object).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

    .section .text
    .globl _start
_start:
    # ---- aligned JAL regression: must retire normally ----
    jal   x1, aligned_tgt    # 0x00: x1 <- 0x04, jump to 0x0C (4-aligned)
    addi  x2, x0, 1          # 0x04: should not execute
    addi  x2, x0, 2          # 0x08: should not execute
aligned_tgt:
    addi  x3, x0, 7          # 0x0C: x3 <- 7 (executes)
    # ---- misaligned JAL: target 0x10 + 2 = 0x12, not 4-aligned ----
    jal   x0, . + 2          # 0x10: must halt here, cause 3, rvfi_trap beat
    addi  x4, x0, 1          # 0x14: should not execute
    ecall                    # 0x18: should not execute
    .size _start, . - _start
