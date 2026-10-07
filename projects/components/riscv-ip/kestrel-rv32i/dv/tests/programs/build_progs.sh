#!/bin/bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Program: build_progs.sh
# Purpose: Rebuild the kestrel_core TB program images: assemble each .s with
#          riscv-none-elf-as, keep an objdump word listing for provenance, then
#          objcopy -O verilog + normalize_hex.py to the word-indexed images
#          the TB loads via +imem=<hex> ($readmemh into word arrays).
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

set -euo pipefail

TOOLCHAIN="${RISCV_TOOLCHAIN:-/mnt/data/tools/xpack-riscv-none-elf-gcc/bin}"
AS="$TOOLCHAIN/riscv-none-elf-as"
OBJDUMP="$TOOLCHAIN/riscv-none-elf-objdump"
OBJCOPY="$TOOLCHAIN/riscv-none-elf-objcopy"

cd "$(dirname "$0")"

for src in focus.s rv32ui_ops.s focus_at_0x100.s branch_all.s jal_jalr.s loop_sum.s ls_basic.s ls_misaligned.s ls_chain.s; do
    name="${src%.s}"
    "$AS" -march=rv32i -mabi=ilp32 "$src" -o "$name.o"
    "$OBJDUMP" -d "$name.o" > "$name.dump"
    "$OBJCOPY" -O verilog "$name.o" "$name.raw.hex"
    python3 normalize_hex.py "$name.raw.hex" "$name.hex"
    rm -f "$name.o" "$name.raw.hex"
    echo "built $name.hex"
done
