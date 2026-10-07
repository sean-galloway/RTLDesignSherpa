#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: normalize_hex
# Purpose: Convert `objcopy -O verilog` output (one BYTE per token, @ records
#          carry BYTE addresses) into the kestrel TB image format: one 32-bit
#          WORD per line, @ records carry WORD indices, records are sparse so
#          no zero padding is ever emitted. $readmemh into the tb_top word
#          arrays treats @ as the element index, so word-indexed records are
#          the only form the SV loader consumes correctly.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""Normalize objcopy -O verilog byte images into kestrel word-indexed hex.

Usage:
    python3 normalize_hex.py in.hex out.hex [--base 0x80000000]

--base subtracts a link base address (e.g. riscv-tests link at 0x80000000)
from every byte address before word packing; Task 8's rv32ui battery needs
this because the tb_top imem array is indexed from 0.
"""

import argparse
import sys


def load_byte_image(path):
    """Parse objcopy -O verilog byte records into {byte_address: value}."""
    mem = {}
    addr = 0
    with open(path) as fh:
        for line in fh:
            line = line.split("#")[0].strip()
            for tok in line.split():
                if tok.startswith("@"):
                    addr = int(tok[1:], 16)
                else:
                    mem[addr] = int(tok, 16) & 0xFF
                    addr += 1
    return mem


def pack_words(byte_mem):
    """Little-endian pack a byte image into {word_index: 32-bit word}."""
    words = {}
    for addr, val in byte_mem.items():
        idx = addr // 4
        if addr % 4 == 0:
            words[idx] = val
        else:
            words[idx] = words.get(idx, 0) | (val << (8 * (addr % 4)))
    return words


def emit_word_image(words, path):
    """Sparse word-indexed records: @record only where the index jumps."""
    with open(path, "w") as fh:
        prev = None
        for idx in sorted(words):
            if prev is None or idx != prev + 1:
                fh.write("@{:08X}\n".format(idx))
            fh.write("{:08x}\n".format(words[idx] & 0xFFFFFFFF))
            prev = idx


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("src")
    parser.add_argument("dst")
    parser.add_argument("--base", type=lambda s: int(s, 0), default=0,
                        help="link base to subtract from byte addresses")
    args = parser.parse_args(argv)

    byte_mem = load_byte_image(args.src)
    if args.base:
        byte_mem = {a - args.base: v for a, v in byte_mem.items()
                    if a >= args.base}
        if any(a < 0 for a in byte_mem):
            print("error: image contains addresses below the base", file=sys.stderr)
            return 1
    emit_word_image(pack_words(byte_mem), args.dst)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
