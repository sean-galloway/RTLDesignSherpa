#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Dump the descriptor chain that DescriptorBuilder produces for a given
# config, in a reviewable per-descriptor form. Reads the host-side
# write list (== what would land in desc_ram, as already verified by
# verify_desc_ram_writeback.py), reassembles each 256-bit descriptor
# from its 8 word writes, and prints the fields.

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from descriptor_builder import DescriptorBuilder, CharConfig


# Descriptor field layout (per descriptor_builder + STREAM):
#   Word 0: src_addr[31:0]
#   Word 1: src_addr[63:32]
#   Word 2: dst_addr[31:0]
#   Word 3: dst_addr[63:32]
#   Word 4: length (in BEATS)
#   Word 5: next_descriptor_ptr
#   Word 6: ctrl    bit0=valid, bit1=interrupt, bit2=last,
#                    bits[7:4]=channel_id, bits[23:8]=stamp/priority byte
#   Word 7: reserved


def collect_descriptors(writes):
    """Group flat (addr, data) tuples into 8-word descriptor records,
    keyed by descriptor base address (word 0's addr)."""
    descs = {}
    for addr, data in writes:
        base = addr & ~0x1F        # 32B align
        word_idx = (addr & 0x1F) >> 2
        descs.setdefault(base, [None] * 8)[word_idx] = data
    return descs


def fmt_field(name, value, width=20):
    return f"    {name:<{width}}:    {value}"


def print_descriptor(idx, base_addr, words):
    src_addr = (words[1] << 32) | words[0]
    dst_addr = (words[3] << 32) | words[2]
    length   = words[4]
    next_ptr = words[5]
    ctrl     = words[6]
    reserved = words[7]

    valid     = (ctrl >> 0) & 0x1
    interrupt = (ctrl >> 1) & 0x1
    last      = (ctrl >> 2) & 0x1
    error     = (ctrl >> 3) & 0x1
    channel   = (ctrl >> 4) & 0xF
    priority  = (ctrl >> 8) & 0xFF
    stamp     = (ctrl >> 16) & 0xFFFF

    print("=" * 72)
    print(f"Descriptor #{idx:<3} (channel {channel}) @ host addr "
          f"0x{base_addr:08X}")
    print("=" * 72)
    print(fmt_field("src_addr",            f"0x{src_addr:016X}"))
    print(fmt_field("dst_addr",            f"0x{dst_addr:016X}"))
    print(fmt_field("length (beats)",      f"{length}  (0x{length:08X})"))
    print(fmt_field("next_descriptor_ptr", f"0x{next_ptr:08X}"))
    print(fmt_field("ctrl word",           f"0x{ctrl:08X}"))
    print(fmt_field("  valid",             f"{valid}"))
    print(fmt_field("  interrupt",         f"{interrupt}"))
    print(fmt_field("  last",              f"{last}"))
    print(fmt_field("  error",             f"{error}"))
    print(fmt_field("  channel_id",        f"{channel}"))
    print(fmt_field("  priority",          f"0x{priority:02X}"))
    print(fmt_field("  stamp / top16",     f"0x{stamp:04X}"))
    print(fmt_field("reserved",            f"0x{reserved:08X}"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--name',          default='16desc_7ch_1MB')
    parser.add_argument('--channels',      type=int, default=7)
    parser.add_argument('--descriptors',   type=int, default=16)
    parser.add_argument('--transfer-bytes', type=int, default=1024 * 1024)
    parser.add_argument('--data-width',    type=int, default=128)
    args = parser.parse_args()

    builder = DescriptorBuilder(data_width=args.data_width)
    cfg = CharConfig(
        name=args.name,
        num_channels=args.channels,
        descriptors_per_channel=args.descriptors,
        transfer_bytes=args.transfer_bytes,
    )
    test_data = builder.build_test(cfg)
    writes = test_data['descriptor_writes']

    print(f"Config:     {args.name}")
    print(f"Channels:   {args.channels}")
    print(f"Desc/Ch:    {args.descriptors}")
    print(f"Xfer bytes: {args.transfer_bytes}")
    print(f"Data width: {args.data_width} bits  ->  "
          f"{args.transfer_bytes // (args.data_width // 8)} beats/desc")
    print()

    descs = collect_descriptors(writes)
    # Sort by host address, which is also the in-memory order.
    for idx, base in enumerate(sorted(descs.keys())):
        words = descs[base]
        if any(w is None for w in words):
            print(f"  [WARN] Descriptor at 0x{base:08X} has unwritten words: "
                  f"{[i for i, w in enumerate(words) if w is None]}")
            continue
        print_descriptor(idx, base, words)
    print("=" * 72)
    print(f"Total descriptors: {len(descs)}")


if __name__ == '__main__':
    main()
