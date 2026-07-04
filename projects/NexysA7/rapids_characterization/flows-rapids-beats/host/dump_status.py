#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: dump_status
# Purpose: Read + pretty-print the rapids_char_top HARNESS CSR block over UART:
#          the STATUS bitfield, beat-count totals, scheduler-error words, and the
#          per-channel CRC arrays (GEN_EXPECTED / CHK_ACTUAL / RD / WR).
#
# Usage:
#   source env_python
#   ./dump_status.py --port /dev/ttyUSB1 --channels 4
#
# Author: sean galloway
# Created: 2026-07-04

"""Pretty-print the rapids_char_top status CSRs."""

import argparse
import os
import sys

_HOST_DIR = os.path.dirname(os.path.abspath(__file__))
if _HOST_DIR not in sys.path:
    sys.path.insert(0, _HOST_DIR)

import rapids_char_io as rio  # noqa: E402
from rapids_char_io import RapidsCharIO  # noqa: E402

_STATUS_BITS = [
    ('mon_irq', rio.STATUS_MON_IRQ),
    ('src_idle', rio.STATUS_SRC_IDLE),
    ('snk_idle', rio.STATUS_SNK_IDLE),
    ('gen_busy', rio.STATUS_GEN_BUSY),
    ('gen_done', rio.STATUS_GEN_DONE),
    ('data_error', rio.STATUS_DATA_ERROR),
    ('rd_mem_busy', rio.STATUS_RD_MEM_BUSY),
    ('wr_mem_busy', rio.STATUS_WR_MEM_BUSY),
]

_TOTALS = [
    ('GEN_BEATS_TOTAL', rio.CSR_GEN_BEATS_T),
    ('CHK_BEATS_TOTAL', rio.CSR_CHK_BEATS_T),
    ('PKT_COUNT', rio.CSR_PKT_CNT),
    ('RD_BEATS_TOTAL', rio.CSR_RD_BEATS_T),
    ('WR_BEATS_TOTAL', rio.CSR_WR_BEATS_T),
    ('SRC_SCHED_ERROR', rio.CSR_SRC_SCHERR),
    ('SNK_SCHED_ERROR', rio.CSR_SNK_SCHERR),
]

# Per-channel indexed CRC arrays: (label, data reg @0xA0-0xAC, valid mask reg).
_CRC_ARRAYS = [
    ('GEN_EXPECTED_CRC', rio.CSR_GEN_EXP_CRC, rio.CSR_GEN_EXP_VLD),
    ('CHK_ACTUAL_CRC', rio.CSR_CHK_ACT_CRC, rio.CSR_CHK_ACT_VLD),
    ('RD_CRC_VALUE', rio.CSR_RD_CRC, rio.CSR_RD_CRC_VLD),
    ('WR_CRC_VALUE', rio.CSR_WR_CRC, rio.CSR_WR_CRC_VLD),
]


def _fmt(v):
    return "----" if v is None else f"0x{v:08X}"


def dump(io: RapidsCharIO, num_channels: int) -> None:
    print("=" * 60)
    dev_id = io.csr_read(rio.CSR_ID)
    ok = dev_id == rio.CSR_ID_EXPECTED
    print(f"ID         : {_fmt(dev_id)}  ('RAP1' expected: "
          f"{'OK' if ok else 'MISMATCH'})")

    status = io.read_status()
    print(f"STATUS     : {_fmt(status)}")
    if status is not None:
        flags = [name for name, bit in _STATUS_BITS if status & bit]
        print(f"             [{', '.join(flags) if flags else '-'}]")

    print("-" * 60)
    for name, off in _TOTALS:
        print(f"{name:<16}: {_fmt(io.csr_read(off))}")

    print("-" * 60)
    print(f"Per-channel CRC arrays (0..{num_channels - 1}):")
    # Read the valid masks once.
    valid_masks = {label: (io.csr_read(vld_reg) or 0)
                   for label, _, vld_reg in _CRC_ARRAYS}
    header = "  ch  " + "  ".join(f"{label:<18}" for label, _, _ in _CRC_ARRAYS)
    print(header)
    for ch in range(num_channels):
        io.select_channel(ch)
        cells = []
        for label, crc_reg, _ in _CRC_ARRAYS:
            crc = io.csr_read(crc_reg)
            valid = (valid_masks[label] >> ch) & 0x1
            cells.append(f"{_fmt(crc)}{'*' if valid else ' '}    ")
        print(f"  {ch:<3} " + "".join(cells))
    print("  (* = valid bit set)")
    print("=" * 60)


def parse_args():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--port', default='/dev/ttyUSB1', help='UART device')
    p.add_argument('--baud', type=int, default=115200)
    p.add_argument('--channels', type=int, default=4,
                   help='NUM_CHANNELS the bitstream was built with')
    return p.parse_args()


def main() -> int:
    args = parse_args()
    with RapidsCharIO(port=args.port, baudrate=args.baud) as io:
        dump(io, args.channels)
    return 0


if __name__ == '__main__':
    sys.exit(main())
