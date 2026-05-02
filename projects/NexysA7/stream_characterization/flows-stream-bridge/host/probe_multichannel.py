#!/usr/bin/env python3
# Quick post-run probe: read per-channel CRC registers + beat counts from
# the board after a multi-channel test. Used to tell whether all channels
# actually transferred their data, vs. only ch0 carrying the load while
# ch1+ silently errored out.
#
# Run a 2ch test first, then this script. It reads:
#   0x10  CRC_RD (legacy, ch0 view)
#   0x18  CRC_WR (legacy, ch0 view)
#   0x1C  CRC_MATCH (aggregate)
#   0x60+4*ch  per-channel read CRC
#   0x80+4*ch  per-channel write CRC
#   0xA0  CRC_VALID_MASK
#   0xA4  CRC_MATCH_MASK

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

# REPO_ROOT must be set in the environment (source env_python).
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    raise RuntimeError(
        "REPO_ROOT is not set. Source env_python (or export REPO_ROOT) "
        "before running this script."
    )
sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))

from uart_axi_bridge import UARTAxiBridge  # noqa: E402

HARNESS_CSR_BASE       = 0x0001_0000
CSR_CRC_RD_EXPECTED    = HARNESS_CSR_BASE + 0x10
CSR_CRC_WR_EXPECTED    = HARNESS_CSR_BASE + 0x14
CSR_CRC_WR_COMPUTED    = HARNESS_CSR_BASE + 0x18
CSR_CRC_MATCH          = HARNESS_CSR_BASE + 0x1C
CSR_CRC_RD_PER_CH_BASE = HARNESS_CSR_BASE + 0x60
CSR_CRC_WR_PER_CH_BASE = HARNESS_CSR_BASE + 0x80
CSR_CRC_VALID_MASK     = HARNESS_CSR_BASE + 0xA0
CSR_CRC_MATCH_MASK     = HARNESS_CSR_BASE + 0xA4


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--port", required=True)
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--num-channels", type=int, default=4,
                   help="Number of channels to read (default 4)")
    args = p.parse_args()

    with UARTAxiBridge(args.port, args.baud) as br:
        legacy_rd  = br.read(CSR_CRC_RD_EXPECTED)
        legacy_wr  = br.read(CSR_CRC_WR_COMPUTED)
        legacy_mr  = br.read(CSR_CRC_MATCH)
        valid_mask = br.read(CSR_CRC_VALID_MASK) or 0
        match_mask = br.read(CSR_CRC_MATCH_MASK) or 0

        print(f"Legacy (0x10/0x18/0x1C):  rd=0x{(legacy_rd or 0):08X}  "
              f"wr=0x{(legacy_wr or 0):08X}  match_reg=0x{(legacy_mr or 0):08X}")
        print(f"VALID_MASK (0xA0): 0x{valid_mask:08X}")
        print(f"MATCH_MASK (0xA4): 0x{match_mask:08X}")
        print()
        print(f"  ch  rd_crc      wr_crc      valid  match")
        print(f"  --  ----------  ----------  -----  -----")
        for ch in range(args.num_channels):
            rd = br.read(CSR_CRC_RD_PER_CH_BASE + 4 * ch)
            wr = br.read(CSR_CRC_WR_PER_CH_BASE + 4 * ch)
            v = (valid_mask >> ch) & 1
            m = (match_mask >> ch) & 1
            print(f"  {ch:2d}  0x{(rd or 0):08X}  0x{(wr or 0):08X}    "
                  f"{v}      {m}")


if __name__ == "__main__":
    main()
