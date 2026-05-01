#!/usr/bin/env python3
# Quick status dump for a hung stream_char run on the FPGA.
# Usage:  python3 host/dump_status.py [--port /dev/ttyUSB1]
#
# Reads a handful of useful registers without disturbing state and prints
# them with bit-decode hints so we can see where the DMA is stuck.

import argparse
import os
import sys

from descriptor_builder import HARNESS_CSR_BASE, STREAM_APB_BASE

# Pull in the same UARTAxiBridge the runner uses.
sys.path.insert(0, os.path.abspath(os.path.join(
    os.path.dirname(__file__), "../../../components/converters/bin")))
from uart_axi_bridge import UARTAxiBridge

# Harness CSR offsets (mirror of run_characterization.py)
CSR_CTRL          = HARNESS_CSR_BASE + 0x00
CSR_STATUS        = HARNESS_CSR_BASE + 0x04
CSR_DBG_WR_PTR    = HARNESS_CSR_BASE + 0x08
CSR_DBG_OVERFLOW  = HARNESS_CSR_BASE + 0x0C
CSR_CRC_RD_EXP    = HARNESS_CSR_BASE + 0x10
CSR_CRC_WR_EXP    = HARNESS_CSR_BASE + 0x14
CSR_CRC_WR_COMP   = HARNESS_CSR_BASE + 0x18
CSR_CRC_MATCH     = HARNESS_CSR_BASE + 0x1C
CSR_BUILD_ID      = HARNESS_CSR_BASE + 0x24

# STREAM APB offsets (from stream_regmap.py)
APB_GLOBAL_CTRL    = STREAM_APB_BASE + 0x100
APB_GLOBAL_STATUS  = STREAM_APB_BASE + 0x104
APB_CHANNEL_ENABLE = STREAM_APB_BASE + 0x120
APB_CHANNEL_RESET  = STREAM_APB_BASE + 0x124
APB_SCHED_CONFIG   = STREAM_APB_BASE + 0x204
APB_SCHED_ERROR    = STREAM_APB_BASE + 0x170
APB_MON_FIFO_STAT  = STREAM_APB_BASE + 0x180
APB_DESCENG_CFG    = STREAM_APB_BASE + 0x220
APB_AXI_XFER_CFG   = STREAM_APB_BASE + 0x2A0


def rd(b, addr, label):
    val = b.read(addr)
    print(f"  {label:<22} @ 0x{addr:08X}  =  "
          f"{('--------' if val is None else f'0x{val:08X}')}")
    return val


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB1")
    ap.add_argument("--baud", type=int, default=115200)
    args = ap.parse_args()

    with UARTAxiBridge(args.port, args.baud) as b:
        print("=== Harness CSRs ===")
        bid = rd(b, CSR_BUILD_ID,     "BUILD_ID")
        sts = rd(b, CSR_STATUS,       "CSR_STATUS")
        rd(b, CSR_DBG_WR_PTR,         "DBG_WR_PTR")
        rd(b, CSR_DBG_OVERFLOW,       "DBG_OVERFLOW")
        rd(b, CSR_CRC_RD_EXP,         "CRC_RD_EXPECTED")
        rd(b, CSR_CRC_WR_EXP,         "CRC_WR_EXPECTED")
        rd(b, CSR_CRC_WR_COMP,        "CRC_WR_COMPUTED")
        rd(b, CSR_CRC_MATCH,          "CRC_MATCH")

        if sts is not None:
            print(f"    bits: irq={(sts>>0)&1}  "
                  f"err={(sts>>1)&1}  overflow={(sts>>2)&1}")

        print("\n=== STREAM APB ===")
        rd(b, APB_GLOBAL_CTRL,    "GLOBAL_CTRL")
        gs  = rd(b, APB_GLOBAL_STATUS,  "GLOBAL_STATUS")
        rd(b, APB_CHANNEL_ENABLE, "CHANNEL_ENABLE")
        rd(b, APB_CHANNEL_RESET,  "CHANNEL_RESET")
        rd(b, APB_SCHED_CONFIG,   "SCHED_CONFIG")
        se  = rd(b, APB_SCHED_ERROR,    "SCHED_ERROR")
        mfs = rd(b, APB_MON_FIFO_STAT,  "MON_FIFO_STATUS")
        rd(b, APB_DESCENG_CFG,    "DESCENG_CONFIG")
        rd(b, APB_AXI_XFER_CFG,   "AXI_XFER_CONFIG")

        # Channel kick-LOW (read-back is just the value last written)
        print("\n=== Channel kick LOW words (last written values) ===")
        for ch in range(8):
            rd(b, STREAM_APB_BASE + ch * 0x08, f"CH{ch}_KICK_LO")

        print()
        if sts is not None and (sts & 0x02):
            print("** CSR_STATUS error bit set — design flagged an error.")
        if mfs is not None and (mfs != 0):
            print(f"** MON_FIFO_STATUS = 0x{mfs:08X} (non-zero) "
                  "— monitor bus has packets queued.")
        if se is not None and (se != 0):
            print(f"** SCHED_ERROR = 0x{se:08X} — scheduler reported error.")
        if gs is not None and (gs != 0):
            print(f"** GLOBAL_STATUS = 0x{gs:08X} — see stream_regmap.py "
                  "GLOBAL_STATUS for bit decode.")


if __name__ == "__main__":
    sys.exit(main() or 0)
