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
# REPO_ROOT must be set in the environment (source env_python).
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    raise RuntimeError(
        "REPO_ROOT is not set. Source env_python (or export REPO_ROOT) "
        "before running this script."
    )
sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))
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

# desc_ram observation counters (see harness_csr.sv 0xE0..0xFC). 32-bit
# saturating; clear on CTRL.clear_stats. The AR/R pair is the primary
# decoder for "is the SRAM responding or is STREAM not accepting?".
CSR_DESC_AR_HS    = HARNESS_CSR_BASE + 0xE0
CSR_DESC_AR_STALL = HARNESS_CSR_BASE + 0xE4
CSR_DESC_R_HS     = HARNESS_CSR_BASE + 0xE8
CSR_DESC_R_STALL  = HARNESS_CSR_BASE + 0xEC
CSR_DESC_AW_HS    = HARNESS_CSR_BASE + 0xF0
CSR_DESC_W_HS     = HARNESS_CSR_BASE + 0xF4
CSR_DESC_B_HS     = HARNESS_CSR_BASE + 0xF8
CSR_DESC_VR_LIVE  = HARNESS_CSR_BASE + 0xFC

# desc_ram o_dbg_vr live bit labels (bit -> short name, used for decode).
DESC_VR_BITS = [
    (0,  "axil_awvalid"), (1,  "axil_awready"),
    (2,  "axil_wvalid"),  (3,  "axil_wready"),
    (4,  "axil_bvalid"),  (5,  "axil_bready"),
    (6,  "axil_arvalid"), (7,  "axil_arready"),
    (8,  "axil_rvalid"),  (9,  "axil_rready"),
    (10, "axi_arvalid"),  (11, "axi_arready"),
    (12, "axi_rvalid"),   (13, "axi_rready"),
]

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

# STREAM channel-observation mux. Host writes OBS_CTRL with the channel
# and category to probe, then reads the three OBS_* status registers.
# bit [2:0] = ch_sel, bit [4:3] = cat_sel.
APB_OBS_CTRL       = STREAM_APB_BASE + 0x2C0
APB_OBS_FLAGS      = STREAM_APB_BASE + 0x2C4
APB_OBS_DATA0      = STREAM_APB_BASE + 0x2C8
APB_OBS_DATA1      = STREAM_APB_BASE + 0x2CC

# OBS_FLAGS bit layout (see stream_core.sv obs mux block)
OBS_FLAG_BITS = [
    # bit, label
    (7,  "sched_rd_valid"),
    (8,  "sched_wr_valid"),
    (9,  "sched_wr_ready"),
    (10, "sched_rd_err"),
    (11, "sched_wr_err"),
    (12, "sched_error"),
    (13, "desc_engine_idle"),
    (14, "scheduler_idle"),
    (15, "ch_enable"),
    (16, "rd_all_complete"),
    (17, "wr_all_complete"),
    (18, "STK:desc_err"),
    (19, "STK:rd_err"),
    (20, "STK:wr_err"),
    (21, "timeout_expired"),
]

OBS_CAT_NAMES = {0: "status", 1: "rd_addr", 2: "wr_addr", 3: "sram"}


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

        print("\n=== desc_ram observation (host AXIL writes / STREAM AXI4 reads) ===")
        ar_hs   = rd(b, CSR_DESC_AR_HS,    "DESC_AR_HS")
        ar_st   = rd(b, CSR_DESC_AR_STALL, "DESC_AR_STALL")
        r_hs    = rd(b, CSR_DESC_R_HS,     "DESC_R_HS")
        r_st    = rd(b, CSR_DESC_R_STALL,  "DESC_R_STALL")
        rd(b, CSR_DESC_AW_HS, "DESC_AW_HS")
        rd(b, CSR_DESC_W_HS,  "DESC_W_HS")
        rd(b, CSR_DESC_B_HS,  "DESC_B_HS")
        live = rd(b, CSR_DESC_VR_LIVE, "DESC_VR_LIVE")

        if live is not None:
            asserted = [name for bit, name in DESC_VR_BITS if live & (1 << bit)]
            print(f"    live asserted: {', '.join(asserted) if asserted else '(none)'}")

        # ---- STREAM channel-observation mux ----
        # Walk all 8 channels under each of the 4 categories, printing the
        # decoded obs_flags + the two cat-dependent data words. This is the
        # primary tool for answering "why is ch0 stuck?" since the mux
        # surfaces scheduler FSM state, read/write valid/ready, beats
        # remaining, addresses, and per-channel SRAM occupancy.
        print("\n=== STREAM channel-observation mux (0x2C0..0x2CC) ===")
        for ch in range(8):
            for cat in range(4):
                b.write(APB_OBS_CTRL, (cat << 3) | (ch & 0x7))
                flags = b.read(APB_OBS_FLAGS)
                d0    = b.read(APB_OBS_DATA0)
                d1    = b.read(APB_OBS_DATA1)
                cat_name = OBS_CAT_NAMES.get(cat, f"cat{cat}")
                state = flags & 0x7F
                hot_bits = [name for bit, name in OBS_FLAG_BITS if flags & (1 << bit)]
                if cat == 0:
                    print(f"  ch{ch} {cat_name:<7}  state={state:#04x}  "
                          f"rd_beats={d0:#x}  wr_beats={d1:#x}  "
                          f"flags=[{', '.join(hot_bits)}]")
                elif cat == 1:
                    print(f"  ch{ch} {cat_name:<7}  src_addr=0x{d1:08X}{d0:08X}")
                elif cat == 2:
                    print(f"  ch{ch} {cat_name:<7}  dst_addr=0x{d1:08X}{d0:08X}")
                elif cat == 3:
                    print(f"  ch{ch} {cat_name:<7}  rd_space_free={d0}  wr_data_avail={d1}")

        # Diagnose where the desc path is stuck. If you only see one of
        # these prints, that's the loudest signal.
        if ar_hs is not None and ar_hs == 0 and ar_st is not None and ar_st > 0:
            print(f"** desc_ram never granted AR ({ar_st} stall cycles) "
                  "— SRAM stuck or upstream arbiter blocking.")
        elif ar_hs is not None and ar_hs > 0 and r_hs is not None and r_hs == 0:
            print(f"** desc_ram accepted {ar_hs} AR but produced 0 R "
                  "— SRAM is the bottleneck.")
        elif r_hs is not None and r_st is not None and r_st > 0 and r_hs > 0 \
                and r_st > r_hs * 4:
            print(f"** STREAM stalled R for {r_st} cycles vs {r_hs} delivered "
                  "— STREAM read path / desc skid full.")

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
