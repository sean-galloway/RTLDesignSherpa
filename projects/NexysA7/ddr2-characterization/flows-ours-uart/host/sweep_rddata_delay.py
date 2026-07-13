#!/usr/bin/env python3
"""Sweep DFI_TUNING.rddata_delay on the board and report read integrity.

The on-silicon ILA showed the a7ddrphy presents read DATA ~read_latency cycles
before its rddata_valid, so pumice (valid-gated capture) latches zeros. The
runtime dfi_rddata_delay realigns data to the late valid. This sweeps the delay
0..15, writing a known pattern once and reading it back at each delay, and
reports beats_mismatched per setting — the value where it drops to 0 is the
PHY read_latency (expected ~8). Runtime knob, no rebuild between points.

    python3 host/sweep_rddata_delay.py [--port /dev/ttyUSB2]
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

SEED = 0xA5A5_1234


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--lo", type=int, default=0)
    ap.add_argument("--hi", type=int, default=15)
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)

    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X} cmd_delay={d.get_dfi_cmd_delay()}",
          flush=True)
    d.soft_reset(); time.sleep(0.01)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=0,
                         t_rddata_en=6, rd_in_order=True)
    # a7ddrphy rdphase=1: place the READ command on DFI phase 1 so the whole BL4
    # burst (both DFI cycles) returns aligned. Without this only the first DFI
    # cycle reads correctly (8/16). See project_ddr2_ila_read_valid_skew.
    d.set_dfi_phase(rd_phase=1, wr_phase=0)

    # Write the known pattern once (writes land regardless of read delay).
    d.clear_stats()
    d.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=4, stride_0=32,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.start_wr(); wait_engine(d, "wr")

    best = None
    print(f"{'rddly':>5}  {'beats_mismatched':>16}")
    for dly in range(args.lo, args.hi + 1):
        d.set_dfi_rddata_delay(dly)
        d.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=4, stride_0=32,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.clear_stats(); d.start_rd(); wait_engine(d, "rd")
        mm = d.beats_mismatched()
        flag = "  <-- CLEAN" if mm == 0 else ""
        print(f"{dly:>5}  {mm:>16}{flag}", flush=True)
        if mm == 0 and best is None:
            best = dly
        time.sleep(0.02)

    if best is not None:
        print(f"\nPASS: reads clean at rddata_delay={best} "
              f"(= a7ddrphy read_latency). Bake this into the programs.")
    else:
        print("\nNo delay gave clean reads — widen the sweep or re-check "
              "t_rddata_en / the ILA capture.")


if __name__ == "__main__":
    main()
