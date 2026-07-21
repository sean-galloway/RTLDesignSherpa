#!/usr/bin/env python3
"""Train the per-64b-beat read DESKEW on the board (PHY_TIMING.deskew_lo/hi).

The a7ddrphy returns the two 64b beats of a 128b DFI word at DIFFERENT capture
latencies (the two packed sub-reads arrive skewed in time), so a single whole-word
capture takes one beat correct and the other STALE -> exactly 2-of-4 device-words
wrong, EVERY read, INVARIANT to rddata_delay (which shifts both beats together and
so can never fix a skew BETWEEN them — why A7Leveling found "no passing tap").

deskew_lo/hi independently delay the LOW/HIGH beat capture (0..3 DFI cycles) to
realign the two beats. This sweeps deskew_lo x deskew_hi, writing a PHASE-DISTINCT
pattern once and reading it back at each combo, and reports beats_mismatched. The
(lo,hi) where it drops to 0 is the trained deskew — structural + stable, so bake it
into the programs (expected ~deskew_lo=0, deskew_hi=1). Runtime, no rebuild.

    python3 host/train_deskew.py [--port /dev/ttyUSB2] [--max 3]

CRITICAL: uses a PHASE-DISTINCT data pattern (data_mode counter), never an aliased
a5a0-repeat that can make a stale/shifted beat equal the expected beat and hide the
skew (the a5a0 trap that wasted a debug session). See TASK-DESKEW.
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

SEED = 0x1234_5678   # counter/hash seed -> phase-distinct device words


def _read_mism(d, deskew_lo, deskew_hi):
    d.set_deskew(deskew_lo=deskew_lo, deskew_hi=deskew_hi)
    d.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=8, stride_0=32,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.clear_stats(); d.start_rd(); wait_engine(d, "rd")
    return d.beats_mismatched()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--max", type=int, default=3, help="max deskew per beat (0..3)")
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}", flush=True)

    # Board known-good bring-up point (deskew is orthogonal to these).
    d.soft_reset(); time.sleep(0.01)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=0,
                         t_rddata_en=6, rd_in_order=True)
    d.set_dfi_phase(rd_phase=0, wr_phase=0)
    d.set_dfi_rddata_delay(8)

    # Write the phase-distinct pattern ONCE (writes land regardless of deskew).
    d.clear_stats()
    d.program_wr_engine(start_addr=0x0, burst_len=8, txn_count=8, stride_0=32,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.start_wr(); wait_engine(d, "wr")

    best, grid = None, {}
    print(f"     {'  '.join(f'hi={h}' for h in range(args.max + 1))}")
    for lo in range(args.max + 1):
        row = []
        for hi in range(args.max + 1):
            mm = _read_mism(d, lo, hi)
            grid[(lo, hi)] = mm
            row.append(mm)
            if mm == 0 and best is None:
                best = (lo, hi)
            time.sleep(0.02)
        print(f"lo={lo}  " + "  ".join(f"{m:>4}" for m in row), flush=True)

    if best is not None:
        d.set_deskew(deskew_lo=best[0], deskew_hi=best[1])
        print(f"\nPASS: reads CLEAN at deskew_lo={best[0]} deskew_hi={best[1]} "
              f"(beats_mismatched=0). Bake into the programs / A7Leveling.")
    else:
        print("\nNo (lo,hi) gave clean reads. If the diagonal shows ~2/4 at every "
              "combo, the skew is > the deskew range (widen DESKEW_W) or the fault "
              "is not a per-beat skew — re-ILA the raw dfi_rddata two 64b halves.")


if __name__ == "__main__":
    main()
