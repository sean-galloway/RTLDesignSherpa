#!/usr/bin/env python3
"""Board bring-up: find the DFI read/write latency alignment at 300 MT/s.

The nphases=2 / CL-3 / CWL-2 build fixed the write stall (wr_done now
asserts), but reads still error pre-alignment. The A7DDRPHY read-data
capture is closed-loop on dfi_rddata_valid, so t_rddata_en only has to
place dfi_rddata_en in the right window; t_phy_wrlat places wrdata_en.
Their correct values are a pumice-internal pipeline offset (not the raw
LiteDRAM read_latency=8), so we sweep them empirically here.

We pin the analog DQ eye at LiteDRAM's proven point (read bitslip 3,
IDELAY tap ~22 on both x16 lanes) and sweep t_phy_wrlat x t_rddata_en,
reporting beats_mismatched for a small write-then-read at each point.
The (wrlat, rden) with zero mismatches is the alignment; feed it into
A7Leveling/SimpleTest afterwards.
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

LANES = 0b11          # x16 -> both byte lanes together
EYE_BITSLIP = 3       # LiteDRAM's winning read bitslip on this board
EYE_TAP = 22          # LiteDRAM's centred IDELAY tap (m0 23+-8 / m1 22+-8)


def strobe(drv: DDR2CharDriver, knob: int) -> None:
    """dly_sel-bracketed PHY strobe (the PHY gates rdly/bitslip by dly_sel)."""
    drv.phy_poke(dc.PHY_DLY_SEL, LANES)
    drv.phy_poke(knob, 1)
    drv.phy_poke(dc.PHY_DLY_SEL, 0)


def set_analog_eye(drv: DDR2CharDriver, bitslip: int, tap: int) -> None:
    """Reset the read path then advance to (bitslip, tap). Persists across
    soft_reset, so we set it once before the latency sweep."""
    strobe(drv, dc.PHY_RDLY_DQ_RST)
    strobe(drv, dc.PHY_RDLY_DQ_BITSLIP_RST)
    for _ in range(bitslip):
        strobe(drv, dc.PHY_RDLY_DQ_BITSLIP)
    for _ in range(tap):
        strobe(drv, dc.PHY_RDLY_DQ_INC)


def try_point(drv: DDR2CharDriver, wrlat: int, rden: int, base: int,
              blen: int, txn: int, seed: int) -> int:
    """soft_reset -> cfg(wrlat,rden) -> write pattern -> read; return
    beats_mismatched (or -1 if the write itself never completed)."""
    drv.soft_reset()
    time.sleep(0.005)
    drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=wrlat,
                           t_rddata_en=rden, rd_in_order=True)
    drv.clear_stats()
    drv.program_wr_engine(start_addr=base, burst_len=blen, txn_count=txn,
                          stride_0=blen * 8, lfsr_seed=seed, data_mode=True,
                          hash_seed0=seed)
    drv.start_wr()
    if not wait_engine(drv, "wr"):
        return -1
    drv.program_rd_engine(start_addr=base, burst_len=blen, txn_count=txn,
                          stride_0=blen * 8, lfsr_seed=seed, data_mode=True,
                          hash_seed0=seed)
    drv.clear_stats()
    drv.start_rd()
    wait_engine(drv, "rd")   # rd_error on mismatch is fine; the metric is beats
    return drv.beats_mismatched()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--bitslip", type=int, default=EYE_BITSLIP)
    ap.add_argument("--tap", type=int, default=EYE_TAP)
    ap.add_argument("--wrlat", default="0,1,2,3,4",
                    help="comma list of t_phy_wrlat to sweep")
    ap.add_argument("--rden", default="1,2,3,4,5,6,7,8,9,10,11,12",
                    help="comma list of t_rddata_en to sweep")
    ap.add_argument("--blen", type=int, default=4)
    ap.add_argument("--txn", type=int, default=4)
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=0x1EAFF00D)
    args = ap.parse_args()

    wrlats = [int(x) for x in args.wrlat.split(",")]
    rdens = [int(x) for x in args.rden.split(",")]

    drv = DDR2CharDriver(port=args.port, baudrate=args.baud)
    bid = drv.build_id()
    print(f"BUILD_ID=0x{bid:08X} ({'DDR2 OK' if bid == drv.BUILD_ID_MAGIC else 'UNEXPECTED'})")

    # Init once, then pin the analog eye (persists across soft_reset).
    drv.soft_reset()
    time.sleep(0.01)
    drv.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=2,
                           t_rddata_en=6, rd_in_order=True)
    drv.clear_stats()
    print(f"pinning analog eye: read bitslip={args.bitslip}, IDELAY tap={args.tap}")
    set_analog_eye(drv, args.bitslip, args.tap)

    print(f"\nsweeping t_phy_wrlat x t_rddata_en (blen={args.blen}, txn={args.txn}):")
    header = "wrlat\\rden " + " ".join(f"{r:>4}" for r in rdens)
    print(header)
    best = None
    for wl in wrlats:
        cells = []
        for rd in rdens:
            mm = try_point(drv, wl, rd, 0x0, args.blen, args.txn, args.seed)
            cells.append("  wr" if mm < 0 else f"{mm:>4}")
            if mm == 0 and best is None:
                best = (wl, rd)
        print(f"{wl:>9} " + " ".join(cells))

    print()
    if best:
        print(f"*** ALIGNED at t_phy_wrlat={best[0]}, t_rddata_en={best[1]} "
              f"(0 beats mismatched) ***")
    else:
        print("No (wrlat,rden) gave 0 mismatches at this eye. Next: sweep the "
              "analog eye (bitslip/tap) too, or widen the latency ranges.")


if __name__ == "__main__":
    main()
