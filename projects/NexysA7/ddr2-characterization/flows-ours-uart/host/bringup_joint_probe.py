#!/usr/bin/env python3
"""Coarse JOINT (t_phy_wrlat, t_rddata_en, bitslip) probe at a fixed mid tap.

A7Leveling swept (bitslip, tap) at FIXED wrlat=4/rden=6 and found no eye, yet
reads capture data (rd_prod=8). So the fixed write/read-gate latency is wrong,
and the eye search can't see it. This probe sweeps the two latency knobs and,
for each, does an inner bitslip scan at one mid IDELAY tap, reporting the MIN
beats_mismatched found. Any cell < full (blen*txn) means that (wrlat, rden,
bitslip) aligns the gate -> refine tap there with A7Leveling/the tap sweep.
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

LANES = 0b11


def strobe(drv, knob):
    drv.phy_poke(dc.PHY_DLY_SEL, LANES)
    drv.phy_poke(knob, 1)
    drv.phy_poke(dc.PHY_DLY_SEL, 0)


def set_tap(drv, tap):
    """Reset read path (tap 0, bitslip 0) then advance IDELAY to `tap`."""
    strobe(drv, dc.PHY_RDLY_DQ_BITSLIP_RST)
    strobe(drv, dc.PHY_RDLY_DQ_RST)
    for _ in range(tap):
        strobe(drv, dc.PHY_RDLY_DQ_INC)


def one_test(drv, wrlat, rden, base, blen, txn, seed):
    drv.soft_reset()
    time.sleep(0.004)
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
    wait_engine(drv, "rd")
    return drv.beats_mismatched()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--wrlat", default="0,1,2,3")
    ap.add_argument("--rden", default="5,6,7,8,9")
    ap.add_argument("--tap", type=int, default=16)
    ap.add_argument("--blen", type=int, default=4)
    ap.add_argument("--txn", type=int, default=2)
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=0x1EAFF00D)
    args = ap.parse_args()

    wrlats = [int(x) for x in args.wrlat.split(",")]
    rdens = [int(x) for x in args.rden.split(",")]
    total = args.blen * args.txn

    drv = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{drv.build_id():08X}  (full-mismatch = {total} beats)")
    print(f"inner bitslip scan (0..7) at IDELAY tap={args.tap}; cell = min beats over bitslips (bitslip@min)\n")

    header = "wrlat\\rden " + " ".join(f"{r:>7}" for r in rdens)
    print(header)
    hits = []
    for wl in wrlats:
        cells = []
        for rd in rdens:
            best_mm, best_bs = total + 1, -1
            for bs in range(8):
                set_tap(drv, args.tap)
                for _ in range(bs):
                    strobe(drv, dc.PHY_RDLY_DQ_BITSLIP)
                mm = one_test(drv, wl, rd, 0x0, args.blen, args.txn, args.seed)
                if 0 <= mm < best_mm:
                    best_mm, best_bs = mm, bs
                if mm == 0:
                    break
            cells.append(f"{best_mm:>3}@b{best_bs}" if best_bs >= 0 else "  wr")
            if best_mm < total:
                hits.append((wl, rd, best_bs, best_mm))
        print(f"{wl:>9} " + " ".join(cells))

    print()
    if hits:
        hits.sort(key=lambda h: h[3])
        print("PROMISING (below full mismatch):")
        for wl, rd, bs, mm in hits[:10]:
            print(f"  wrlat={wl} rden={rd} bitslip={bs} -> {mm} beats mismatched")
    else:
        print("Every (wrlat,rden,bitslip) still full-mismatch at this tap. "
              "The data read back never partially matches -> writes likely not "
              "landing correctly in DRAM (analog write path), not a read-gate issue.")


if __name__ == "__main__":
    main()
