#!/usr/bin/env python3
"""Validate BL8 board reads at the current DRAM rate via the level-then-skew
flow, then a LONG write/read-back integrity pass.

Order is fixed (learned on silicon): leveling AND skew detection must ALWAYS be
done, in that composed order --
  1. deskew find at a known-good eye point (bitslip/tap held), sweeping
     deskew_lo x deskew_hi 0..MAX.  bitslip/tap align DQ *bits within a beat*;
     deskew aligns the two 64b *beats to each other* -- independent layers, so
     the eye search below only converges once the beat-to-beat deskew is right.
  2. deskew-AWARE leveling: centre the read IDELAY tap with the trained deskew
     applied (A7Leveling re-applies deskew every reinit).
  3. LONG batch write, then read it all back; PASS iff beats_mismatched == 0.

DESKEW_W was widened 1->2 in the board build so deskew_lo/hi reach 0..3 DFI
cycles: the lower board rate pushed the per-beat read skew past 1 cycle, which
the old 1-bit field could not express (48/64 read floor invariant to a 0..1
deskew sweep).  Usage:
    python3 host/validate_reads.py [--port /dev/ttyUSB2] [--max 3]
                                   [--eye-bitslip 0] [--eye-tap 8]
                                   [--txn 256] [--blen 8]
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import A7Leveling, wait_engine

SEED = 0x1EAF_F00D


def _mism_at(d: DDR2CharDriver, base: int, blen: int, txn: int,
             deskew_lo: int, deskew_hi: int) -> int:
    """Set deskew, read back the pre-written pattern, return beats_mismatched."""
    d.set_deskew(deskew_lo=deskew_lo, deskew_hi=deskew_hi)
    d.program_rd_engine(start_addr=base, burst_len=blen, txn_count=txn,
                        stride_0=blen * 8, lfsr_seed=SEED, data_mode=True,
                        hash_seed0=SEED)
    d.clear_stats()
    d.start_rd()
    wait_engine(d, "rd")
    return d.beats_mismatched()


def find_deskew(d: DDR2CharDriver, base: int, blen: int, txn: int,
                dmax: int) -> tuple[int, int, int]:
    """Sweep deskew_lo x deskew_hi 0..dmax at the fixed eye point; return the
    (lo, hi, mism) with the fewest mismatched beats (0 == clean)."""
    # Write the phase-distinct pattern ONCE (writes land regardless of deskew).
    d.clear_stats()
    d.program_wr_engine(start_addr=base, burst_len=blen, txn_count=txn,
                        stride_0=blen * 8, lfsr_seed=SEED, data_mode=True,
                        hash_seed0=SEED)
    d.start_wr()
    if not wait_engine(d, "wr"):
        print("[validate] WARNING: write engine did not complete")
    best = (0, 0, 1 << 30)
    print("       " + "  ".join(f"hi={h}" for h in range(dmax + 1)))
    for lo in range(dmax + 1):
        row = []
        for hi in range(dmax + 1):
            mm = _mism_at(d, base, blen, txn, lo, hi)
            row.append(mm)
            if mm < best[2]:
                best = (lo, hi, mm)
            time.sleep(0.02)
        print(f"lo={lo}  " + "  ".join(f"{m:>5}" for m in row), flush=True)
    print(f"[validate] best deskew_lo={best[0]} deskew_hi={best[1]} "
          f"mism={best[2]}", flush=True)
    return best


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0)
    ap.add_argument("--max", type=int, default=3, help="max deskew per beat (0..3)")
    ap.add_argument("--eye-bitslip", type=int, default=0)
    ap.add_argument("--eye-tap", type=int, default=8)
    ap.add_argument("--blen", type=int, default=8, help="AXI burst_len (AxLEN)")
    ap.add_argument("--txn", type=int, default=256, help="long-validation txns")
    ap.add_argument("--deskew-txn", type=int, default=8, help="deskew-find txns")
    args = ap.parse_args()

    args.port = dc.autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}", flush=True)

    # ---- base bring-up point (rd_phase=0, rddata_delay=8, wrlat=0, rden=6) ----
    d.soft_reset(); time.sleep(0.01)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=0,
                         t_rddata_en=6, rd_in_order=True)
    d.set_dfi_phase(rd_phase=0, wr_phase=0)
    d.set_dfi_rddata_delay(8)

    # ---- 1. hold a known eye point, find the beat-to-beat deskew ----
    lv = A7Leveling(d, base_addr=args.base, burst_len=args.blen, rd_phase=0,
                    rddata_delay=8, t_phy_wrlat=0, t_rddata_en=6, verbose=False)
    print(f"[validate] applying eye point bitslip={args.eye_bitslip} "
          f"tap={args.eye_tap} for deskew find", flush=True)
    lv.apply_taps(args.eye_bitslip, args.eye_tap)
    dlo, dhi, dmism = find_deskew(d, args.base, args.blen, args.deskew_txn, args.max)

    if dmism != 0:
        print(f"\n[validate] FAIL: deskew find did not reach 0 (best={dmism}). "
              f"If the whole grid is a flat floor, the skew exceeds 0..{args.max} "
              f"or the fault is not a per-beat skew -> ILA the raw dfi_rddata "
              f"64b halves at this rate.", flush=True)
        return 2

    # ---- 2. deskew-AWARE leveling: centre the tap with the trained deskew ----
    print(f"\n[validate] deskew-aware leveling with deskew_lo={dlo} deskew_hi={dhi}",
          flush=True)
    lv2 = A7Leveling(d, base_addr=args.base, burst_len=args.blen, rd_phase=0,
                     rddata_delay=8, t_phy_wrlat=0, t_rddata_en=6,
                     deskew_lo=dlo, deskew_hi=dhi, verbose=True)
    res = lv2.run()
    if not res.ok:
        print(f"[validate] FAIL: deskew-aware leveling did not verify: {res.notes}",
              flush=True)
        return 3
    print(f"[validate] leveled: bitslip={res.bitslip} tap={res.rd_tap} "
          f"eye={res.rd_window} deskew=({dlo},{dhi})", flush=True)

    # ---- 3. LONG write batch, then read it all back ----
    print(f"\n[validate] LONG validation: {args.txn} txns x burst_len {args.blen}",
          flush=True)
    d.set_deskew(deskew_lo=dlo, deskew_hi=dhi)
    d.clear_stats()
    d.program_wr_engine(start_addr=args.base, burst_len=args.blen,
                        txn_count=args.txn, stride_0=args.blen * 8,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.start_wr()
    wr_ok = wait_engine(d, "wr")
    d.program_rd_engine(start_addr=args.base, burst_len=args.blen,
                        txn_count=args.txn, stride_0=args.blen * 8,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.clear_stats()
    d.start_rd()
    rd_ok = wait_engine(d, "rd")
    mism = d.beats_mismatched()
    exp, act, match, valid = d.crc()
    print(f"[validate] wr_ok={wr_ok} rd_ok={rd_ok} beats_mismatched={mism} "
          f"crc_match={match} crc_valid={valid}", flush=True)
    if mism == 0 and wr_ok and rd_ok:
        print(f"\n[validate] PASS: {args.txn} txns written + read back clean at "
              f"bitslip={res.bitslip} tap={res.rd_tap} deskew=({dlo},{dhi}). "
              f"Reads validated.", flush=True)
        return 0
    print(f"\n[validate] FAIL: long read-back had {mism} mismatched beats.",
          flush=True)
    return 4


if __name__ == "__main__":
    raise SystemExit(main())
