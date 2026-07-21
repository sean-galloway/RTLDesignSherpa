#!/usr/bin/env python3
"""Wide coarse read-timing sweep: t_rddata_en x rddata_delay (deskew=0, fixed
eye bitslip/tap). The board rate changed (266 MT/s), which shifts the a7ddrphy
read-return window; the earlier sweep only covered rddata_delay 7..9. If any
cell drops well below the 48/64 floor, the read window just moved with frequency
and it is a runtime retune (no rebuild). Flat 48 everywhere => not coarse timing.
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import A7Leveling, wait_engine

SEED = 0x1EAF_F00D


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--base", type=lambda x: int(x, 0), default=0x0)
    ap.add_argument("--blen", type=int, default=8)
    ap.add_argument("--txn", type=int, default=8)
    ap.add_argument("--eye-bitslip", type=int, default=0)
    ap.add_argument("--eye-tap", type=int, default=8)
    ap.add_argument("--rden", default="3,4,5,6,7,8")
    ap.add_argument("--rddly", default="4,5,6,7,8,9,10,11,12")
    ap.add_argument("--rdphase", default="0,1")
    args = ap.parse_args()

    rden_list = [int(x) for x in args.rden.split(",")]
    rddly_list = [int(x) for x in args.rddly.split(",")]
    rdphase_list = [int(x) for x in args.rdphase.split(",")]

    args.port = dc.autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}", flush=True)

    # Fix the analog eye + deskew off; we are only moving the coarse window.
    lv = A7Leveling(d, base_addr=args.base, burst_len=args.blen, verbose=False)
    lv.apply_taps(args.eye_bitslip, args.eye_tap)

    def measure(rden, rddly, rdphase):
        d.soft_reset(); time.sleep(0.005)
        d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=0,
                             t_rddata_en=rden, rd_in_order=True)
        d.set_dfi_phase(rd_phase=rdphase, wr_phase=0)
        d.set_dfi_rddata_delay(rddly)
        d.set_deskew(deskew_lo=0, deskew_hi=0)
        d.clear_stats()
        d.program_wr_engine(start_addr=args.base, burst_len=args.blen,
                            txn_count=args.txn, stride_0=args.blen * 8,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.start_wr()
        if not wait_engine(d, "wr", ignore_error=True):
            return None                       # write never completed
        d.program_rd_engine(start_addr=args.base, burst_len=args.blen,
                            txn_count=args.txn, stride_0=args.blen * 8,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.clear_stats()
        d.start_rd()
        # ignore_error: a MISMATCHING read latches rd_error, which is exactly
        # the case being measured -- bailing on it would discard every real data
        # point. Only a read that never asserts done is a non-measurement.
        # (An incomplete read compares ZERO beats, so beats_mismatched() would
        # return 0 and read as a perfect score -- hence "x", never 0.)
        if not wait_engine(d, "rd", ignore_error=True):
            return None
        return d.beats_mismatched()

    best = (None, 1 << 30)
    for rdphase in rdphase_list:
        print(f"\n=== rd_phase={rdphase} ===  (cols rddata_delay {rddly_list})",
              flush=True)
        print("rden\\rddly  " + "  ".join(f"{c:>3}" for c in rddly_list))
        for rden in rden_list:
            row = []
            for rddly in rddly_list:
                mm = measure(rden, rddly, rdphase)
                row.append(mm)
                if mm is not None and mm < best[1]:
                    best = ((rden, rddly, rdphase), mm)
                time.sleep(0.01)
            print(f"  {rden:>3}      "
                  + "  ".join("  x" if m is None else f"{m:>3}" for m in row),
                  flush=True)

    print(f"\n[wide] best mism={best[1]} at (t_rddata_en, rddata_delay, rd_phase)"
          f"={best[0]}", flush=True)
    if best[1] == 0:
        print("[wide] CLEAN point found -> coarse read-window retune. Bake it in.")
    elif best[1] < 48:
        print("[wide] below the 48 floor -> window is moving; narrow around best.")
    else:
        print("[wide] flat >=48 floor across the whole coarse space -> NOT coarse "
              "read timing. ILA the raw dfi_rddata 64b halves at this rate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
