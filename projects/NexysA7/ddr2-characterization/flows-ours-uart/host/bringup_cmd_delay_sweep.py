#!/usr/bin/env python3
"""Live sweep of the runtime DFI command->data alignment (DFI_TUNING.cmd_delay)
x read bitslip, over UART — no rebuilds. Finds the on-silicon write-alignment
sweet spot: pumice's command->wrdata skew is ~5 in sim, but the real a7ddrphy
may want a slightly different value. For each cmd_delay, do an inner bitslip
scan at a mid IDELAY tap and report the min beats_mismatched. Any cell below the
full burst means writes are landing at that cmd_delay -> refine tap/bitslip there.
"""
import argparse
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

LANES = 0b11


def strobe(d, k):
    d.phy_poke(dc.PHY_DLY_SEL, LANES)
    d.phy_poke(k, 1)
    d.phy_poke(dc.PHY_DLY_SEL, 0)


def set_eye(d, bitslip, tap):
    strobe(d, dc.PHY_RDLY_DQ_BITSLIP_RST)
    strobe(d, dc.PHY_RDLY_DQ_RST)
    for _ in range(bitslip):
        strobe(d, dc.PHY_RDLY_DQ_BITSLIP)
    strobe(d, dc.PHY_RDLY_DQ_RST)
    for _ in range(tap):
        strobe(d, dc.PHY_RDLY_DQ_INC)


def one_test(d, base, blen, txn, seed):
    d.soft_reset()
    time.sleep(0.004)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=2,
                         t_rddata_en=6, rd_in_order=True)
    d.clear_stats()
    d.program_wr_engine(start_addr=base, burst_len=blen, txn_count=txn,
                        stride_0=blen * 8, lfsr_seed=seed, data_mode=True,
                        hash_seed0=seed)
    d.start_wr()
    if not wait_engine(d, "wr"):
        return -1
    d.program_rd_engine(start_addr=base, burst_len=blen, txn_count=txn,
                        stride_0=blen * 8, lfsr_seed=seed, data_mode=True,
                        hash_seed0=seed)
    d.clear_stats()
    d.start_rd()
    wait_engine(d, "rd")
    return d.beats_mismatched()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--cmd-delays", default="0,1,2,3,4,5,6,7,8")
    ap.add_argument("--tap", type=int, default=16)
    ap.add_argument("--rdphase", type=int, default=0)
    ap.add_argument("--wrphase", type=int, default=0)
    ap.add_argument("--blen", type=int, default=4)
    ap.add_argument("--txn", type=int, default=1)
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=0x1EAFF00D)
    args = ap.parse_args()

    delays = [int(x) for x in args.cmd_delays.split(",")]
    total = args.blen * args.txn

    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}  (full-mismatch = {total})", flush=True)
    d.phy_poke(11, args.rdphase)
    d.phy_poke(12, args.wrphase)
    print(f"rdphase={args.rdphase} wrphase={args.wrphase}, inner bitslip scan "
          f"(0..7) at IDELAY tap={args.tap}; cell = min beats (bitslip@min)\n",
          flush=True)
    print("cmd_delay:  min_beats@bitslip", flush=True)
    hits = []
    for cd in delays:
        d.set_dfi_cmd_delay(cd)
        best_mm, best_bs = total + 1, -1
        for bs in range(8):
            set_eye(d, bs, args.tap)
            mm = one_test(d, 0x0, args.blen, args.txn, args.seed)
            if 0 <= mm < best_mm:
                best_mm, best_bs = mm, bs
            if mm == 0:
                break
        tag = f"{best_mm}@b{best_bs}" if best_bs >= 0 else "wr-fail"
        print(f"  {cd:>2}:       {tag}", flush=True)
        if 0 <= best_mm < total:
            hits.append((cd, best_bs, best_mm))

    print(flush=True)
    if hits:
        hits.sort(key=lambda h: h[2])
        print("PROMISING (writes landing — below full mismatch):", flush=True)
        for cd, bs, mm in hits[:10]:
            print(f"  cmd_delay={cd} bitslip={bs} -> {mm} beats mismatched",
                  flush=True)
    else:
        print("Every cmd_delay still full-mismatch at this tap. Try other taps "
              "or rdphase/wrphase; if still flat, the read path (not writes) "
              "needs the faithful read oracle + fix.", flush=True)


if __name__ == "__main__":
    main()
