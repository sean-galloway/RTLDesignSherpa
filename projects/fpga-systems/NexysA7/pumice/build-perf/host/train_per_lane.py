#!/usr/bin/env python3
"""Per-BYTE-LANE read leveling on the board (independent bitslip + IDELAY tap).

The x16 DDR2 has TWO byte lanes (DQ[7:0]/DQS0 = lane0, DQ[15:8]/DQS1 = lane1),
and the a7ddrphy gates every rdly/bitslip strobe per lane via dly_sel[1:0]
(s7ddrphy.py: `self._dly_sel.storage[i]`). A7Leveling has only ever swept with
dly_sel=0b11 — BOTH lanes forced to the SAME (bitslip, tap). If the lanes' read
eyes do not overlap at a common setting (inter-lane DQS return skew), the joint
sweep can NEVER pass — "no passing tap at any bitslip" — while per-lane settings
would. LiteDRAM's BIOS levels each module independently for exactly this reason.

Procedure (write once, read per point — read leveling never disturbs DRAM):
  1. Coarse: sweep (bitslip0 x bitslip1) x a few shared taps, aggregate
     beats_mismatched. A pass needs BOTH lanes right, so a clean point proves
     the pair. bitslip0==bitslip1 diagonal == the old joint sweep.
  2. Refine: at the winning pair, per-lane tap eye — hold the other lane at a
     passing tap, sweep this lane 0..31; aggregate mismatches then belong to
     the swept lane alone. Centre each lane in its own eye.
  3. Verify + persist to reports/leveling_per_lane.json.

If NOTHING in the full per-lane space passes, the fault is NOT leveling — it is
digital (rate-2->4 adapter / aligner), go back to the ILA.

    python3 host/train_per_lane.py [--port auto] [--bl 4] [--mr0 0x0432]

CRITICAL: phase-distinct data pattern (data_mode=True address-hash), never an
aliased a5a0-repeat — a repeating pattern makes a slipped lane read back as
CORRECT (lane1's a5/3f stream repeats every 2 words) and hides the skew.
"""
import argparse
import json
import os
import time

import ddr2_char as dc
from ddr2_char import DDR2CharDriver
from pumice_master import wait_engine

SEED = 0x1234_5678          # address-hash seed -> phase/lane-distinct words
LANE0, LANE1, BOTH = 0b01, 0b10, 0b11
N_BITSLIPS = 8              # ISERDES bitslip range (mod-8)
MAX_TAPS = 32               # IDELAYE2 5-bit tap
COARSE_TAPS = (0, 8, 16, 24)
RESULT_PATH = os.path.join(os.path.dirname(__file__), os.pardir,
                           "reports", "leveling_per_lane.json")


class PerLanePhy:
    """dly_sel-bracketed per-lane PHY strobes with absolute (bitslip, tap)
    tracking per lane (the PHY knobs are inc/rst-relative, no readback)."""

    def __init__(self, drv: DDR2CharDriver):
        self.drv = drv
        self.bs = [0, 0]
        self.tap = [0, 0]

    def _strobe(self, knob: int, lanes: int) -> None:
        self.drv.phy_poke(dc.PHY_DLY_SEL, lanes)
        self.drv.phy_poke(knob, 1)
        self.drv.phy_poke(dc.PHY_DLY_SEL, 0)

    def reset_read_path(self) -> None:
        self._strobe(dc.PHY_RDLY_DQ_RST, BOTH)
        self._strobe(dc.PHY_RDLY_DQ_BITSLIP_RST, BOTH)
        self.bs = [0, 0]
        self.tap = [0, 0]

    def set_bitslip(self, lane: int, value: int) -> None:
        value %= N_BITSLIPS
        mask = LANE0 if lane == 0 else LANE1
        # bitslip advances mod-8; reach any target without a full-path reset
        steps = (value - self.bs[lane]) % N_BITSLIPS
        for _ in range(steps):
            self._strobe(dc.PHY_RDLY_DQ_BITSLIP, mask)
        self.bs[lane] = value

    def set_tap(self, lane: int, value: int) -> None:
        assert 0 <= value < MAX_TAPS
        mask = LANE0 if lane == 0 else LANE1
        if value < self.tap[lane]:            # tap only increments; rst -> 0
            self._strobe(dc.PHY_RDLY_DQ_RST, mask)
            self.tap[lane] = 0
        for _ in range(value - self.tap[lane]):
            self._strobe(dc.PHY_RDLY_DQ_INC, mask)
        self.tap[lane] = value


def read_mism(d: DDR2CharDriver, blen: int, txn: int, stride: int) -> int:
    """One read pass against the written pattern; aggregate mismatch count."""
    d.program_rd_engine(start_addr=0x0, burst_len=blen, txn_count=txn,
                        stride_0=stride, lfsr_seed=SEED, data_mode=True,
                        hash_seed0=SEED)
    d.clear_stats()
    d.start_rd()
    # ignore_error (rd_error latches on any mismatch; we want the count) and
    # treat a never-done read as a HANG sentinel — its counter counted nothing
    # and would otherwise read back as a false-clean 0.
    if not wait_engine(d, "rd", ignore_error=True):
        return 1 << 30
    return d.beats_mismatched()


def tap_eye(phy: PerLanePhy, d: DDR2CharDriver, lane: int,
            blen: int, txn: int, stride: int):
    """Sweep this lane's 32 taps (other lane held); return passing tap list."""
    passing = []
    for tap in range(MAX_TAPS):
        phy.set_tap(lane, tap)
        if read_mism(d, blen, txn, stride) == 0:
            passing.append(tap)
    return passing


def longest_run(vals):
    best = cur = (vals[0], vals[0])
    for v in vals[1:]:
        cur = (cur[0], v) if v == cur[1] + 1 else (v, v)
        if (cur[1] - cur[0]) > (best[1] - best[0]):
            best = cur
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--bl", type=int,
                    default=int(os.environ.get("TEST_DRAM_BL", "4")),
                    help="DRAM burst length the bitstream runs (runtime CSR)")
    ap.add_argument("--mr0", type=lambda s: int(s, 0),
                    default=int(os.environ.get("TEST_MR0", "0x0432"), 0),
                    help="MR0 matching --bl (BL4/CL3 = 0x0432, BL8 = 0x0433)")
    ap.add_argument("--burst-len", type=int, default=8,
                    help="AXI beats per engine txn (multiple of the quantum)")
    ap.add_argument("--txn", type=int, default=4)
    args = ap.parse_args()

    # Geometry the CURRENT bitstream runs. soft_reset() re-programs geometry
    # from these class attrs, so override BEFORE any reset (the shipped
    # defaults are the old BL4 build).
    DDR2CharDriver.BOARD_DRAM_BL = args.bl
    DDR2CharDriver.BOARD_MR0 = args.mr0

    args.port = dc.autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"BUILD_ID=0x{d.build_id():08X}  BL={args.bl} MR0=0x{args.mr0:04X}",
          flush=True)

    # Board known-good bring-up point.
    d.soft_reset(); time.sleep(0.01)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=1,
                         t_rddata_en=6, rd_in_order=True)
    d.set_dfi_phase(rd_phase=0, wr_phase=0)
    d.set_dfi_rddata_delay(7)

    stride = args.burst_len * 8
    d.clear_stats()
    d.program_wr_engine(start_addr=0x0, burst_len=args.burst_len,
                        txn_count=args.txn, stride_0=stride,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.start_wr()
    if not wait_engine(d, "wr"):
        raise SystemExit("pattern write failed — fix writes before leveling")

    phy = PerLanePhy(d)
    phy.reset_read_path()

    # ---- coarse: (bitslip0 x bitslip1) x shared taps -----------------------
    total = N_BITSLIPS * N_BITSLIPS * len(COARSE_TAPS)
    n = 0
    coarse = {}          # (bs0, bs1, tap) -> mism
    passes = []
    for bs0 in range(N_BITSLIPS):
        phy.set_bitslip(0, bs0)
        for bs1 in range(N_BITSLIPS):
            phy.set_bitslip(1, bs1)
            best_mm = None
            for tap in COARSE_TAPS:
                phy.set_tap(0, tap)
                phy.set_tap(1, tap)
                mm = read_mism(d, args.burst_len, args.txn, stride)
                coarse[(bs0, bs1, tap)] = mm
                best_mm = mm if best_mm is None else min(best_mm, mm)
                if mm == 0:
                    passes.append((bs0, bs1, tap))
                n += 1
                print(f"\r[{n}/{total}] bs0={bs0} bs1={bs1} tap={tap:2d} "
                      f"mism={mm:<6d} passes={len(passes)}   ",
                      end="", flush=True)
            if best_mm == 0:
                print(f"\n  bs0={bs0} bs1={bs1}: CLEAN", flush=True)
    print(flush=True)

    if not passes:
        floor = min(coarse.values())
        print(f"\nNo (bs0, bs1, tap) passed anywhere in the per-lane space "
              f"(best mism={floor}). This is NOT a leveling problem — suspect "
              f"the digital read path (rate-2->4 adapter word gather / "
              f"aligner). Re-ILA raw dfi_rddata vs the delayed net.")
        return

    off_diag = sorted({(b0, b1) for b0, b1, _ in passes if b0 != b1})
    diag = sorted({(b0, b1) for b0, b1, _ in passes if b0 == b1})
    print(f"\npassing bitslip pairs: diagonal (joint-equivalent) {diag}, "
          f"per-lane-only {off_diag}")
    if off_diag and not diag:
        print("=> lanes REQUIRE different bitslips — inter-lane skew "
              "confirmed; the joint sweep could never pass.")

    # ---- refine: per-lane tap eye at the best pair -------------------------
    bs0, bs1, tap0 = passes[0]
    phy.set_bitslip(0, bs0)
    phy.set_bitslip(1, bs1)
    phy.set_tap(0, tap0)
    phy.set_tap(1, tap0)

    centres = [tap0, tap0]
    windows = [None, None]
    for lane in (0, 1):
        other = 1 - lane
        phy.set_tap(other, centres[other])   # hold partner at a passing tap
        eye = tap_eye(phy, d, lane, args.burst_len, args.txn, stride)
        if not eye:
            print(f"lane{lane}: no passing tap during refine (partner at "
                  f"{centres[other]}) — keeping coarse tap {tap0}")
            phy.set_tap(lane, tap0)
            continue
        lo, hi = longest_run(eye)
        centres[lane] = (lo + hi) // 2
        windows[lane] = (lo, hi)
        phy.set_tap(lane, centres[lane])
        print(f"lane{lane}: eye taps {lo}..{hi} (width {hi - lo + 1}), "
              f"centred at {centres[lane]}")

    ok = read_mism(d, args.burst_len, args.txn, stride) == 0
    result = {"ok": ok, "bitslip": [bs0, bs1], "tap": centres,
              "window": windows, "bl": args.bl, "mr0": args.mr0}
    os.makedirs(os.path.dirname(RESULT_PATH), exist_ok=True)
    with open(RESULT_PATH, "w") as f:
        json.dump(result, f, indent=2)
    print(f"\n{'PASS' if ok else 'FAIL'}: bitslip=(l0={bs0}, l1={bs1}) "
          f"tap=(l0={centres[0]}, l1={centres[1]}) -> {RESULT_PATH}")


if __name__ == "__main__":
    main()
