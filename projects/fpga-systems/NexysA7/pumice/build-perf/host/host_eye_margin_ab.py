#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read-eye margin A/B across t_rddata_en (pumice ISSUE-015).

Two board host paths program two different read-path tuples:

    init  (pumice_master.SimpleTest)   wrlat=1, t_rddata_en=6, rddata_delay=7
    char  (pumice_char.ControllerConfig) wrlat=1, t_rddata_en=1, rddata_delay=2

Both sit on the measured clean diagonal `rddata_delay = t_rddata_en + 1` -- the
a7ddrphy's data-vs-valid offset is a fixed 1 cycle -- so both WORK, and that is
exactly why "both pass integrity" settles nothing. The question is which has
more MARGIN.

The measurement is the leveling scan itself. A7Leveling sweeps the read IDELAY
tap within each bitslip and records the passing window; `LevelingResult.rd_window`
is (first, last) passing tap under the winning bitslip. Its WIDTH is the data eye
in tap steps. So: level once per candidate tuple and compare widths. Wider eye =
more margin against temperature, voltage and part-to-part spread.

This is NOT `host_sweep_rddata_delay.py`. That sweeps the coarse delay at a fixed
bitslip/tap and cannot find an eye at all without leveling first -- run at both
candidates it reported 16/16 beats mismatched at every delay, which is the tool,
not the tuples.

    source env_python
    python3 host/host_eye_margin_ab.py
    python3 host/host_eye_margin_ab.py --points 6:7 1:2 4:5
"""
import argparse

import ddr2_char as dc
from ddr2_char import DDR2CharDriver, harness_probe
from boards import get_board
from pumice_master import SimpleTest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--wrlat", type=int, default=1,
                    help="t_phy_wrlat; both host paths program 1")
    ap.add_argument("--points", nargs="+", default=["6:7", "1:2"],
                    help="t_rddata_en:rddata_delay pairs (default: init's and char's)")
    args = ap.parse_args()

    board = get_board(args.board)
    args.port = board.find_uart_port(probe=harness_probe(), want=args.port,
                                     label="pumice DDR2 char harness")
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)
    print(f"board: {d.describe_build()}", flush=True)

    rows = []
    for spec in args.points:
        rden, dly = (int(x) for x in spec.split(":"))
        print(f"\n=== leveling at t_rddata_en={rden} rddata_delay={dly} "
              f"(wrlat={args.wrlat}) ===", flush=True)
        # level_cache=None: must actually SCAN, not replay a cached point.
        t = SimpleTest(d, t_phy_wrlat=args.wrlat, t_rddata_en=rden,
                       rddata_delay=dly, level_cache=None)
        t.init(do_leveling=True)
        lv = t.level
        if lv is None:
            rows.append((rden, dly, None, None, None, "no leveling result"))
            continue
        lo, hi = lv.rd_window
        width = (hi - lo + 1) if (lo >= 0 and hi >= lo) else 0
        rows.append((rden, dly, lv.bitslip, lv.rd_tap, width,
                     "clean" if lv.ok else f"NOT CLEAN: {lv.notes}"))

    print("\n" + "=" * 68)
    print(f"{'rden':>5} {'rddly':>6} {'bitslip':>8} {'tap':>5} {'eye(taps)':>10}  status")
    for rden, dly, bs, tap, w, note in rows:
        print(f"{rden:>5} {dly:>6} {str(bs):>8} {str(tap):>5} {str(w):>10}  {note}")
    print("=" * 68)

    good = [r for r in rows if r[4]]
    if len(good) >= 2:
        best = max(good, key=lambda r: r[4])
        worst = min(good, key=lambda r: r[4])
        if best[4] == worst[4]:
            print(f"EQUAL MARGIN: every point measured an eye {best[4]} taps wide. "
                  f"The tuple choice is not a margin question; pick on another "
                  f"ground and say so.")
        else:
            print(f"WIDEST EYE: t_rddata_en={best[0]} rddata_delay={best[1]} "
                  f"at {best[4]} taps, vs {worst[4]} at t_rddata_en={worst[0]}. "
                  f"That is {best[4] - worst[4]} taps more margin.")
    else:
        print("Not enough clean points to compare -- fix the leveling first.")


if __name__ == "__main__":
    main()
