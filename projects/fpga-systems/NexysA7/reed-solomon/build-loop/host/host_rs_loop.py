#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""host_rs_loop.py -- host CLI for the rs_loop_top bitstream (`make host-rs_loop ARGS=...`).

Thin front-end over rs_loop.RsLoopDriver and the authored-once programs in
rs_loop_programs.py -- the SAME programs the cocotb sim runs.

Subcommands:
  smoke      BUILD_ID, SCRATCH round-trip, PROFILE
  bypass     generator -> checkers with the codec bypassed
  run        one run: --mode none|count|burst|rate --count E --rate R --blocks N [--throttle]
  sweep      COUNT mode over --counts (default 0..2t+2): one line per error count
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import rs_loop as rl                 # noqa: E402
import rs_loop_programs as progs     # noqa: E402
from boards import get_board         # noqa: E402

MODES = {"none": rl.RsLoopDriver.INJ_NONE, "count": rl.RsLoopDriver.INJ_COUNT,
         "burst": rl.RsLoopDriver.INJ_BURST, "rate": rl.RsLoopDriver.INJ_RATE}


def cmd_smoke(args, drv):
    r = progs.smoke(drv)
    print(f"  BUILD_ID = 0x{r.build_id:08X}  {'OK' if r.build_id_ok else 'FAIL'}")
    for w, rd, ok in r.scratch:
        print(f"  SCRATCH 0x{w:08X} -> 0x{rd:08X}  {'OK' if ok else 'FAIL'}")
    p = r.profile
    print(f"  PROFILE RS({p['n']},{p['n'] - 2 * p['t']}) t={p['t']} m={p['m']} {p['spb']} symbols/beat")
    return 0 if r.ok else 1


def _print_run(r, t):
    bad = progs.verdict(r, t)
    print(f"  blocks={r.blocks} mode={r.mode} count={r.count} rate={r.rate} bypass={r.bypass} "
          f"cycles={r.cycles} ({r.cycles_per_block:.1f}/block)")
    for d in (r.a, r.b):
        print(f"  {d.name:>6}: ok={d.blk_ok} corr={d.blk_corr} unc={d.blk_unc} frame={d.blk_frame} "
              f"sym_corr={d.sym_corr} pkts={d.pkts} crc=0x{d.crc:08X} crc_ok={d.crc_ok} data_err={d.data_err}")
    print(f"  expected crc 0x{r.crc_expected:08X}; injector: {r.inj_symbols} symbols in {r.inj_blocks} blocks, "
          f"{r.inj_over_t} blocks over t; A vs B: {r.cmp_beats} beats, {r.cmp_data_mismatch} data / "
          f"{r.cmp_status_mismatch} verdict mismatches")
    print("  " + ("PASS" if not bad else "FAIL: " + "; ".join(bad)))
    return 0 if not bad else 1


def cmd_bypass(args, drv):
    return _print_run(progs.bypass(drv, blocks=args.blocks), drv.profile()["t"])


def cmd_run(args, drv):
    r = progs.run(drv, MODES[args.mode], count=args.count, rate=args.rate, blocks=args.blocks,
                  throttle=args.throttle)
    return _print_run(r, drv.profile()["t"])


def cmd_sweep(args, drv):
    t = drv.profile()["t"]
    counts = [int(c) for c in args.counts.split(",")] if args.counts else list(range(0, 2 * t + 3))
    rows = progs.sweep(drv, counts, blocks=args.blocks, t=t, throttle=args.throttle)
    for row in rows:
        print("  " + progs.format_row(row))
    return 0 if all(r.ok for r in rows) else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("smoke")
    p = sub.add_parser("bypass"); p.add_argument("--blocks", type=int, default=16)
    p = sub.add_parser("run")
    p.add_argument("--mode", choices=MODES, default="count")
    p.add_argument("--count", type=int, default=8)
    p.add_argument("--rate", type=int, default=0)
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--throttle", action="store_true")
    p = sub.add_parser("sweep")
    p.add_argument("--counts", default=None, help="comma list; default 0..2t+2")
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--throttle", action="store_true")
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    drv = rl.RsLoopDriver(port=port, baudrate=args.baud)
    print(f"== {args.cmd} on {board.SPEC.display_name} @ {port} ==")
    return {"smoke": cmd_smoke, "bypass": cmd_bypass, "run": cmd_run, "sweep": cmd_sweep}[args.cmd](args, drv)


if __name__ == "__main__":
    sys.exit(main())
