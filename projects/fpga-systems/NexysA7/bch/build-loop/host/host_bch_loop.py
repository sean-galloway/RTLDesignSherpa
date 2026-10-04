#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""host_bch_loop.py -- host CLI for the bch_loop_top bitstream (`make host-bch_loop ARGS=...`).

Thin front-end over bch_loop.BchLoopDriver and the authored-once programs in
bch_loop_programs.py -- the SAME programs the cocotb sim runs.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import bch_loop as bl                 # noqa: E402
import bch_loop_programs as progs     # noqa: E402
from boards import get_board         # noqa: E402

MODES = {"none": bl.BchLoopDriver.INJ_NONE, "count": bl.BchLoopDriver.INJ_COUNT,
         "burst": bl.BchLoopDriver.INJ_BURST, "rate": bl.BchLoopDriver.INJ_RATE}


def cmd_smoke(args, drv):
    r = progs.smoke(drv)
    print(f"  BUILD_ID = 0x{r.build_id:08X}  {'OK' if r.build_id_ok else 'FAIL'}")
    for w, rd, ok in r.scratch:
        print(f"  SCRATCH 0x{w:08X} -> 0x{rd:08X}  {'OK' if ok else 'FAIL'}")
    p = r.profile
    print(f"  PROFILE BCH({p['n']},{p['k']}) t={p['t']} m={p['m']} {p['spb']} symbols/beat")
    return 0 if r.ok else 1


def _print_run(r, t):
    bad = progs.verdict(r, t)
    print(f"  blocks={r.blocks} mode={r.mode} count={r.count} rate={r.rate} bypass={r.bypass} "
          f"cycles={r.cycles} ({r.cycles_per_block:.1f}/block)")
    for d in r.present:
        print(f"  {d.name:>6}: ok={d.blk_ok} corr={d.blk_corr} unc={d.blk_unc} frame={d.blk_frame} "
              f"sym_corr={d.sym_corr} pkts={d.pkts} crc=0x{d.crc:08X} data_err={d.data_err}")
    print(f"  injector: {r.inj_symbols} bits in {r.inj_blocks} blocks, {r.inj_over_t} blocks over t")
    print("  " + ("PASS" if not bad else "FAIL: " + "; ".join(bad)))
    return 0 if not bad else 1


def cmd_bypass(args, drv):
    return _print_run(progs.bypass(drv, blocks=args.blocks), drv.profile()["t"])


def cmd_run(args, drv):
    r = progs.run(drv, MODES[args.mode], count=args.count, rate=args.rate, blocks=args.blocks,
                  throttle=args.throttle, gen_seed=args.gen_seed, inj_seed=args.inj_seed)
    return _print_run(r, drv.profile()["t"])


def cmd_sweep(args, drv):
    t = drv.profile()["t"]
    counts = [int(c) for c in args.counts.split(",")] if args.counts else list(range(0, 2 * t + 3))
    rows = progs.sweep(drv, counts, blocks=args.blocks, t=t, throttle=args.throttle)
    for row in rows:
        print("  " + progs.format_row(row))
    return 0 if all(r.ok for r in rows) else 1


def cmd_random(args, drv):
    from pathlib import Path as _P
    _bin = str(_P(__file__).resolve().parents[2] / "bin")
    if _bin not in sys.path:
        sys.path.insert(0, _bin)
    import bch_env  # noqa: F401
    from sequence import SequenceContext, SequenceRunner
    ctx = SequenceContext(bus=drv, board=None,
                          params={"runs": args.runs, "blocks": args.blocks, "seed": args.seed},
                          log=print)
    runner = SequenceRunner(ctx=ctx).discover(_bin)
    report = runner.run(["init", "random"])
    print(report.summary())
    return 0 if report.ok else 1


def cmd_bw(args, drv):
    topo = drv.topology()
    print(f"  datapath {topo['iface']}, decoder {topo['name_a']}")
    if args.bypass:
        r = drv.run(mode=bl.BchLoopDriver.INJ_NONE, blocks=args.blocks, bypass=True)
    else:
        r = progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=args.count,
                      blocks=args.blocks, throttle=args.throttle)
    bad = progs.verdict(r, args.t)
    print(f"  {r.blocks} blocks, e={args.count}: {r.cycles} cycles "
          f"({r.cycles_per_block:.1f}/block)")
    print(progs.bandwidth(r))

    if args.slope:
        small_blocks = args.small or max(4, args.blocks // 4)
        if args.bypass:
            r2 = drv.run(mode=bl.BchLoopDriver.INJ_NONE, blocks=small_blocks, bypass=True)
        else:
            r2 = progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=args.count,
                           blocks=small_blocks, throttle=args.throttle)
        prof = drv.profile()
        n = args.n or prof["n"]
        k = args.k or prof["k"]
        s = prof["spb"]
        print(f"  {r2.blocks} blocks: {r2.cycles} cycles "
              f"({r2.cycles_per_block:.1f}/block)")
        print(progs.bandwidth_slope(r2, r, n, k, s))
    if bad:
        print("  COMPLAINTS: " + "; ".join(bad))
        return 1
    return 0


def cmd_obs(args, drv):
    caps = drv.observer_caps()
    prof = drv.profile()
    r = progs.iface_observers(drv, blocks=args.blocks, count=args.count)
    bad = progs.verdict(r, prof["t"])
    print(f"  {r.blocks} blocks, e={args.count}: {r.cycles} cycles "
          f"({r.cycles_per_block:.1f}/block)")
    print(progs.format_iface_obs(r, prof, caps))
    if args.hist and drv.topology()["iface"] == "AXI4":
        print(progs.format_axi4_hist(drv.axi4_observer(hist=True)))
    if bad:
        print("  COMPLAINTS: " + "; ".join(bad))
        return 1
    return 0


def cmd_soak(args, drv):
    from pathlib import Path as _P
    _bin = str(_P(__file__).resolve().parents[2] / "bin")
    if _bin not in sys.path:
        sys.path.insert(0, _bin)
    import bch_env  # noqa: F401
    from sequence import SequenceContext, SequenceRunner
    ctx = SequenceContext(bus=drv, board=None,
                          params={"target": args.target, "blocks": args.blocks,
                                  "seed": args.seed, "progress": args.progress},
                          log=print)
    runner = SequenceRunner(ctx=ctx).discover(_bin)
    report = runner.run(["init", "soak"])
    print(report.summary())
    return 0 if report.ok else 1


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
    p.add_argument("--gen-seed", type=lambda s: int(s, 0), default=0)
    p.add_argument("--inj-seed", type=lambda s: int(s, 0), default=None)
    p = sub.add_parser("sweep")
    p.add_argument("--counts", default=None, help="comma list; default 0..2t+2")
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--throttle", action="store_true")
    p = sub.add_parser("random")
    p.add_argument("--runs", type=int, default=64)
    p.add_argument("--blocks", type=int, default=4)
    p.add_argument("--seed", type=int, default=1)
    p = sub.add_parser("bw", help="one run, reported as bandwidth from the meters")
    p.add_argument("--blocks", type=int, default=64)
    p.add_argument("--count", type=int, default=0, help="errors per block")
    p.add_argument("--t", type=int, default=8, help="the profile's t, for the verdict")
    p.add_argument("--throttle", action="store_true")
    p.add_argument("--bypass", action="store_true")
    p.add_argument("--slope", action="store_true")
    p.add_argument("--small", type=int, default=0)
    p.add_argument("--n", type=int, default=0)
    p.add_argument("--k", type=int, default=0)
    p = sub.add_parser("obs", help="one run, reported from the interface observer")
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--count", type=int, default=0)
    p.add_argument("--hist", action="store_true")
    p = sub.add_parser("soak")
    p.add_argument("--target", type=int, default=1_000_000)
    p.add_argument("--blocks", type=int, default=4096)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--progress", type=int, default=16)
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    drv = bl.BchLoopDriver(port=port, baudrate=args.baud)
    print(f"== {args.cmd} on {board.SPEC.display_name} @ {port} ==")
    return {"smoke": cmd_smoke, "bypass": cmd_bypass, "run": cmd_run, "sweep": cmd_sweep,
            "random": cmd_random, "soak": cmd_soak, "bw": cmd_bw, "obs": cmd_obs}[args.cmd](args, drv)


if __name__ == "__main__":
    sys.exit(main())
