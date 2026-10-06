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
  random     --runs N runs, each with a fresh data seed, error seed, mode and count
  bw         one run, reported as input/output bandwidth from the hardware
             meters (productive/backpressure/starvation/idle per end)
  obs        one run, reported from the INTERFACE observer on the datapath's
             own seams (exact beats/bytes/packets per port, ideal column)
  soak       --target blocks (default 1,000,000) of random patterns, in runs of
             --blocks each so any failure replays as one short run
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import rs_loop as rl                 # noqa: E402
import rs_loop_programs as progs     # noqa: E402
from boards import get_board         # noqa: E402

MODES = {"none": rl.RsLoopDriver.INJ_NONE, "count": rl.RsLoopDriver.INJ_COUNT,
         "burst": rl.RsLoopDriver.INJ_BURST, "rate": rl.RsLoopDriver.INJ_RATE,
         "cluster": rl.RsLoopDriver.INJ_RANDOM}


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
                  throttle=args.throttle, gen_seed=args.gen_seed, inj_seed=args.inj_seed,
                  mark=args.mark)
    return _print_run(r, drv.profile()["t"])


def cmd_erasure(args, drv):
    """The erasure sequence on the board: f = t, 2t correct; f = 2t+1 refused."""
    from pathlib import Path as _P
    _bin = str(_P(__file__).resolve().parents[2] / "bin")
    if _bin not in sys.path:
        sys.path.insert(0, _bin)      # rs_env lives in the area's bin/, alongside the sequences
    import rs_env  # noqa: F401  (path setup for `sequence`)
    from sequence import SequenceContext, SequenceRunner
    ctx = SequenceContext(bus=drv, board=None,
                          params={"blocks": args.blocks},
                          log=print)
    runner = SequenceRunner(ctx=ctx).discover(_bin)
    report = runner.run(["init", "erasure"])
    print(report.summary())
    return 0 if report.ok else 1


def cmd_sweep(args, drv):
    t = drv.profile()["t"]
    counts = [int(c) for c in args.counts.split(",")] if args.counts else list(range(0, 2 * t + 3))
    rows = progs.sweep(drv, counts, blocks=args.blocks, t=t, throttle=args.throttle)
    for row in rows:
        print("  " + progs.format_row(row))
    return 0 if all(r.ok for r in rows) else 1


def cmd_random(args, drv):
    """The random campaign, driven through the same sequence the board runs."""
    from pathlib import Path as _P
    _bin = str(_P(__file__).resolve().parents[2] / "bin")
    if _bin not in sys.path:
        sys.path.insert(0, _bin)      # rs_env lives in the area's bin/, alongside the sequences
    import rs_env  # noqa: F401  (path setup for `sequence`)
    from sequence import SequenceContext, SequenceRunner
    ctx = SequenceContext(bus=drv, board=None,
                          params={"runs": args.runs, "blocks": args.blocks, "seed": args.seed},
                          log=print)
    runner = SequenceRunner(ctx=ctx).discover(_bin)
    report = runner.run(["init", "random"])
    print(report.summary())
    return 0 if report.ok else 1


def cmd_bw(args, drv):
    """One measured run, reported as bandwidth from the hardware meters.

    The numbers come from the two axi_bus_meter instances, not from dividing a
    block count by CYCLES: the meters bucket every cycle of each end's
    valid/ready handshake and freeze when the run does, so utilisation is
    productive/window with no host polling folded in.
    """
    topo = drv.topology()
    print(f"  datapath {topo['iface']}, decoder {topo['name_a']}, "
          f"{topo['decoders']} decoder(s)")
    if args.bypass:
        # generator straight to the checkers, codec out of the loop. This is
        # the 100% reference: whatever it falls short of 1 beat/cycle is the
        # harness, and everything beyond that in a codec run is the codec.
        r = drv.run(mode=rl.RsLoopDriver.INJ_NONE, blocks=args.blocks, bypass=True)
    else:
        r = progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=args.count,
                      blocks=args.blocks, throttle=args.throttle)
    bad = progs.verdict(r, args.t)
    print(f"  {r.blocks} blocks, e={args.count}: {r.cycles} cycles "
          f"({r.cycles_per_block:.1f}/block)")
    print(progs.bandwidth(r))

    if args.slope:
        # A second, shorter run. Differencing the two cancels the pipeline
        # fill, which is a FIXED cost present in both windows -- the same
        # reason the sim tests score a slope over two block counts instead of
        # timing one. Without this, every finite run reads below the true
        # utilisation by fill/window, and a total divided by a block count is
        # not a rate at all.
        small_blocks = args.small or max(4, args.blocks // 4)
        if args.bypass:
            r2 = drv.run(mode=rl.RsLoopDriver.INJ_NONE, blocks=small_blocks, bypass=True)
        else:
            r2 = progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=args.count,
                           blocks=small_blocks, throttle=args.throttle)
        # straight off PROFILE, so the ideal describes the bitstream actually
        # on the board rather than a default that can silently disagree
        prof = drv.profile()
        n = args.n or prof["n"]
        k = args.k or (prof["n"] - 2 * prof["t"])
        s = prof["spb"]
        print(f"  {r2.blocks} blocks: {r2.cycles} cycles "
              f"({r2.cycles_per_block:.1f}/block)")
        print(progs.bandwidth_slope(r2, r, n, k, s))
    if bad:
        print("  COMPLAINTS: " + "; ".join(bad))
        return 1
    return 0


def cmd_obs(args, drv):
    """One measured run, reported from the interface observer on the datapath's
    own seams -- the characterization readout proven in the uart_observers /
    uart_axi4_observers cosim tests, now reachable from the board CLI.
    """
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
    """A million blocks of random patterns, through the same sequence layer."""
    from pathlib import Path as _P
    _bin = str(_P(__file__).resolve().parents[2] / "bin")
    if _bin not in sys.path:
        sys.path.insert(0, _bin)      # rs_env lives in the area's bin/, alongside the sequences
    import rs_env  # noqa: F401  (path setup for `sequence`)
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
    # a failing random-campaign run is replayed by passing its two seeds back
    p.add_argument("--gen-seed", type=lambda s: int(s, 0), default=0)
    p.add_argument("--inj-seed", type=lambda s: int(s, 0), default=None)
    p.add_argument("--mark", action="store_true",
                   help="erasure run: the injector's hit mask rides in_erasure, "
                        "so the bound doubles to 2t (needs TOPOLOGY.erasure = 1)")
    p = sub.add_parser("erasure", help="marked runs at f = t, 2t, 2t+1, through the sequence")
    p.add_argument("--blocks", type=int, default=8)
    p = sub.add_parser("sweep")
    p.add_argument("--counts", default=None, help="comma list; default 0..2t+2")
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--throttle", action="store_true")
    p = sub.add_parser("random")
    p.add_argument("--runs", type=int, default=64)
    p.add_argument("--blocks", type=int, default=4)
    p.add_argument("--seed", type=int, default=1, help="host RNG seed; the campaign is reproducible")
    p = sub.add_parser("bw", help="one run, reported as bandwidth from the meters")
    p.add_argument("--blocks", type=int, default=64)
    p.add_argument("--count", type=int, default=0, help="errors per block")
    p.add_argument("--t", type=int, default=8, help="the profile's t, for the verdict")
    p.add_argument("--throttle", action="store_true", help="random checker ready")
    p.add_argument("--bypass", action="store_true",
                   help="codec out of the loop: the 100%% bandwidth reference")
    p.add_argument("--slope", action="store_true",
                   help="two runs, differenced, so the pipeline fill cancels -- "
                        "the only form that can read 100%%")
    p.add_argument("--small", type=int, default=0,
                   help="the second block count for --slope (default blocks/4)")
    p.add_argument("--n", type=int, default=0, help="n, for the ideal (default from PROFILE)")
    p.add_argument("--k", type=int, default=0, help="k, for the ideal (default from PROFILE)")
    p = sub.add_parser("obs", help="one run, reported from the interface observer")
    p.add_argument("--blocks", type=int, default=16)
    p.add_argument("--count", type=int, default=0, help="errors per block")
    p.add_argument("--hist", action="store_true",
                   help="AXI4 only: also dump the latency histograms "
                        "(96 extra SELECT+DATA round-trips)")
    p = sub.add_parser("soak")
    p.add_argument("--target", type=int, default=1_000_000, help="total blocks to push")
    p.add_argument("--blocks", type=int, default=4096, help="blocks per run (per seed pair)")
    p.add_argument("--seed", type=int, default=1, help="host RNG seed; the soak is reproducible")
    p.add_argument("--progress", type=int, default=16, help="report every N runs")
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    drv = rl.RsLoopDriver(port=port, baudrate=args.baud)
    print(f"== {args.cmd} on {board.SPEC.display_name} @ {port} ==")
    return {"smoke": cmd_smoke, "bypass": cmd_bypass, "run": cmd_run, "sweep": cmd_sweep,
            "random": cmd_random, "soak": cmd_soak, "erasure": cmd_erasure,
            "bw": cmd_bw, "obs": cmd_obs}[args.cmd](args, drv)


if __name__ == "__main__":
    sys.exit(main())
