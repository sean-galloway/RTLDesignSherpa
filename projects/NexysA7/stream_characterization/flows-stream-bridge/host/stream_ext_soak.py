#!/usr/bin/env python3
"""Aggressive chained-descriptor SOAK for the STREAM char board flow (TASK-059).

Loops randomized MIXED chained EXTENDED descriptors -- transpose (strided write),
reverse-transpose (strided read) and contiguous, at varied depth/tile-dims, all
chained via next_ptr (the pre-si failure shape a single kicked transpose never
exercised). Each chain must move ALL its beats; a dropped beat ("hole") means the
sink write-beat counter never reaches TIMER_EXPECTED_BEATS, TIMER_STATUS.done
never asserts, and the run FAILS -- the exact board-readable TASK-059 signature.

Reuses the PROVEN board flow from run_characterization.CharacterizationRunner
(configure_stream / clear_stats / setup_timer / kick_channels / poll_completion);
the only new part is the mixed extended-chain generation and the soak loop. Runs
on the real board (needs the harness bitstream built with
USE_ROW_COL_MAJOR_ADDRESSING=1 -- stream_char_top hardwires it).

Usage (board):
    source env_python
    python3 host/stream_ext_soak.py --minutes 10          # 10-minute soak
    python3 host/stream_ext_soak.py --iters 2000 --seed 1 # fixed count / seed
The UART port is auto-detected (autodetect_port) since ttyUSB numbering drifts.
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _here)
# converters/bin holds UARTAxiBridge (same probe run_characterization uses).
for up in range(3, 9):
    cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
    if os.path.isdir(cand):
        sys.path.insert(0, cand)
        break

from harness_addrs import autodetect_port
from run_characterization import CharacterizationRunner


def _shape(kind, W, H, bs):
    """rd/wr stride dicts for one tile shape (mirrors stream_char_tb soak)."""
    if kind == 'transpose':        # contiguous read, column-major (strided) write
        return (dict(s0=bs,     s1=W * bs, inner=W),
                dict(s0=H * bs, s1=bs,     inner=H))
    if kind == 'rtranspose':       # column-major (strided) read, contiguous write
        return (dict(s0=H * bs, s1=bs,     inner=H),
                dict(s0=bs,     s1=W * bs, inner=W))
    beats = W * H                  # contiguous both sides
    return (dict(s0=bs, s1=0, inner=beats), dict(s0=bs, s1=0, inner=beats))


def run_soak(runner, *, channel=0, minutes=10.0, iters=None, seed=0x5EED,
             max_depth=6, per_run_timeout_s=30.0):
    import random
    rng = random.Random(seed)
    bs = runner.builder.bytes_per_beat
    runner.configure_stream([channel])

    deadline = time.time() + minutes * 60.0
    it = 0
    passed = 0
    total_beats = 0
    fails = []
    while (iters is None and time.time() < deadline) or (iters is not None and it < iters):
        depth = rng.randint(2, max_depth)
        descriptors, plan = [], []
        for _k in range(depth):
            kind = rng.choice(['transpose', 'rtranspose', 'contig'])
            W = rng.choice([2, 4, 8]); H = rng.choice([2, 4, 8])
            rd, wr = _shape(kind, W, H, bs)
            descriptors.append(dict(transfer_bytes=W * H * bs, rd=rd, wr=wr))
            plan.append(f"{kind}{W}x{H}")
        chain_bytes = sum(d['transfer_bytes'] for d in descriptors)
        chain_beats = chain_bytes // bs

        runner.clear_stats()
        for addr, data in runner.builder.build_ext_chain(channel, descriptors):
            runner.bridge.write(addr, data)
        runner.setup_timer(chain_bytes)
        runner.kick_channels({channel: runner.builder.kick_address(channel)})
        res = runner.poll_completion(timeout_s=per_run_timeout_s)

        ok = bool(res.get('done')) and not res.get('error')
        passed += int(ok)
        total_beats += chain_beats if ok else 0
        tag = 'PASS' if ok else 'FAIL'
        print(f"soak[{it:04d}] depth={depth} {'+'.join(plan)} "
              f"beats={chain_beats} {tag} ({res})")
        if not ok:
            fails.append((it, plan, res))
            # keep soaking to gather the failure distribution, but flag loudly
        it += 1

    print(f"\nstream_ext_soak: {passed}/{it} chained runs PASS, "
          f"{total_beats} beats moved, {len(fails)} FAIL")
    if fails:
        for i, plan, res in fails[:10]:
            print(f"  FAIL iter {i}: {'+'.join(plan)} -> {res}")
    return 0 if not fails else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM extended chained-descriptor soak")
    ap.add_argument("--port", default='auto')
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--minutes", type=float, default=10.0,
                    help="soak wall-clock budget (ignored if --iters given)")
    ap.add_argument("--iters", type=int, default=None, help="fixed iteration count")
    ap.add_argument("--seed", type=lambda s: int(s, 0), default=0x5EED)
    ap.add_argument("--max-depth", type=int, default=6)
    args = ap.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    print(f"stream_ext_soak: port={port} baud={args.baud} "
          f"{'iters=' + str(args.iters) if args.iters else str(args.minutes) + ' min'} "
          f"seed=0x{args.seed:X}")
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge)
        return run_soak(runner, channel=args.channel, minutes=args.minutes,
                        iters=args.iters, seed=args.seed, max_depth=args.max_depth)


if __name__ == "__main__":
    raise SystemExit(main())
