#!/usr/bin/env python3
"""Aggressive chained-descriptor SOAK for the STREAM char board flow (TASK-059).

Loops randomized MIXED chained EXTENDED descriptors -- transpose (strided write),
reverse-transpose (strided read) and contiguous, at varied depth/tile-dims, all
chained via next_ptr (the pre-si failure shape a single kicked transpose never
exercised). Each chain must move ALL its beats; a dropped beat ("hole") means the
sink write-beat counter never reaches TIMER_EXPECTED_BEATS, TIMER_STATUS.done
never asserts, and the run FAILS -- the exact board-readable TASK-059 signature.

Reuses the PROVEN board flow from characterization.CharacterizationRunner
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
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/). Replaces the
# hand-counted walks to a sibling flow and to converters/bin.
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from harness_addrs import H as harness_reg, autodetect_port  # 'H' alias: the soak
from characterization import CharacterizationRunner          # loop uses H=tile height


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
             max_depth=6, per_run_timeout_s=30.0, check_crc=True):
    import random
    rng = random.Random(seed)
    bs = runner.builder.bytes_per_beat
    bridge = runner.bridge
    ch_bit = 1 << channel
    crc_addr = harness_reg("CRC_MATCH")   # resolve now; the loop shadows H with tile height

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

        # Proven per-run order (characterization): clear_stats then
        # (re)configure the stream -- clear_stats zeroes the counters AND drops
        # the scheduler config, so configure_stream must follow it every run.
        runner.clear_stats()
        runner.configure_stream([channel])
        for addr, data in runner.builder.build_ext_chain(channel, descriptors):
            bridge.write(addr, data)
        runner.setup_timer(chain_bytes)
        runner.kick_channels({channel: runner.builder.kick_address(channel)})
        res = runner.poll_completion(timeout_s=per_run_timeout_s)

        # DMA-slave verification only (no monitors). The harness TIMER watches the
        # crc_check SINK SLAVE's write-beat counter: done => it reached the
        # programmed expected beats (a dropped "hole" never asserts done),
        # timer_pass => it matched. CRC_MATCH is the crc_check slave's data check.
        done  = bool(res.get('completed'))   # poll_completion key is 'completed'
        tpass = bool(res.get('timer_pass'))  # timer fired done AND beat count matched
        err   = bool(res.get('error'))
        crc_ok = True
        if check_crc:
            crc_ok = bool(bridge.read(crc_addr) & ch_bit)

        ok = done and tpass and not err and crc_ok
        passed += int(ok)
        total_beats += chain_beats if ok else 0
        print(f"soak[{it:04d}] depth={depth} {'+'.join(plan)} "
              f"beats={chain_beats} done={done} pass={tpass} crc={crc_ok} "
              f"{'PASS' if ok else 'FAIL'}")
        if not ok:
            fails.append((it, plan, dict(done=done, pass_=tpass, err=err,
                                         crc=crc_ok, expect=chain_beats)))
            # keep soaking to gather the failure distribution, but flag loudly
        it += 1

    print(f"\nstream_ext_soak: {passed}/{it} chained runs PASS, "
          f"{total_beats} beats moved (slave beat+CRC verified), {len(fails)} FAIL")
    if fails:
        for i, plan, info in fails[:10]:
            print(f"  FAIL iter {i}: {'+'.join(plan)} -> {info}")
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
    ap.add_argument("--no-crc", action="store_true",
                    help="skip the crc_check data check; rely on TIMER done+pass "
                         "(the sink-slave beat count) only")
    args = ap.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    print(f"stream_ext_soak: port={port} baud={args.baud} "
          f"{'iters=' + str(args.iters) if args.iters else str(args.minutes) + ' min'} "
          f"seed=0x{args.seed:X}")
    with UARTAxiBridge(port, args.baud) as bridge:
        runner = CharacterizationRunner(bridge)
        return run_soak(runner, channel=args.channel, minutes=args.minutes,
                        iters=args.iters, seed=args.seed, max_depth=args.max_depth,
                        check_crc=not args.no_crc)


if __name__ == "__main__":
    raise SystemExit(main())
