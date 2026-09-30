#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the RS loop campaign on a programmed Nexys A7: init, then smoke (and sweep).

    ./run_smoke.py                          # auto-detect the board's port
    ./run_smoke.py --sequences init smoke sweep
    ./run_smoke.py --list
"""
from __future__ import annotations

import argparse
import os
import sys

import rs_env  # noqa: F401
from boards import get_board
from sequence import SequenceContext, SequenceError, SequenceRunner
from rs_loop import RsLoopDriver

SEQ_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ORDER = ["init", "smoke"]


def build_runner() -> SequenceRunner:
    return SequenceRunner(SequenceContext()).discover(SEQ_DIR)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--sequences", nargs="+", default=DEFAULT_ORDER)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--keep-going", action="store_true")
    ap.add_argument("--blocks", type=int, default=16)
    ap.add_argument("--counts", default=None, help="sweep: comma list of error counts")
    ap.add_argument("--throttle", action="store_true", help="sweep: random ready on the checkers")
    args = ap.parse_args(argv)

    runner = build_runner()
    if args.list:
        print(runner.catalog())
        return 0
    try:
        runner.resolve(args.sequences)
    except SequenceError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    print(f"board: {board.SPEC.display_name}  port: {port}")
    runner.ctx.bus = RsLoopDriver(port=port, baudrate=args.baud)
    runner.ctx.params.update(blocks=args.blocks, throttle=args.throttle,
                             counts=[int(c) for c in args.counts.split(",")] if args.counts else None)
    report = runner.run(args.sequences, stop_on_fail=not args.keep_going)
    print(report.summary())
    return 0 if report.ok else 1


if __name__ == "__main__":
    sys.exit(main())
