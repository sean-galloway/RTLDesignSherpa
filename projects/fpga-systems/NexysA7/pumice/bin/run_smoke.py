#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the pumice bring-up smoke: init, then one write-then-read pass.

This is the shape every `run_<test>.py` takes. It does the three things a
sequence is not allowed to do -- pick the board, resolve the port, open the
transport -- and then hands the runner a plain list of sequence names:

    ./run_smoke.py                        # auto-detect the board's port
    ./run_smoke.py --port /dev/ttyUSB1    # pin the port
    ./run_smoke.py --sequences init write_read memtest
    ./run_smoke.py --list                 # what this area offers

Adding a test to the campaign is a new `seq_*.py` here plus its name on the
command line; nothing in this file changes.
"""

from __future__ import annotations

import argparse
import os
import sys

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from boards import get_board
from sequence import SequenceContext, SequenceError, SequenceRunner

from ddr2_char import DDR2CharDriver, harness_probe

SEQ_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ORDER = ["init", "write_read"]


def build_runner() -> SequenceRunner:
    """Registry for this area, with no transport attached yet -- so `--list`
    works with no board present."""
    return SequenceRunner(SequenceContext()).discover(SEQ_DIR)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto",
                    help="serial port; 'auto' probes this board's ports")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--sequences", nargs="+", default=DEFAULT_ORDER,
                    help=f"sequence names in run order (default: {' '.join(DEFAULT_ORDER)})")
    ap.add_argument("--list", action="store_true",
                    help="list this area's sequences and exit")
    ap.add_argument("--keep-going", action="store_true",
                    help="run every sequence even after one fails")

    ap.add_argument("--base-addr", type=lambda s: int(s, 0), default=0x0)
    ap.add_argument("--burst-len", type=int, default=8)
    ap.add_argument("--txn", type=int, default=64)
    ap.add_argument("--no-leveling", action="store_true")
    ap.add_argument("--level-cache", default=None,
                    help="path to persist/reuse the leveled read window")
    ap.add_argument("--mem-mb", type=int, default=128,
                    help="device size for the memtest sequence")
    args = ap.parse_args(argv)

    runner = build_runner()

    if args.list:
        print(f"sequences in {SEQ_DIR}:")
        print(runner.catalog())
        return 0

    # Resolve the plan BEFORE opening anything: a typo in --sequences should
    # cost nothing, not a board session and a half-run campaign.
    try:
        runner.resolve(args.sequences)
    except SequenceError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        print(f"\nsequences available in {SEQ_DIR}:", file=sys.stderr)
        print(runner.catalog(), file=sys.stderr)
        return 2

    # Narrow to this board's ports by USB serial, then confirm the bitstream by
    # its BUILD_ID. Neither alone is enough: the serial cannot tell which
    # bitstream is loaded, and the probe cannot tell two identical boards apart.
    board = get_board(args.board)
    port = board.find_uart_port(
        probe=harness_probe(),
        want=args.port,
        label="pumice DDR2 char harness",
    )

    drv = DDR2CharDriver(port=port, baudrate=args.baud)

    runner.ctx.bus = drv
    runner.ctx.board = board
    runner.ctx.params = {
        "base_addr": args.base_addr,
        "burst_len": args.burst_len,
        "txn_count": args.txn,
        "leveling": not args.no_leveling,
        "level_cache": args.level_cache,
        "mem_bytes": args.mem_mb << 20,
    }

    try:
        report = runner.run(args.sequences, stop_on_fail=not args.keep_going)
    finally:
        bridge = getattr(drv, "bridge", None)
        if bridge is not None:
            bridge.close()

    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
