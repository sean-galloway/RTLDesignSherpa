#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the amber pair-rig smoke campaign.

This is the one file allowed to know about ports, boards, and transport. It
composes the UART bridge once and then hands the runner a list of sequence
names, so the identical campaign runs on the FPGA and in cocotb sim.
"""

from __future__ import annotations

import argparse
import os
import sys
import time

import amber_env  # noqa: F401  (path setup)

from amber_board import (AmberDriver, build_amber_bridge, harness_probe,
                         open_amber_link)
from boards import get_board
from sequence import RunReport, SequenceContext, SequenceError, SequenceRunner


SEQ_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ORDER = ["init", "smoke"]


def build_runner(ctx: SequenceContext | None = None) -> SequenceRunner:
    """Registry for this area, with no transport attached yet."""
    return SequenceRunner(ctx or SequenceContext()).discover(SEQ_DIR)


def run_campaign(bridge, *, sequences=None, params=None,
                 log=print) -> RunReport:
    """Run the amber smoke campaign over an already-built bridge.

    This is the entry point used by the cocotb cosim: it supplies a
    UARTAxiBridge over a CocotbUartChannel and re-uses the same sequences
    the board CLI runs.
    """
    ctx = SequenceContext(bus=AmberDriver(bridge, log=logging_or_print(log)),
                          params=params or {}, log=log)
    runner = build_runner(ctx)
    order = sequences or DEFAULT_ORDER
    return runner.run(order, stop_on_fail=True)


def logging_or_print(log):
    """Accept a logger or a print-like callable."""
    if hasattr(log, "info"):
        return log
    import logging
    return logging.getLogger("run_smoke")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.strip().splitlines()[0])
    ap.add_argument("--board", default="genesys2")
    ap.add_argument("--port", default="auto",
                    help="serial port; 'auto' probes this board's ports")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--sequences", nargs="+", default=DEFAULT_ORDER,
                    help=f"sequence names in run order "
                         f"(default: {' '.join(DEFAULT_ORDER)})")
    ap.add_argument("--list", action="store_true",
                    help="list this area's sequences and exit")
    ap.add_argument("--count", type=int, default=20000)
    ap.add_argument("--blind", action="store_true",
                    help="write-only smoke (no reads); board only")

    args = ap.parse_args(argv)

    runner = build_runner()

    if args.list:
        print(f"sequences in {SEQ_DIR}:")
        print(runner.catalog())
        return 0

    try:
        runner.resolve(args.sequences)
    except SequenceError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        print(f"\nsequences available in {SEQ_DIR}:", file=sys.stderr)
        print(runner.catalog(), file=sys.stderr)
        return 2

    board = get_board(args.board)
    port = board.find_uart_port(
        probe=harness_probe(),
        want=args.port,
        baudrate=args.baud,
        timeout=0.4,
        label="amber Genesys2 harness",
    )
    link = open_amber_link(port, board_name=args.board, baudrate=args.baud)
    bridge = build_amber_bridge(link)

    ctx = SequenceContext(
        bus=AmberDriver(bridge),
        board=board,
        params={
            "count": args.count,
            "blind": args.blind,
            "sleep_fn": time.sleep,
        },
    )
    runner.ctx = ctx

    try:
        report = runner.run(args.sequences, stop_on_fail=True)
    finally:
        bridge.close()

    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
