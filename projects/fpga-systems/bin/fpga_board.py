#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""CLI over the board registry -- what Makefiles and shells call.

    python3 projects/fpga-systems/bin/fpga_board.py list
    python3 projects/fpga-systems/bin/fpga_board.py info    --board nexys_a7_100t
    python3 projects/fpga-systems/bin/fpga_board.py ports   --board nexys_a7_100t
    python3 projects/fpga-systems/bin/fpga_board.py program --board nexys_a7_100t --bitstream x.bit

`program` is the replacement for each flow's `vivado -source tcl/program_fpga.tcl`
recipe: the board facts come from the registry, so a flow's Makefile no longer
carries a serial or its own copy of the tcl.
"""

from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from boards import get_board, list_boards  # noqa: E402


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--board", default=None,
                    help="board name (default: $FPGA_BOARD, else nexys_a7_100t)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("list", help="list known boards")
    sub.add_parser("info", help="show one board's facts")
    sub.add_parser("ports", help="list this board's UART ports")

    prog = sub.add_parser("program", help="program this board over JTAG")
    prog.add_argument("--bitstream", required=True)
    prog.add_argument("--vivado", default=os.environ.get("VIVADO", "vivado"))
    prog.add_argument("--dry-run", action="store_true",
                      help="print the command and environment, run nothing")

    args = ap.parse_args(argv)

    if args.cmd == "list":
        for name in list_boards():
            print(f"  {name}")
        return 0

    board = get_board(args.board)

    if args.cmd == "info":
        print(board.describe())
        return 0

    if args.cmd == "ports":
        ports = board.find_uart_ports()
        if not ports:
            print(f"no UART ports found for {board.SPEC.display_name} "
                  f"(serial {board.SPEC.uart_usb_serial})")
            return 1
        for p in ports:
            print(f"  {p}")
        return 0

    if args.cmd == "program":
        try:
            return board.program(args.bitstream, vivado=args.vivado,
                                 dry_run=args.dry_run)
        except (FileNotFoundError, RuntimeError) as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
