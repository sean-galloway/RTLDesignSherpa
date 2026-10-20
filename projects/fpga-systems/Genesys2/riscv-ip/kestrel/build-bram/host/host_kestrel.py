#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""host_kestrel.py -- host CLI for the kestrel build-bram bitstream (`make host-kestrel ARGS=...`).

Thin front end over ../../bin/kestrel_board.KestrelBoard and the
authored-once programs in ../../bin/kestrel_programs.py -- the SAME programs
the cocotb UART sim runs.

    make host-kestrel                          # smoke, then the full rv32ui battery
    make host-kestrel ARGS="--tests add,lw"    # a subset of the battery
"""
import argparse
import sys
from pathlib import Path

_BIN = Path(__file__).resolve().parents[2] / "bin"
sys.path.insert(0, str(_BIN))
import kestrel_board as kb          # noqa: E402
import kestrel_programs as progs    # noqa: E402
from boards import get_board        # noqa: E402


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--board", default="genesys2")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--tests", default=None, help="comma list of rv32ui tests (default: all)")
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    k = kb.KestrelBoard(port=port, baudrate=args.baud)
    print(f"== kestrel (block RAM) on {board.SPEC.display_name} @ {port} ==")
    reports = [progs.smoke(k),
               progs.battery(k, args.tests.split(",") if args.tests else None)]
    for r in reports:
        print("  " + r.line())
        for row in r.rows:
            print("      " + row)
        for f in r.failures[:10]:
            print("    ! " + f)
    return 0 if all(r.ok for r in reports) else 1


if __name__ == "__main__":
    sys.exit(main())
