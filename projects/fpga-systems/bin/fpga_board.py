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
    sub.add_parser("serial", help="print this board's JTAG serial (for tcl)")

    rb = sub.add_parser("readback",
                        help="what the hw_server sees on the JTAG chain (read-only)")
    rb.add_argument("--vivado", default=os.environ.get("VIVADO", "vivado"))
    rb.add_argument("--json", action="store_true",
                    help="emit the parsed chain as JSON (for harnesses to record)")
    rb.add_argument("--verify", action="store_true",
                    help="also fail if THIS board is not on the chain")

    prog = sub.add_parser("program", help="program this board over JTAG")
    prog.add_argument("--bitstream", required=True)
    prog.add_argument("--vivado", default=os.environ.get("VIVADO", "vivado"))
    prog.add_argument("--dry-run", action="store_true",
                      help="print the command and environment, run nothing")
    # Verification is ON by default: programming whichever board answers first is
    # how a result gets attributed to the wrong design, which is the argument the
    # HOLD fallback comment in fpga_board.mk already makes. The opt-out exists
    # because this lands on 13 board paths at once.
    prog.add_argument("--no-verify-identity", dest="verify_identity",
                      action="store_false", default=True,
                      help="skip the pre-program JTAG identity check")

    args = ap.parse_args(argv)

    if args.cmd == "list":
        for name in list_boards():
            print(f"  {name}")
        return 0

    board = get_board(args.board)

    if args.cmd == "info":
        print(board.describe())
        return 0

    if args.cmd == "serial":
        # For tcl that must pin a hw_target. Prints nothing (exit 0) when the
        # board has no serial, so a caller can substitute it unconditionally and
        # get "any target" rather than the string "None" as a match pattern.
        if board.jtag_serial:
            print(board.jtag_serial)
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

    if args.cmd == "readback":
        try:
            chain = board.readback(vivado=args.vivado)
            if args.verify:
                board.verify_identity(vivado=args.vivado, readback=chain)
        except RuntimeError as exc:          # IdentityError included
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1
        if args.json:
            import json
            print(json.dumps(chain, indent=2, sort_keys=True))
        else:
            for t in chain["targets"]:
                print(f"target {t['serial']}  ({t['target']})")
            for d in chain["devices"]:
                print(f"  device {d['name']}  part {d['part']}  idcode {d['idcode']}")
        return 0

    if args.cmd == "program":
        try:
            return board.program(args.bitstream, vivado=args.vivado,
                                 dry_run=args.dry_run,
                                 verify_identity=args.verify_identity)
        except (FileNotFoundError, RuntimeError) as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 1

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
