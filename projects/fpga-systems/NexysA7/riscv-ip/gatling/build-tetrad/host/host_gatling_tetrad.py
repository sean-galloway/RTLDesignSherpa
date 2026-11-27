#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""host_gatling_tetrad.py -- host CLI for the gatling build-tetrad bitstream (`make host-gatling_tetrad ARGS=...`).

Thin front end over gatling_tetrad_board.TetradBoard and the authored-once
programs in gatling_tetrad_programs.py (this area's bin/) -- the SAME
programs the cocotb UART sim runs.

    make host-gatling_tetrad                       # smoke, then the tetrad program (N = 96)
    make host-gatling_tetrad ARGS="--count 384 --seed 7"
"""
import argparse
import sys
from pathlib import Path

_BIN = Path(__file__).resolve().parents[2] / "bin"
sys.path.insert(0, str(_BIN))
import gatling_tetrad_board as tb_board      # noqa: E402
import gatling_tetrad_programs as progs      # noqa: E402
from boards import get_board                 # noqa: E402


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--count", type=int, default=96, help="ACCUMULATE invocations per cell")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    k = tb_board.TetradBoard(port=port, baudrate=args.baud)
    print(f"== gatling_tetrad (4 contexts, 4 cells) on {board.SPEC.display_name} @ {port} ==")
    reports = progs.all_programs(k, count=args.count, seed=args.seed)
    for r in reports:
        print("  " + r.line())
        for row in r.rows:
            print("      " + row)
        for f in r.failures[:10]:
            print("      FAIL " + f)
    return 0 if all(r.ok for r in reports) else 1


if __name__ == "__main__":
    sys.exit(main())
