#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""host_alu.py -- host CLI for the alu-infer harness bitstream (`make host-alu ARGS=...`).

Thin front end over alu_harness.AluHarness and the authored-once programs in
alu_programs.py, both in the Genesys 2 area's bin/ (board-independent) -- the
SAME programs the cocotb UART sim runs (that area's
dv/tests/test_alu_harness_uart.py).

    make host-alu                       # every program
    make host-alu ARGS="stream latency" # a subset
"""
import argparse
import sys
from pathlib import Path

_BIN = (Path(__file__).resolve().parents[5]
        / "Genesys2" / "compute-eng-ip" / "alu-infer" / "bin")
sys.path.insert(0, str(_BIN))
import alu_harness as ah        # noqa: E402
import alu_programs as progs    # noqa: E402
from boards import get_board    # noqa: E402


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("programs", nargs="*", metavar="PROGRAM",
                    help="programs to run (default: all)")
    ap.add_argument("--board", default="nexys_a7_100t")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    args = ap.parse_args(argv)

    board = get_board(args.board)
    port = args.port if args.port != "auto" else board.find_uart_port()
    h = ah.AluHarness(port=port, baudrate=args.baud)
    s = h.slot_info()
    print(f"== alu-infer harness on {board.SPEC.display_name} @ {port} ==")
    print(f"   slot kind={s['kind']} en={s['en']} latencies add/mul/mac="
          f"{s['add_lat']}/{s['mul_lat']}/{s['mac_lat']} pipe_depth={s['pipe_depth']} "
          f"depth={s['depth']} clk={s['clk_mhz']} MHz")
    reports = progs.run_all(h, args.programs or None)
    for r in reports:
        print("  " + r.line())
        for f in r.failures[:8]:
            print(f"      {f}")
    return 0 if all(r.ok for r in reports) else 1


if __name__ == "__main__":
    sys.exit(main())
