#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: examples.counter_bin
# Purpose: Regenerate rtl/common/counter_bin.sv from Python
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-07-30
"""Regenerate ``rtl/common/counter_bin.sv``.

A deliberately faithful port of an existing hand-written module, including its
documentation banner, so the generated file can be diffed against the original.
This is the useful way to adopt a generator: reproduce something you already
trust before generating something you do not.

    python counter_bin.py            # print to stdout
    python counter_bin.py --verify   # lint and synthesis-check
    python counter_bin.py -o out/    # write out/counter_bin.sv
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from svsherpa import (  # noqa: E402  (path set up above)
    C,
    Concat,
    If,
    Module,
    ModuleDoc,
    Repl,
    ZERO,
    verify,
)

WAVEDROM = """\
Timing Diagram (WIDTH=3, MAX=4):

{signal: [
  {name: 'clk',              wave: 'p..........'},
  {name: 'rst_n',            wave: '01.........'},
  {name: 'enable',           wave: '0.1........'},
  {name: 'counter_bin_curr', wave: 'x.22222222.', data: \
['000','001','010','011','100','101','110','111']},
  {name: 'counter_bin_next', wave: 'x.22222222.', data: \
['001','010','011','100','101','110','111','000']}
]}\
"""


def build() -> Module:
    """Build the counter_bin module."""
    doc = ModuleDoc(
        description=(
            "Binary counter with configurable maximum value and special\n"
            "FIFO-optimized wraparound behavior. Counts from 0 to MAX-1, then\n"
            "wraps by clearing lower bits and inverting the MSB. This behavior\n"
            "is specifically designed for efficient FIFO pointer management\n"
            "where the MSB indicates buffer fullness."
        ),
        features=(
            "Configurable bit width (2-64 bits)",
            "Parameterizable maximum count value",
            "FIFO-optimized wraparound (MSB inversion + lower bit clear)",
            "Enable control for gating count operation",
            "Single-cycle registered output",
            "Combinational next-value preview",
        ),
        param_notes={
            "WIDTH": (
                "Description: Bit width of counter\n"
                "Range: 2 to 64\n"
                "Constraints: Must be at least 2 to support MSB inversion"
            ),
            "MAX": (
                "Description: Maximum count value (counter wraps at MAX-1)\n"
                "Range: 2 to (2^(WIDTH-1))\n"
                "Constraints: Must fit within WIDTH-1 bits"
            ),
        },
        port_notes={
            "clk": "Clock input (rising edge active)",
            "rst_n": "Asynchronous active-low reset",
            "enable": "Count enable (active-high)",
            "counter_bin_curr": "Current counter value (registered)",
            "counter_bin_next": "Next counter value (combinational)",
        },
        timing=(
            "Latency:        1 cycle (counter_bin_curr is registered)",
            "Combinational:  counter_bin_next available same cycle as enable",
            "Pipeline:       No pipeline stages",
        ),
        behavior=(
            "On each rising clock edge (if enable=1):\n"
            "1. If counter_bin_curr[WIDTH-2:0] == MAX-1:\n"
            "   - Invert the MSB and clear all lower bits\n"
            "2. Else:\n"
            "   - counter_bin_next = counter_bin_curr + 1\n"
            "3. If enable=0:\n"
            "   - counter_bin_next = counter_bin_curr (hold)"
        ),
        wavedrom=WAVEDROM,
        notes=(
            "**FIFO-Specific Design:** MSB inversion is NOT standard counter "
            "wraparound",
            "For a standard modulo-N counter, use counter_load_clear.sv",
            "counter_bin_next provides 1-cycle lookahead for timing closure",
            "enable=0 holds the count (does NOT reset)",
        ),
        related=(
            "counter_load_clear.sv - Standard counter with load/clear",
            "counter_bingray.sv - Gray code counter for CDC",
            "fifo_sync.sv - Uses this counter for read/write pointers",
        ),
        test=(
            "Location: val/common/test_counter_bin.py\n"
            "Run: pytest val/common/test_counter_bin.py -v"
        ),
        references=(
            '"RTL Coding for FIFOs" - Cliff Cummings, SNUG 2002',
            "FIFO pointer management technique (MSB for full/empty detection)",
        ),
    )

    m = Module(
        "counter_bin",
        subsystem="common",
        purpose=(
            "Binary counter with configurable maximum and FIFO-optimized "
            "wraparound"
        ),
        doc=doc,
    )
    width = m.param("WIDTH", 5)
    max_val = m.param("MAX", 10)

    clk = m.input("clk")
    rst_n = m.input("rst_n")
    enable = m.input("enable")
    curr = m.output("counter_bin_curr", width)
    nxt = m.output("counter_bin_next", width)

    # Lower bits only -- the MSB is the FIFO wrap flag, not part of the count.
    w_max = m.logic("w_max_val", width - 1,
                    comment="Maximum value for lower bits (excludes MSB)")
    m.assign(w_max, C(max_val - 1).cast(width - 1))

    m.always_comb(
        If(enable,
            If(curr[width - 2:0] == w_max,
                # Wraparound: invert MSB, clear lower bits.
                nxt.set(Concat(~curr[width - 1],
                               Repl(width - 1, C(0, 1, base="b")))),
            ).Else(
                nxt.set(curr + 1),
            ),
        ).Else(
            # Hold current value when disabled.
            nxt.set(curr),
        ),
        comment="Combinational next-value logic",
    )

    m.always_ff(clk, rst_n,
                reset=[curr.set(ZERO)],
                body=[curr.set(nxt)],
                comment="Registered counter output")
    return m


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-o", "--out", help="directory or file to write")
    parser.add_argument("--verify", action="store_true",
                        help="run verilator and yosys checks")
    args = parser.parse_args()

    module = build()

    for warning in module.check():
        print(f"warning: {warning}", file=sys.stderr)

    if args.verify:
        report = verify(module)
        print(report, file=sys.stderr)
        if not report.ok:
            return 1

    if args.out:
        path = module.write(args.out)
        print(f"wrote {path}", file=sys.stderr)
    else:
        print(module.emit(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
