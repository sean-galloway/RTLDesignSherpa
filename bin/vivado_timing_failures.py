#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Tool: vivado_timing_failures.py
# Purpose: Parse Vivado report_timing detail output into one-line summaries.
#
# Companion to (a future) vivado_timing_summary.py: that one parses
# timing_summary.txt; this one parses the verbose per-path detail report
# (typically named timing_failing_setup_full.txt or similar) emitted by:
#
#     report_timing -setup -slack_lesser_than 0 -max_paths 100000 \
#                   -nworst 1 -sort_by slack -input_pins -file <file>
#
# (or the equivalent -hold form).
#
# Author: sean galloway
# Created: 2026-04-26

"""
Vivado timing-violation summarizer.

Reads a Vivado report_timing detail file and emits one line per violation
with the high-level fields:

    violation_type   "setup" or "hold"
    path_group       e.g. sys_clk_pin
    path_type        e.g. "Max at Slow Process Corner"
    source           start point pin / port
    destination      end point pin / port
    slack_ns         slack in nanoseconds (negative = violated)

Two modes:

  default:
      One line per violation, sorted by slack (worst first).

  --bucketize:
      Collapse `[<digits>]` indices in source / destination to `[*]`, then
      keep only the worst-slack violation per (violation_type, source,
      destination) bucket. Useful when many bit-level violations share the
      same root cause and you want the unique-hierarchy hot list.

USAGE:
    bin/vivado_timing_failures.py <report.txt>
    bin/vivado_timing_failures.py <report.txt> --bucketize
    bin/vivado_timing_failures.py <report.txt> --format csv -o out.csv
    bin/vivado_timing_failures.py <report.txt> --include-met
"""

import argparse
import csv
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterator, List, Optional, TextIO

# ---------------------------------------------------------------------------
# Vivado report parsing
# ---------------------------------------------------------------------------
# A violation block looks like:
#
#   Slack (VIOLATED) :        -1.327ns  (required time - arrival time)
#     Source:                 u_harness/.../rd_empty_reg/C
#                               (rising edge-triggered cell FDPE clocked by ...)
#     Destination:            LED[0]
#                               (output port clocked by ...)
#     Path Group:             sys_clk_pin
#     Path Type:              Max at Slow Process Corner
#     ... (further per-path details we don't need)
#
# We pick out exactly six fields and ignore the rest. The next "Slack ("
# line ends the current block.

SLACK_RE      = re.compile(r"^\s*Slack\s*\(([A-Z]+)\)\s*:\s*([-\d.]+)ns\s*\((.*?)\)")
SOURCE_RE     = re.compile(r"^\s*Source:\s+(\S+)")
DEST_RE       = re.compile(r"^\s*Destination:\s+(\S+)")
PATH_GROUP_RE = re.compile(r"^\s*Path Group:\s+(.+?)\s*$")
PATH_TYPE_RE  = re.compile(r"^\s*Path Type:\s+(.+?)\s*$")

# Bracket-index pattern: matches one `[<digits>]` group. Replacing all
# occurrences with "[*]" collapses both bit positions (`r_data_reg[3]`)
# and generate-block / array indices (`gen_groups[2].u_inst`).
BRACKET_INDEX_RE = re.compile(r"\[\d+\]")


@dataclass
class Violation:
    violation_type: str  # "setup" or "hold" (or "unknown")
    path_group:     str
    path_type:      str
    source:         str
    destination:    str
    slack_ns:       float

    @staticmethod
    def field_order() -> List[str]:
        return ["violation_type", "path_group", "path_type",
                "source", "destination", "slack_ns"]

    def bucketized(self) -> "Violation":
        """Return a copy with bracket-indices collapsed to `[*]`."""
        return Violation(
            violation_type=self.violation_type,
            path_group=self.path_group,
            path_type=self.path_type,
            source=BRACKET_INDEX_RE.sub("[*]", self.source),
            destination=BRACKET_INDEX_RE.sub("[*]", self.destination),
            slack_ns=self.slack_ns,
        )


def _classify_violation(slack_descr: str) -> str:
    """Distinguish setup vs hold from the parenthetical on the Slack line.

    Setup paths print: "(required time - arrival time)"
    Hold paths print:  "(arrival time - required time)"
    """
    s = slack_descr.lower()
    if "required time - arrival time" in s:
        return "setup"
    if "arrival time - required time" in s:
        return "hold"
    return "unknown"


def parse_violations(stream: TextIO,
                     include_met: bool = False) -> Iterator[Violation]:
    """Yield one Violation per Slack block in a Vivado timing report."""

    pending: Optional[dict] = None
    required_keys = ("status", "slack_ns", "slack_descr", "source",
                     "destination", "path_group", "path_type")

    def emit(block: dict) -> Optional[Violation]:
        if any(k not in block for k in required_keys):
            return None
        if not include_met and block["status"] != "VIOLATED":
            return None
        return Violation(
            violation_type=_classify_violation(block["slack_descr"]),
            path_group=block["path_group"],
            path_type=block["path_type"],
            source=block["source"],
            destination=block["destination"],
            slack_ns=block["slack_ns"],
        )

    for line in stream:
        m = SLACK_RE.match(line)
        if m:
            # New block — flush previous.
            if pending is not None:
                v = emit(pending)
                if v is not None:
                    yield v
            pending = {
                "status":      m.group(1),
                "slack_ns":    float(m.group(2)),
                "slack_descr": m.group(3),
            }
            continue

        if pending is None:
            continue  # text before the first Slack block

        # Only fill each field once per block (Vivado prints them at most
        # once anyway, but be defensive against the per-pin path detail
        # rows further down using similar prefixes).
        for key, regex in (
            ("source",      SOURCE_RE),
            ("destination", DEST_RE),
            ("path_group",  PATH_GROUP_RE),
            ("path_type",   PATH_TYPE_RE),
        ):
            if key in pending:
                continue
            m = regex.match(line)
            if m:
                pending[key] = m.group(1)
                break

    # Flush trailing block at EOF.
    if pending is not None:
        v = emit(pending)
        if v is not None:
            yield v


def bucketize_worst(violations: List[Violation]) -> List[Violation]:
    """Collapse `[<digits>]` indices and keep the worst slack per bucket."""
    buckets: dict = {}
    for v in violations:
        b = v.bucketized()
        key = (b.violation_type, b.source, b.destination)
        existing = buckets.get(key)
        if existing is None or b.slack_ns < existing.slack_ns:
            buckets[key] = b
    return list(buckets.values())


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def _row(v: Violation) -> List[str]:
    return [v.violation_type, v.path_group, v.path_type,
            v.source, v.destination, f"{v.slack_ns:.3f}"]


def write_tabular(rows: List[Violation], out: TextIO, delimiter: str) -> None:
    writer = csv.writer(out, delimiter=delimiter, lineterminator="\n")
    writer.writerow(Violation.field_order())
    for v in rows:
        writer.writerow(_row(v))


def write_json(rows: List[Violation], out: TextIO) -> None:
    json.dump([asdict(v) for v in rows], out, indent=2)
    out.write("\n")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

class _StdoutKeeper:
    """Context manager that hands out sys.stdout without closing it."""
    def __init__(self, stream): self._s = stream
    def __enter__(self): return self._s
    def __exit__(self, *_): return False


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=("Parse a Vivado report_timing detail file (e.g. "
                     "timing_failing_setup_full.txt) into one-line per-"
                     "violation summaries."),
    )
    parser.add_argument("input", type=Path,
                        help="Path to the Vivado report_timing detail file.")
    parser.add_argument("--bucketize", action="store_true",
                        help=("Collapse [<digits>] indices in source/dest "
                              "and keep only the worst slack per bucket."))
    parser.add_argument("--include-met", action="store_true",
                        help=("Also emit Slack (MET) paths. By default only "
                              "Slack (VIOLATED) entries are kept."))
    parser.add_argument("--format", choices=["tsv", "csv", "json"],
                        default="tsv",
                        help="Output format (default: tsv).")
    parser.add_argument("--output", "-o", type=Path,
                        help="Output file (default: stdout).")

    args = parser.parse_args(argv)

    if not args.input.is_file():
        print(f"error: {args.input}: no such file", file=sys.stderr)
        return 2

    with args.input.open() as f:
        violations = list(parse_violations(f, include_met=args.include_met))

    if args.bucketize:
        violations = bucketize_worst(violations)

    # Sort by slack ascending so worst (most-negative) is first.
    violations.sort(key=lambda v: v.slack_ns)

    out_ctx = (args.output.open("w") if args.output
               else _StdoutKeeper(sys.stdout))
    with out_ctx as out:
        if args.format == "json":
            write_json(violations, out)
        else:
            write_tabular(violations, out,
                          delimiter="\t" if args.format == "tsv" else ",")

    print(f"# {len(violations)} violation(s) "
          f"{'(bucketized)' if args.bucketize else '(all)'} "
          f"from {args.input}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
