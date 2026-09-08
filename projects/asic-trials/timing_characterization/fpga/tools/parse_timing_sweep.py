#!/usr/bin/env python3
"""Parse Vivado timing_summary.txt files captured by `make bitstream-sweep`
and roll them up into one CSV the spreadsheet builder can ingest.

Usage:
  parse_timing_sweep.py REPORTS_DIR OUT_CSV

REPORTS_DIR is `fpga/reports/`; it is expected to contain one or more
sweep_*MHz/ subdirectories produced by the sweep target.  Each contains
that run's timing_summary.txt + utilization_impl.txt.

Output CSV columns:
  freq_mhz, period_ns, group, wns_ns, slack_status, utilization_luts,
  utilization_ffs, utilization_brams, utilization_dsps

The 'group' column carries Vivado's path-group label (e.g. 'sys_clk_pin'
plus any other clock domains the design declared).  At the SWAG level
the main thing of interest is the WNS for sys_clk_pin under each target
period - that's the calibration signal.
"""
from __future__ import annotations
import csv
import re
import sys
from pathlib import Path

# Match Vivado's "Inter Clock Table" / "Design Timing Summary" headers
# and capture the per-group WNS lines that follow.
RE_DIR_FREQ = re.compile(r"sweep_(\d+)MHz")
RE_GROUP_HEAD = re.compile(
    r"^\s*Clock\s+WNS\(ns\)\s+", re.MULTILINE
)
RE_GROUP_LINE = re.compile(
    r"^\s*(\S+)\s+(-?\d+\.\d+)\s+(-?\d+\.\d+)\s+(-?\d+\.\d+)",
    re.MULTILINE,
)
RE_DESIGN_WNS = re.compile(
    r"Design Timing Summary[\s\S]*?WNS\(ns\)[\s\S]*?\n[-\s]+\n\s*(-?\d+\.\d+)",
    re.MULTILINE,
)

# Resource utilization regexes (Vivado prints | Slice LUTs | 1234 | etc.)
RE_UTIL_ROW = re.compile(
    r"^\|\s*(\S[^|]*?)\s*\|\s*(\d+)\s*\|", re.MULTILINE,
)


def parse_timing(path: Path) -> tuple[float | None, list[tuple[str, float]]]:
    txt = path.read_text(errors="ignore")
    # Design-level WNS (single number) for sanity.
    m = RE_DESIGN_WNS.search(txt)
    design_wns = float(m.group(1)) if m else None
    # Per-group rows that follow each "Clock WNS(ns) ..." header.
    groups = []
    for hdr in RE_GROUP_HEAD.finditer(txt):
        sub = txt[hdr.end():]
        # Stop at the next blank line / non-data row.
        for line in sub.splitlines():
            line = line.rstrip()
            if not line.strip():
                break
            m = RE_GROUP_LINE.match(line)
            if m:
                groups.append((m.group(1), float(m.group(2))))
            else:
                # Header continuation or non-data; bail.
                break
        # Only need the first table block (Inter-Clock).
        if groups:
            break
    return design_wns, groups


def parse_util(path: Path) -> dict[str, int]:
    """Extract LUT / FF / BRAM / DSP totals from a utilization report."""
    if not path.exists():
        return {}
    txt = path.read_text(errors="ignore")
    want = {
        "Slice LUTs": "luts",
        "Slice Registers": "ffs",
        "Block RAM Tile": "brams",
        "DSPs": "dsps",
    }
    result: dict[str, int] = {}
    for m in RE_UTIL_ROW.finditer(txt):
        label = m.group(1).strip()
        if label in want and want[label] not in result:
            result[want[label]] = int(m.group(2))
    return result


def main():
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    reports_dir = Path(sys.argv[1])
    out_csv = Path(sys.argv[2])

    rows: list[dict] = []
    for sub in sorted(reports_dir.iterdir()):
        if not sub.is_dir():
            continue
        m = RE_DIR_FREQ.match(sub.name)
        if not m:
            continue
        freq = int(m.group(1))
        period = round(1000.0 / freq, 4)
        ts = sub / "timing_summary.txt"
        util_imp = sub / "utilization_impl.txt"
        if not ts.exists():
            print(f"  skip {sub.name}: no timing_summary.txt", file=sys.stderr)
            continue
        design_wns, groups = parse_timing(ts)
        util = parse_util(util_imp)
        base = dict(freq_mhz=freq, period_ns=period,
                    utilization_luts=util.get("luts", ""),
                    utilization_ffs=util.get("ffs", ""),
                    utilization_brams=util.get("brams", ""),
                    utilization_dsps=util.get("dsps", ""))
        if not groups:
            # Fall back to design-level WNS only.
            rows.append({**base, "group": "design", "wns_ns": design_wns,
                         "slack_status": "PASS" if design_wns and design_wns >= 0
                                          else "FAIL"})
        else:
            for grp, wns in groups:
                rows.append({**base, "group": grp, "wns_ns": wns,
                             "slack_status": "PASS" if wns >= 0 else "FAIL"})

    if not rows:
        print("no sweep results found", file=sys.stderr)
        return 1

    cols = ["freq_mhz", "period_ns", "group", "wns_ns", "slack_status",
            "utilization_luts", "utilization_ffs",
            "utilization_brams", "utilization_dsps"]
    with out_csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"wrote {out_csv} ({len(rows)} rows)")


if __name__ == "__main__":
    sys.exit(main())
