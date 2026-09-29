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

Quartus (``--tool quartus``, written by fpga/quartus/syn_sweep_quartus.tcl):

  parse_timing_sweep.py --tool quartus REPORTS_DIR/quartus OUT_CSV

Each sweep_*MHz/ holds <top>.sta.summary (per-model setup slack for the
clock), <top>.fit.summary (ALMs, registers, RAM blocks, DSPs) and
fub_slack.csv from sta_reports.tcl (worst setup path launched from each
FUB's registers: slack, data-path delay, logic levels). Rows come out in
the same columns as Vivado, with 'group' = 'clk:<model>' for the summary
rows and 'fub:<name>' for the per-FUB rows, plus two columns Vivado
leaves empty: data_delay_ns and logic_levels. utilization_luts carries
ALMs and utilization_brams the RAM-block count -- a LUT and an ALM are not
the same thing, so compare across tools by ratio, not by count.
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
# A row of the Intra Clock Table is `<clock>  WNS  TNS  <failing endpoints>
# <total endpoints>  WHS ...`: two floats, then two INTEGERS. The previous
# expression wanted three floats in a row, matched no real Vivado report
# (checked 2026-09-29 against rtl/amba/fpga/reports/*/timing_summary.txt),
# and every row silently fell back to the design-level "design" group.
RE_GROUP_LINE = re.compile(
    r"^\s*(\S+)\s+(-?\d+\.\d+)\s+(-?\d+\.\d+)\s+(\d+)\s+(\d+)",
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
        # RE_GROUP_HEAD stops after "WNS(ns)"; the rest of that header line
        # (TNS, endpoint counts, WHS ...) is not a data row, so start at the
        # NEXT line. Starting mid-header was the second reason no real report
        # ever yielded a per-clock row.
        nl = txt.find("\n", hdr.end())
        sub = txt[nl + 1:] if nl >= 0 else ""
        # Stop at the next blank line / non-data row.
        for line in sub.splitlines():
            line = line.rstrip()
            if not line.strip():
                break
            # the `-----  -------  ...` rule under the header is not data
            if set(line.strip()) <= set("- "):
                continue
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


RE_Q_BLOCK = re.compile(
    r"^Type\s*:\s*(?P<model>.+?) Model (?P<check>Setup|Hold|Minimum Pulse Width)"
    r" '(?P<clock>[^']+)'\s*\nSlack\s*:\s*(?P<slack>-?\d+\.\d+)",
    re.MULTILINE,
)
RE_Q_FIT_ROW = re.compile(r"^(?P<label>[^:\n]+?)\s*:\s*(?P<value>[\d,]+)(?:\s*/|\s*$)", re.MULTILINE)


def parse_quartus_summary(path: Path) -> list[tuple[str, float]]:
    """[(model, setup_slack)] for the clock, one per timing model."""
    out = []
    for m in RE_Q_BLOCK.finditer(path.read_text(errors="ignore")):
        if m.group("check") == "Setup":
            out.append((m.group("model"), float(m.group("slack"))))
    return out


def parse_quartus_fit(path: Path) -> dict[str, int]:
    """ALMs / registers / RAM blocks / DSPs from <top>.fit.summary."""
    if not path.exists():
        return {}
    want = {
        "Logic utilization (in ALMs)": "luts",
        "Total registers": "ffs",
        "Total RAM Blocks": "brams",
        "Total DSP Blocks": "dsps",
    }
    result: dict[str, int] = {}
    for m in RE_Q_FIT_ROW.finditer(path.read_text(errors="ignore")):
        label = m.group("label").strip()
        if label in want and want[label] not in result:
            result[want[label]] = int(m.group("value").replace(",", ""))
    return result


def parse_fub_slack(path: Path) -> list[dict]:
    """Rows of fub_slack.csv (sta_reports.tcl); [] when absent or header-only."""
    if not path.exists():
        return []
    with path.open(newline="") as f:
        return [r for r in csv.DictReader(f) if r.get("slack_ns")]


def quartus_rows(sub: Path, freq: int, period: float) -> list[dict]:
    summaries = sorted(sub.glob("*.sta.summary"))
    if not summaries:
        print(f"  skip {sub.name}: no *.sta.summary", file=sys.stderr)
        return []
    top = summaries[0].name[: -len(".sta.summary")]
    util = parse_quartus_fit(sub / f"{top}.fit.summary")
    base = dict(freq_mhz=freq, period_ns=period,
                utilization_luts=util.get("luts", ""),
                utilization_ffs=util.get("ffs", ""),
                utilization_brams=util.get("brams", ""),
                utilization_dsps=util.get("dsps", ""),
                data_delay_ns="", logic_levels="")
    rows = []
    for model, slack in parse_quartus_summary(summaries[0]):
        rows.append({**base, "group": f"clk:{model}", "wns_ns": slack,
                     "slack_status": "PASS" if slack >= 0 else "FAIL"})
    for r in parse_fub_slack(sub / "fub_slack.csv"):
        slack = float(r["slack_ns"])
        rows.append({**base, "group": f"fub:{r['fub']}", "wns_ns": slack,
                     "slack_status": "PASS" if slack >= 0 else "FAIL",
                     "data_delay_ns": r.get("data_delay_ns", ""),
                     "logic_levels": r.get("logic_levels", "")})
    return rows


def parse_args(argv: list[str]):
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--tool", choices=("vivado", "quartus"), default="vivado")
    ap.add_argument("reports_dir", type=Path)
    ap.add_argument("out_csv", type=Path)
    return ap.parse_args(argv)


def main(argv: list[str] | None = None):
    args = parse_args(sys.argv[1:] if argv is None else argv)
    reports_dir = args.reports_dir
    out_csv = args.out_csv

    rows: list[dict] = []
    for sub in sorted(reports_dir.iterdir()):
        if not sub.is_dir():
            continue
        m = RE_DIR_FREQ.match(sub.name)
        if not m:
            continue
        freq = int(m.group(1))
        period = round(1000.0 / freq, 4)
        if args.tool == "quartus":
            rows.extend(quartus_rows(sub, freq, period))
            continue
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
                    utilization_dsps=util.get("dsps", ""),
                    data_delay_ns="", logic_levels="")
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
            "utilization_brams", "utilization_dsps",
            "data_delay_ns", "logic_levels"]
    with out_csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"wrote {out_csv} ({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
