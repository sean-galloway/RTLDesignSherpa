#!/usr/bin/env python3
"""Render the monitor characterization sweep as Markdown tables (amba TASK-034).

Reads reports/summary.csv (one row per run; the latest row per (module, part)
wins) plus each run's power.txt (vectorless dynamic power -- an estimate for
comparing variants, never a measurement) and prints, per part:

  1. every module: LUTs, FFs, BRAM, WNS register-to-register and including the
     out-of-context I/O budget (30 % of the period on every data pin; a miss
     there is a primary-input path, not the block), worst logic levels, power
  2. the monitor's own cost: monitored wrapper minus the plain block it wraps
     (axi4_master_rd_mon - axi4_master_rd, and so on), full against lite,
     with and without clock gating

Usage: bin/summary_table.py [reports/summary.csv]
"""
import csv
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
SRC = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "reports" / "summary.csv"
PARTS = {"xc7k325tffg900-2": "Kintex-7 325T -2 (Genesys 2)",
         "xc7a100tcsg324-1": "Artix-7 100T -1 (Nexys A7)"}
# monitored wrapper -> the plain block it wraps (the monitor is the difference)
BASE = {
    "axi4_master_rd_mon": "axi4_master_rd", "axi4_master_rd_monlite": "axi4_master_rd",
    "axi4_master_rd_mon_cg": "axi4_master_rd_cg", "axi4_master_rd_monlite_cg": "axi4_master_rd_cg",
    "axi4_master_wr_mon": "axi4_master_wr", "axi4_master_wr_monlite": "axi4_master_wr",
    "axi4_slave_rd_mon": "axi4_slave_rd", "axi4_slave_rd_monlite": "axi4_slave_rd",
    "axi5_master_rd_mon": "axi5_master_rd", "axi5_master_rd_monlite": "axi5_master_rd",
    "axil4_master_rd_mon": "axil4_master_rd", "axil4_master_rd_monlite": "axil4_master_rd",
    "axil4_master_wr_mon": "axil4_master_wr", "axil4_master_wr_monlite": "axil4_master_wr",
}


def power_w(module: str, part: str) -> str:
    f = HERE / "reports" / f"{module}__{part}" / "power.txt"
    if not f.is_file():
        return "-"
    m = re.search(r"\|\s*Dynamic \(W\)\s*\|\s*([0-9.]+)", f.read_text(errors="ignore"))
    return f"{float(m.group(1)) * 1000:.0f} mW" if m else "-"


def main() -> int:
    if not SRC.is_file():
        sys.exit(f"no summary at {SRC}; run bin/monitor_synth_sweep.sh first")
    rows = {}
    with SRC.open() as fh:
        for r in csv.DictReader(fh):
            rows[(r["bridge"], r["part"])] = r
    for part, label in PARTS.items():
        sel = {b: r for (b, p), r in rows.items() if p == part}
        if not sel:
            continue
        clk = next(iter(sel.values()))["clk_ns"]
        print(f"\n### {label}, clock constrained at {clk} ns, out of context\n")
        print("| Module | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | WNS incl. I/O (ns) | Worst logic levels | Dynamic power (est.) |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|")
        for b in sorted(sel):
            r = sel[b]
            print(f"| `{b}` | {int(r['luts']):,} | {int(r['ffs']):,} | {r['bram_tiles']} | {float(r['wns_reg2reg_ns']):+.3f} | {float(r['wns_ns']):+.3f} | {r['worst_logic_levels']} | {power_w(b, part)} |")
        print(f"\n#### The monitor's own cost ({label}): wrapper minus the plain block\n")
        print("| Monitored wrapper | Wraps | Monitor LUTs | Monitor FFs | Wrapper WNS reg-to-reg (ns) | Plain WNS reg-to-reg (ns) |")
        print("|---|---|---:|---:|---:|---:|")
        for w, base in BASE.items():
            if w in sel and base in sel:
                rw, rb = sel[w], sel[base]
                print(f"| `{w}` | `{base}` | {int(rw['luts']) - int(rb['luts']):,} | {int(rw['ffs']) - int(rb['ffs']):,} | {float(rw['wns_reg2reg_ns']):+.3f} | {float(rb['wns_reg2reg_ns']):+.3f} |")
    return 0


if __name__ == "__main__":
    sys.exit(main())
