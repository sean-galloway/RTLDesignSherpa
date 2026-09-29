#!/usr/bin/env python3
"""Render reports/summary.csv as the Markdown tables HAS 6.4 / 5.3 carry.

Latest row per (bridge, part) wins, so re-running one bridge refreshes its
line. Usage: bin/summary_table.py [reports/summary.csv]
"""
import csv
import sys
from pathlib import Path

SRC = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent / "reports" / "summary.csv")
PARTS = {"xc7a100tcsg324-1": "Artix-7 100T -1 (Nexys A7)", "xc7k325tffg900-2": "Kintex-7 325T -2 (Genesys 2)"}


def main():
    rows = {}
    with SRC.open() as fh:
        for r in csv.DictReader(fh):
            rows[(r["bridge"], r["part"])] = r
    for part, label in PARTS.items():
        sel = [r for (b, p), r in rows.items() if p == part]
        if not sel:
            continue
        print(f"\n{label}, clock constrained at {sel[0]['clk_ns']} ns\n")
        print("| Bridge | LUTs | FFs | BRAM | WNS reg-to-reg (ns) | Fmax est. (MHz) | Worst logic levels |")
        print("|---|---:|---:|---:|---:|---:|---:|")
        for r in sorted(sel, key=lambda r: r["bridge"]):
            print(f"| `{r['bridge']}` | {int(r['luts']):,} | {int(r['ffs']):,} | {r['bram_tiles']} | "
                  f"{float(r['wns_reg2reg_ns']):+.2f} | {r['fmax_reg2reg_mhz']} | {r['worst_logic_levels']} |")


if __name__ == "__main__":
    main()
