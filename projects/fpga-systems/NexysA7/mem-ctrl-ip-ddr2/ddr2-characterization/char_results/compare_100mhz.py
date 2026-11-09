#!/usr/bin/env python3
"""granite vs LiteDRAM at one operating point, per profile, from the char CSVs beside this file.

    compare_100mhz.py <granite_tag> <granite_date> <litedram_tag> <litedram_date> [profiles...]

For every scenario of every profile: granite's best preset (max of write / read MB/s,
the figure the sweep write-up uses), LiteDRAM's one config, the ratio, and a verdict --
win / tie / lose, a tie being within 2 percent. Prints Markdown tables and the tally.
"""
from __future__ import annotations

import csv
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).parent
PROFILES = ("every", "windows", "half_threads", "half_burst", "half_burst8", "half_gap", "concurrent", "multigen")
TIE = 0.02


def read(path: Path) -> list[dict[str, str]]:
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def score(r: dict[str, str]) -> float:
    return max(float(r["wr_bw_mb_s"]), float(r["rd_bw_mb_s"]))


def fmt(r: dict[str, str]) -> str:
    return f"{float(r['wr_bw_mb_s']):.0f} / {float(r['rd_bw_mb_s']):.0f}"


def verdict(g: float, l: float) -> str:
    if g >= l * (1 + TIE):
        return "win"
    if g <= l * (1 - TIE):
        return "lose"
    return "tie"


def main(argv: list[str]) -> int:
    gtag, gdate, ltag, ldate = argv[1:5]
    profiles = argv[5:] or list(PROFILES)
    tally = defaultdict(int)
    for p in profiles:
        gpath = ROOT / f"char_granite_{gtag}_{p}_{gdate}.csv"
        lpath = ROOT / f"char_litedram_{ltag}_{p}_{ldate}.csv"
        if not gpath.exists() or not lpath.exists():
            print(f"\n### {p}: missing {gpath.name if not gpath.exists() else lpath.name}")
            continue
        g = read(gpath)
        l = {r["scenario"]: r for r in read(lpath)}
        configs = sorted({r["config"] for r in g})
        by_scen: dict[str, dict[str, dict[str, str]]] = defaultdict(dict)
        for r in g:
            by_scen[r["scenario"]][r["config"]] = r
        mism = sum(int(r["mismatched"]) for r in g) + sum(int(r["mismatched"]) for r in l.values())
        print(f"\n### {p}  ({len(g)} granite cells, {len(l)} LiteDRAM cells; mismatched beats: {mism})\n")
        print("| scenario | " + " | ".join(f"granite {c}" for c in configs) + " | LiteDRAM | granite best / LiteDRAM | verdict |")
        print("|---|" + "---|" * (len(configs) + 3))
        wins = 0
        n = 0
        for scen, rows in by_scen.items():
            if scen not in l:
                continue
            best = max(rows.values(), key=score)
            gb, lb = score(best), score(l[scen])
            v = verdict(gb, lb)
            tally[v] += 1
            wins += v == "win"
            n += 1
            cells = " | ".join(fmt(rows[c]) if c in rows else "-" for c in configs)
            print(f"| {scen} | {cells} | {fmt(l[scen])} | {gb:.0f} / {lb:.0f} = {gb / lb:.2f}x | {v} |")
        print(f"\ngranite ahead on {wins} of {n} scenarios (best preset vs LiteDRAM, max of write / read)")
    print(f"\n**Tally over {sum(tally.values())} shared cells: {tally['win']} win, {tally['tie']} tie, {tally['lose']} lose** (tie = within 2 percent)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
