#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Build the cache-ip reference comparison tables (cache-ip common-ip TASK-003).

Reads the newest single-core (--ci1-idle) depth-sweep JSON of each rig --
amber bin N, jet bin N, the HPDcache reference rig, the CVA6 write-back
reference rig -- and the out-of-context summaries written by
fpga/tcl/ooc_cache.tcl, and prints Markdown tables: cycles per transaction
and mean latency per config and depth, the MLP row, and the cache-only
area / timing row. A rig whose JSON is missing shows as "pending", never as
a number. Usage: ref_compare.py [--out FILE] (default: stdout)."""
from __future__ import annotations
import argparse
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE_IP = os.path.normpath(os.path.join(HERE, ".."))          # .../Genesys2/cache-ip/ref
RIGS = os.path.normpath(os.path.join(CACHE_IP, ".."))         # .../Genesys2/cache-ip
RESULTS = {
    "amber":    f"{RIGS}/amber/results/perf_sweep_bin*_single_*.json",
    "jet":      f"{RIGS}/jet/results/perf_sweep_bin*_single_*.json",
    "HPDcache": f"{RIGS}/ref/results/perf_sweep_bin*_single_*.json",
    "CVA6 WB":  f"{RIGS}/ref/results/perf_sweep_cva6_bin*_single_*.json",
    # jet-prime in the same slot with NO pair fabric (TASK-001):
    #   s1 = jet's RTL as forked (bin 1): splits jet's miss cost into
    #        fabric and cache;
    #   s2 = step 2, jet_prime_fill with one read ID per MSHR entry (bin 2):
    #        several fills in flight, completing in any order;
    #   s3 = step 3, the jet-prime PAIR through the pipelined
    #        jet_prime_pair_fabric (REF_CACHE_SEL=3, injector 1 idle): the
    #        jet rig's structure with jet-prime's RTL -- against s2 the
    #        fabric's cost to a single core, against jet the rebuild
    #        (bin 3 = step 4's fabric with the memory-AR fixes);
    #   s5 = step 5, the single-miss path: the fill launch no longer waits
    #        behind the victim capture (the engine holds the beats
    #        instead) and the commit answers three cycles after the last
    #        beat (bin 4, the same pair rig).
    "jet-prime s1": f"{RIGS}/ref/results/perf_sweep_jetp_bin1_single_*.json",
    "jet-prime s2": f"{RIGS}/ref/results/perf_sweep_jetp_bin2_single_*.json",
    "jet-prime s3": f"{RIGS}/ref/results/perf_sweep_jetpp_bin3_single_*.json",
    "jet-prime s5": f"{RIGS}/ref/results/perf_sweep_jetpp_bin4_single_*.json",
}
OOC = {
    "amber": "amber", "jet": "jet", "HPDcache": "hpd", "CVA6 WB": "cva6",
    "jet-prime s1": "jetp_step1", "jet-prime s2": "jetp",
    # s3 is the s2 cache behind a fabric: the cache-only row is s2's
    "jet-prime s3": "jetp",
    # s5 changes the cache (control + fill engine): its own OOC row
    "jet-prime s5": "jetp5",
}
OOC_DIR = f"{CACHE_IP}/results/ooc"
COLS = list(RESULTS)
SHOW_DEPTHS = (1, 4, 16)
SHOW_CONFIGS = ("r4k_we0", "r4k_we255", "smoke4k_we64", "r16k_we64",
                "r64k_we64", "r64k_we255", "r128k_we64")


def newest(pattern):
    files = sorted(glob.glob(pattern))
    return files[-1] if files else None


def load(pattern):
    f = newest(pattern)
    if not f:
        return None, {}
    data = json.load(open(f))["results"]
    rows = {}
    for r in data:
        ci = r["ci0"]
        n = r["count"]
        rows[(r["config"], r.get("outstanding", 1))] = dict(
            cpt=ci["run_cycles"] / n, lat=ci["lat_sum"] / n, lat_min=ci["lat_min"],
            mlp=ci.get("outst_sum", 0) / max(ci["run_cycles"], 1),
            outst_max=ci.get("outst_max", 0), err=ci["err_flag"], done=r["done"])
    return os.path.basename(f), rows


def ooc_summary(name):
    f = f"{OOC_DIR}/{name}/10.0ns/summary.txt"
    if not os.path.exists(f):
        return None
    d = {}
    for line in open(f):
        k, _, v = line.strip().partition(" ")
        d[k] = v
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    srcs, tables = {}, {}
    for name, pat in RESULTS.items():
        srcs[name], tables[name] = load(pat)
    out = []
    out.append("Sources (newest single-core sweep per rig; injector 1 idle):\n")
    for name in COLS:
        out.append(f"- {name}: `{srcs[name]}`" if srcs[name] else f"- {name}: pending")
    out.append("")
    bad = [(n, k) for n in COLS for k, v in tables[n].items() if v["err"] or not v["done"]]
    out.append(f"Error flags / unfinished runs across all sources: {len(bad)}\n")

    def cell(name, key, field, fmt="{:.2f}"):
        v = tables[name].get(key)
        return fmt.format(v[field]) if v else "pending"

    out.append("### Cycles per transaction (injector 0, 20,000 transactions)\n")
    out.append("| config | depth | " + " | ".join(COLS) + " |")
    out.append("|---|---|" + "---|" * len(COLS))
    for cfg in SHOW_CONFIGS:
        for d in SHOW_DEPTHS:
            out.append(f"| {cfg} | {d} | " + " | ".join(cell(n, (cfg, d), "cpt") for n in COLS) + " |")
    out.append("")
    out.append("### Mean latency, accept to response (cycles)\n")
    out.append("| config | depth | " + " | ".join(COLS) + " |")
    out.append("|---|---|" + "---|" * len(COLS))
    for cfg in SHOW_CONFIGS:
        for d in SHOW_DEPTHS:
            out.append(f"| {cfg} | {d} | " + " | ".join(cell(n, (cfg, d), "lat") for n in COLS) + " |")
    out.append("")
    out.append("### Resident-hit floor and achieved parallelism\n")
    out.append("| rig | hit floor (lat_min, r4k_we0 d1) | MLP r64k_we64 d16 | OUTST_MAX r64k_we64 d16 |")
    out.append("|---|---|---|---|")
    for n in COLS:
        out.append(f"| {n} | {cell(n, ('r4k_we0', 1), 'lat_min', '{:.0f}')} | {cell(n, ('r64k_we64', 16), 'mlp')} | {cell(n, ('r64k_we64', 16), 'outst_max', '{:.0f}')} |")
    out.append("")
    out.append("### Cache alone, out of context (xc7k325t-2, 10 ns clock, synth + place + route)\n")
    out.append("| cache | LUT | FF | RAMB36 | RAMB18 | LUTRAM | WNS at 10 ns | worst path levels |")
    out.append("|---|---|---|---|---|---|---|---|")
    for n in COLS:
        s = ooc_summary(OOC[n])
        if not s:
            out.append(f"| {n} | pending | | | | | | |")
        else:
            out.append(f"| {n} | {s['lut']} | {s['ff']} | {s['ramb36']} | {s['ramb18']} | {s['lutram']} | {float(s['wns_ns']):+.3f} | {s['worst_levels']} |")
    text = "\n".join(out) + "\n"
    if args.out:
        open(args.out, "w").write(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
