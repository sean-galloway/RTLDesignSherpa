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
    # amber and jet are pinned to the bins the report's prose reads (amber
    # bin 11, jet bin 17); their newer single-core sweeps feed the two-core
    # table's ratios (DUAL below), not these columns.
    "amber":    f"{RIGS}/amber/results/perf_sweep_bin11_single_*.json",
    "jet":      f"{RIGS}/jet/results/perf_sweep_bin17_single_*.json",
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
    #        beat (bin 4, the same pair rig);
    #   s6 = TASK-002, the 2-cycle resident hit: the arriving request's
    #        data address leads in its capture cycle and a read hit answers
    #        in its classify cycle, and a write hit acks there (bin 7, the
    #        same pair rig; bins 5a and 6 are the first cuts -- 5a with the
    #        live lead starving the record path, 6 with the read side only
    #        -- kept as the measurements that found that, not columns).
    "jet-prime s1": f"{RIGS}/ref/results/perf_sweep_jetp_bin1_single_*.json",
    "jet-prime s2": f"{RIGS}/ref/results/perf_sweep_jetp_bin2_single_*.json",
    "jet-prime s3": f"{RIGS}/ref/results/perf_sweep_jetpp_bin3_single_*.json",
    "jet-prime s5": f"{RIGS}/ref/results/perf_sweep_jetpp_bin4_single_*.json",
    "jet-prime s6": f"{RIGS}/ref/results/perf_sweep_jetpp_bin7_single_*.json",
    # onyx (TASK-001 step 6): the same jet-prime pair behind onyx_ccu in the
    # pair fabric's place -- "onyx" with the memory read alongside the snoop
    # (REF_CACHE_SEL 4), "onyx-d" with the read deferred until the gather
    # (SEL 5, DEFER_AR). Against jet-prime s6 the manager swap alone.
    "onyx":   f"{RIGS}/ref/results/perf_sweep_onyx_bin*_single_*.json",
    "onyx-d": f"{RIGS}/ref/results/perf_sweep_onyxd_bin*_single_*.json",
}
OOC = {
    "amber": "amber", "jet": "jet", "HPDcache": "hpd", "CVA6 WB": "cva6",
    "jet-prime s1": "jetp_step1", "jet-prime s2": "jetp",
    # s3 is the s2 cache behind a fabric: the cache-only row is s2's
    "jet-prime s3": "jetp",
    # s5 changes the cache (control + fill engine): its own OOC row
    "jet-prime s5": "jetp5",
    # s6 changes the control's hit path: its own OOC row
    "jet-prime s6": "jetp6",
    # onyx changes the manager, not the cache: the cache row is s6's; the
    # managers have their own table below
    "onyx": "jetp6", "onyx-d": "jetp6",
}
# the two-port managers alone (18 slots, SNOOP_INFLIGHT 2)
OOC_MGR = {"jet_prime_pair_fabric": "jetp_fabric", "onyx_ccu (N_PORTS 2)": "onyx2"}
# onyx's exact counters (TASK-001 step 6b, D9): the newest DUAL sweep of each
# onyx mode that recorded them ("onyx" key per cell), plus the newest hot-set
# sweep (the hot16_we179 cell, built to reach the CleanUnique-DataTransfer
# and old-write-back corners). The D6 measure is reads wasted over reads
# issued in the parallel mode; the deferred mode's wasted count is its own
# check (should be 0).
# ONLY sweeps launched by the harness GO count as dual: every earlier "dual"
# file (bin1..bin7, named perf_sweep_<rig>_bin<N>_dual_*) started the two
# injectors with two UART writes >= 16 ms apart, so they ran one after the
# other (cache-ip common-ip BUG-001). Those files stay as records; they are
# not two-core measurements.
ONYX_CNT = {
    "onyx":   [f"{RIGS}/ref/results/perf_sweep_onyx_go_dual_*.json",
               f"{RIGS}/ref/results/perf_sweep_onyx_go_hot_dual_*.json"],
    "onyx-d": [f"{RIGS}/ref/results/perf_sweep_onyxd_go_dual_*.json",
               f"{RIGS}/ref/results/perf_sweep_onyxd_go_hot_dual_*.json"],
}
# Two cores at once: the newest dual sweep per coherent rig whose two
# injectors were launched by ONE harness GO (common-ip BUG-001). The value is
# the slower injector's cycles per transaction; the ratio is against the
# same bitstream's single-core sweep (injector 0, peer idle) where the GO
# pass recorded one, else the rig's single-core column in the first table.
DUAL = {
    "amber":        (f"{RIGS}/amber/results/perf_sweep_bin*_go_single_*.json",
                     f"{RIGS}/amber/results/perf_sweep_bin*_go_2*.json"),
    # jet: bin 21, the jet BUG-008 fix (the GO pass's bin 20 ran one
    # injector after the other wherever the peer's hits starved its miss)
    "jet":          (f"{RIGS}/jet/results/perf_sweep_bin21_bug008_single_*.json",
                     f"{RIGS}/jet/results/perf_sweep_bin21_bug008_2*.json"),
    # jet-prime s6: the jet-prime BUG-004 fix (CleanUnique -> CleanInvalid,
    # a memory read waits out a write to its line), onyx's BUG-001/002 fixes
    "jet-prime s6": (f"{RIGS}/ref/results/perf_sweep_jetpp_bug004_single_*.json",
                     f"{RIGS}/ref/results/perf_sweep_jetpp_bug004_dual_*.json"),
    "onyx":         (RESULTS["onyx"], f"{RIGS}/ref/results/perf_sweep_onyx_go_dual_*.json"),
    "onyx-d":       (RESULTS["onyx-d"], f"{RIGS}/ref/results/perf_sweep_onyxd_go_dual_*.json"),
}
DUAL_CONFIGS = ("r4k_we0", "r4k_we255", "smoke4k_we64", "r64k_we64", "r128k_we64",
                "disjoint64k_we64")
OOC_DIR = f"{CACHE_IP}/results/ooc"
# The same cache with USE_MONITOR=0 (MonBus observers and their arbiter tied
# off): HPDcache and CVA6 carry no equivalent, so the area row is shown both
# ways for the three that do. Missing dir shows as pending.
OOC_NOMON = {"amber": "amber_nomon", "jet": "jet_nomon", "jet-prime s6": "jetp6_nomon"}
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


def load_onyx(patterns):
    """per (config, depth): the onyx counters of the newest sweep per pattern
    that has them, merged; returns the source file names and the rows"""
    srcs, rows = [], {}
    for pattern in patterns:
        for f in reversed(sorted(glob.glob(pattern))):
            data = json.load(open(f))["results"]
            got = {(r["config"], r.get("outstanding", 1)): r["onyx"] for r in data if "onyx" in r}
            if got:
                srcs.append(os.path.basename(f))
                rows.update(got)
                break
    return srcs, rows


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
    out.append("")
    out.append("### The same, monitors off (USE_MONITOR=0; HPDcache and CVA6 have none to turn off)\n")
    out.append("| cache | LUT | FF | RAMB36 | RAMB18 | LUTRAM | WNS at 10 ns | worst path levels | LUT with monitors |")
    out.append("|---|---|---|---|---|---|---|---|---|")
    for n, d in OOC_NOMON.items():
        s, m = ooc_summary(d), ooc_summary(OOC[n])
        if not s:
            out.append(f"| {n} | pending | | | | | | | {m['lut'] if m else 'pending'} |")
        else:
            out.append(f"| {n} | {s['lut']} | {s['ff']} | {s['ramb36']} | {s['ramb18']} | {s['lutram']} | {float(s['wns_ns']):+.3f} | {s['worst_levels']} | {m['lut'] if m else 'pending'} |")
    out.append("")
    out.append("### The managers alone, out of context (xc7k325t-2, 10 ns clock; 18 slots, SNOOP_INFLIGHT 2)\n")
    out.append("| manager | LUT | FF | LUTRAM | WNS at 10 ns | worst path levels |")
    out.append("|---|---|---|---|---|---|")
    for n, d in OOC_MGR.items():
        s = ooc_summary(d)
        if not s:
            out.append(f"| {n} | pending | | | | |")
        else:
            out.append(f"| {n} | {s['lut']} | {s['ff']} | {s['lutram']} | {float(s['wns_ns']):+.3f} | {s['worst_levels']} |")
    out.append("### onyx counters, both injectors started by one GO (the D6 trade: reads issued, lines supplied, reads wasted)\n")
    osrc, ocnt = {}, {}
    for n, pats in ONYX_CNT.items():
        osrc[n], ocnt[n] = load_onyx(pats)
        out.append(f"- {n}: " + ", ".join(f"`{f}`" for f in osrc[n]) if osrc[n] else f"- {n}: pending")
    out.append("")
    out.append("| config | depth | mode | transactions | memory reads | lines supplied | reads wasted | wasted / issued | absorptions | write-backs | CleanUnique + DT | old write-backs |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
    for cfg in SHOW_CONFIGS + ("hot16_we179",):
        for d in SHOW_DEPTHS:
            for n in ONYX_CNT:
                c = ocnt[n].get((cfg, d))
                if not c:
                    out.append(f"| {cfg} | {d} | {n} | pending | | | | | | | | |")
                    continue
                frac = c["read_wasted"] / c["mem_read"] if c["mem_read"] else 0.0
                out.append(f"| {cfg} | {d} | {n} | {c['txn']} | {c['mem_read']} | {c['supplied']} | {c['read_wasted']} | {frac:.3f} | {c['absorb']} | {c['wb']} | {c.get('cu_dt', '-')} | {c.get('old_wb', '-')} |")
    out.append("")
    out.append("### Two cores at once (both injectors started by one GO; the slower injector, cycles per transaction, and x its single-core figure)\n")
    dsrc, dtab, done1 = {}, {}, {}
    for n, (single_pat, pat) in DUAL.items():
        ssrc, done1[n] = load(single_pat)
        f = newest(pat)
        dsrc[n] = (f"`{os.path.basename(f)}`" + (f" against `{ssrc}`" if ssrc else "")) if f else None
        dtab[n] = {}
        if f:
            for r in json.load(open(f))["results"]:
                cyc = max(r["ci0"]["run_cycles"], r["ci1"]["run_cycles"])
                dtab[n][(r["config"], r.get("outstanding", 1))] = (
                    cyc / r["count"], r["done"] and not (r["ci0"]["err_flag"] or r["ci1"]["err_flag"]))
        out.append(f"- {n}: {dsrc[n]}" if dsrc[n] else f"- {n}: pending")
    dbad = sum(1 for n in DUAL for v in dtab[n].values() if not v[1])
    out.append("")
    out.append(f"Error flags / unfinished runs across the dual sources: {dbad}\n")
    out.append("| config | depth | " + " | ".join(DUAL) + " |")
    out.append("|---|---|" + "---|" * len(DUAL))
    for cfg in DUAL_CONFIGS:
        for d in SHOW_DEPTHS:
            cells = []
            for n in DUAL:
                v = dtab[n].get((cfg, d))
                one = done1[n].get((cfg, d))
                if not v:
                    cells.append("pending")
                elif one:
                    cells.append(f"{v[0]:.2f} ({v[0] / one['cpt']:.2f}x)")
                else:
                    cells.append(f"{v[0]:.2f}")
            out.append(f"| {cfg} | {d} | " + " | ".join(cells) + " |")
    text = "\n".join(out) + "\n"
    if args.out:
        open(args.out, "w").write(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
