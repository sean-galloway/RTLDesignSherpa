#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""K4: the fabric benchmark's size, timing and repeat-sweep summaries.

    python3 bin/fb_k4.py size                  # board builds -> reports/k4/board_size_timing.csv
    python3 bin/fb_k4.py aggregate --since 20261016_070000
                                               # repeat sweeps -> reports/k4/{w2,w3}_summary.csv
    python3 bin/fb_k4.py aggregate --since 20261023_090000 --tag 20261023_lat
                                               # -> reports/k4/{w2,w3}_summary_20261023_lat.csv

size reads each leg's post-route reports (build-<leg>/fpga/reports/, written by
fpga/tcl/build_all.tcl). The fabric alone, out of context, is
bin/parse_ooc.py's (reports/ooc/README.md).

aggregate groups every sweep CSV at or after --since by its point -- W2:
(leg, channels, bytes per descriptor); W3: (leg, flavor, idle cycles,
outstanding) -- and reports n, mean, min, max and sample standard deviation,
latency columns included where the sweep recorded them (bin/fb_latency.py).
A point with a failing run is reported with its failure count, never averaged
over silently. Both print the Markdown tables the PRD's analysis section uses.
"""
from __future__ import annotations

import argparse
import csv
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path

AREA = Path(__file__).resolve().parent.parent
BOARD = AREA / 'reports' / 'board'
OUT = AREA / 'reports' / 'k4'
LEGS = (('a', 'A (bridge)'), ('a2', 'A2 (bridge, preset = "xbar")'),
        ('b1', 'B1 (AXI Crossbar)'), ('b2', 'B2 (SmartConnect)'),
        ('c1', 'C1 (Forencich axi_crossbar)'), ('c2', 'C2 (PULP axi_xbar)'),
        ('c3', 'C3 (LiteX AXI crossbar)'))
UTIL_ROWS = {'Slice LUTs': 'lut', 'LUT as Memory': 'lutram', 'Slice Registers': 'ff',
             'Block RAM Tile': 'bram', 'DSPs': 'dsp'}


def _util(path: Path) -> dict:
    out = {}
    for line in path.read_text().splitlines():
        cells = [c.strip() for c in line.split('|')]
        if len(cells) > 3 and cells[1] in UTIL_ROWS and UTIL_ROWS[cells[1]] not in out:
            out[UTIL_ROWS[cells[1]]] = cells[2]
    return out


def _timing(path: Path) -> dict:
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
        if line.strip().startswith('WNS(ns)'):
            vals = lines[i + 2].split()
            return {'wns_ns': vals[0], 'tns_ns': vals[1], 'whs_ns': vals[4], 'ths_ns': vals[5],
                    'met': 'All user specified timing constraints are met' in path.read_text()}
    raise ValueError(f"no design timing summary in {path}")


def size() -> int:
    rows = []
    for leg, label in LEGS:
        rep = AREA / f'build-{leg}' / 'fpga' / 'reports'
        u, t = rep / 'utilization_impl.txt', rep / 'timing_summary.txt'
        if not (u.exists() and t.exists()):
            print(f"fb_k4: {leg}: no post-route reports under {rep} (build it first)")
            return 1
        rows.append({'leg': leg, **_util(u), **_timing(t)})
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / 'board_size_timing.csv'
    with open(path, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    print("| Leg | WNS (ns) | WHS (ns) | LUTs | LUT as memory | FFs | BRAM | DSP |")
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    names = dict(LEGS)
    for r in rows:
        print(f"| {names[r['leg']]} | {float(r['wns_ns']):+.3f} | {float(r['whs_ns']):+.3f} | "
              f"{int(r['lut']):,} | {int(r['lutram']):,} | {int(r['ff']):,} | {r['bram']} | {r['dsp']} |")
    print(f"\n-> {path}")
    return 0


def _stamp(path: Path) -> str:
    m = re.search(r'_(\d{8}_\d{6})\.csv$', path.name)
    return m.group(1) if m else ''


def _stats(vals: list[float]) -> dict:
    return {'n': len(vals), 'mean': statistics.fmean(vals), 'min': min(vals), 'max': max(vals),
            'stdev': statistics.stdev(vals) if len(vals) > 1 else 0.0}


def _lat_from_bins(r: dict) -> dict:
    """Latency metrics recomputed from the raw *_bins columns, so every sweep
    file is judged by one rule whichever fb_latency wrote it."""
    import fb_latency as fl
    out = {}
    for h in fl.HISTS:
        bins = fl.from_bins_text(r.get(f'{h}_bins') or '')
        if not bins or sum(bins) != int(r.get(f'{h}_n') or -1):
            continue
        out[f'{h}_p50'] = fl.percentile_edge(bins, 0.5)
        out[f'{h}_p99'] = fl.percentile_edge(bins, 0.99)
        out[f'{h}_mean_est'] = fl.mean_estimate(bins)
    return out


def _collect(prefix: str, since: str, key, metrics) -> tuple[dict, dict]:
    groups, fails = defaultdict(lambda: defaultdict(list)), defaultdict(int)
    for leg, _ in LEGS:
        for f in sorted(BOARD.glob(f'{prefix}_{leg}_*.csv')):
            if _stamp(f) < since:
                continue
            for r in csv.DictReader(open(f)):
                r = {**r, **_lat_from_bins(r)}
                k = key(r)
                if r['pass'] != 'True':
                    fails[k] += 1
                    continue
                for m in metrics:
                    if r.get(m) not in (None, ''):
                        groups[k][m].append(float(r[m]))
    return groups, fails


def _write(path: Path, keys: tuple, groups: dict, fails: dict, metrics) -> list[dict]:
    rows = []
    for k in sorted(set(groups) | set(fails)):
        row = dict(zip(keys, k))
        row['failed_runs'] = fails.get(k, 0)
        for m in metrics:
            vals = groups.get(k, {}).get(m, [])
            if vals:
                st = _stats(vals)
                row.update({f'{m}_{s}': round(v, 4) for s, v in st.items()})
        rows.append(row)
    fields = list(dict.fromkeys(f for r in rows for f in r))
    with open(path, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    return rows


LAT_M = ('rd_first_p50', 'rd_first_p99', 'rd_first_mean_est', 'rd_last_mean_est',
         'wr_b_p50', 'wr_b_p99', 'wr_b_mean_est')


def aggregate(since: str, tag: str = '') -> int:
    sfx = f'_{tag}' if tag else ''
    OUT.mkdir(parents=True, exist_ok=True)
    w2_keys = ('leg', 'channels', 'bytes_per_desc')
    w2_m = ('bus_throughput_mbps', 'pct_of_peak', 'm_rd_util', 's_rd_util') + LAT_M
    g, f = _collect('w2', since, lambda r: (r['leg'], int(r['channels']), int(r['bytes_per_desc'])), w2_m)
    w2 = _write(OUT / f'w2_summary{sfx}.csv', w2_keys, g, f, w2_m)
    w3_keys = ('leg', 'flavor', 'idle_cycles', 'outstanding')
    w3_m = ('inj_share', 'stream_mibs', 'inj_mibs') + LAT_M
    g, f = _collect('w3', since, lambda r: (r['leg'], r['flavor'], int(r['idle_cycles']),
                                            int(r['outstanding'])), w3_m)
    w3 = _write(OUT / f'w3_summary{sfx}.csv', w3_keys, g, f, w3_m)
    names = dict(LEGS)
    print("W2: MiB/s mean (min-max), n, % of peak")
    for r in w2:
        if r['channels'] in (1, 8):
            print(f"  {names[r['leg']]:18s} {r['channels']}ch {r['bytes_per_desc'] // 1024:5d}K  "
                  f"{r.get('bus_throughput_mbps_mean', 0):7.1f} ({r.get('bus_throughput_mbps_min', 0):.1f}-"
                  f"{r.get('bus_throughput_mbps_max', 0):.1f}) n={r.get('bus_throughput_mbps_n', 0)} "
                  f"fail={r['failed_runs']}  {r.get('pct_of_peak_mean', 0):.1f}%")
    print("W3: injector share mean (min-max), n")
    for r in w3:
        print(f"  {names[r['leg']]:18s} {r['flavor']:6s} idle {r['idle_cycles']:4d} out {r['outstanding']}  "
              f"{100 * r.get('inj_share_mean', 0):5.1f}% ({100 * r.get('inj_share_min', 0):.1f}-"
              f"{100 * r.get('inj_share_max', 0):.1f}) n={r.get('inj_share_n', 0)} fail={r['failed_runs']}")
    print(f"\n-> {OUT / f'w2_summary{sfx}.csv'}, {OUT / f'w3_summary{sfx}.csv'}")
    return 1 if any(r['failed_runs'] for r in w2 + w3) else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest='cmd', required=True)
    sub.add_parser('size')
    a = sub.add_parser('aggregate')
    a.add_argument('--since', required=True, help="YYYYMMDD_HHMMSS: the first sweep file to include")
    a.add_argument('--tag', default='', help="write {w2,w3}_summary_<tag>.csv instead")
    args = ap.parse_args()
    return size() if args.cmd == 'size' else aggregate(args.since, args.tag)


if __name__ == '__main__':
    sys.exit(main())
