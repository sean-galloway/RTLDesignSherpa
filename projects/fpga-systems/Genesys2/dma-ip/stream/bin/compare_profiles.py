#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""STREAM against stream-g on the point profiles (stream TASK-020 phase 6).

Reads the board runs build-perf/results/<profile>_<date>_{fsm,g}.json
(host_characterize --json-output) and, when present, the simulation chunks
build-perf/results/sim/<profile>_{fsm,g}_*.json (make sim-<profile>), and
prints per point: cycles on each design, the ratio STREAM / stream-g (1.00 =
parity), MB/s, and whether the simulation matched the board cycle for cycle.
With --crossover it also prints, per shape, the smallest size from which every
larger size in the sweep stays within 10 %, 5 % and 1 % of STREAM (rapids HAS
Table 6.4.9's definition).

    bin/compare_profiles.py gscale --date 2026-10-24 [--crossover]
"""
from __future__ import annotations
import argparse
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, '..', 'build-perf', 'results')
BEAT_BYTES = 16


def load_board(profile: str, date: str, dut: str) -> dict:
    path = os.path.join(RESULTS, f'{profile}_{date}_{dut}.json')
    if not os.path.exists(path):
        sys.exit(f"missing board run: {path}")
    with open(path) as fh:
        return {d['config']: d['result'] for d in json.load(fh)}


def load_sim(profile: str, dut: str) -> dict:
    out = {}
    for path in sorted(glob.glob(os.path.join(RESULTS, 'sim', f'{profile}_{dut}_*.json'))):
        with open(path) as fh:
            for d in json.load(fh):
                out[d['config']] = d['result']
    return out


def parse_name(name: str):
    m = re.match(r'(beat|chain)_ch(\d+)_b(\d+)(?:_d(\d+))?$', name)
    return (m[1], int(m[2]), int(m[3]), int(m[4] or 1)) if m else (name, 0, 0, 1)


def mbps(r):
    return float(r['throughput_MBps'] or 0)


def table(profile, date, crossover):
    bf, bg = load_board(profile, date, 'fsm'), load_board(profile, date, 'g')
    sf, sg = load_sim(profile, 'fsm'), load_sim(profile, 'g')
    have_sim = bool(sf or sg)
    hdr = f"{'point':22s} {'ch':>2s} {'beats':>6s} {'d':>2s} {'STREAM cyc':>11s} {'stream-g cyc':>12s} {'f/g':>5s} {'STREAM MB/s':>11s} {'g MB/s':>8s}"
    if have_sim:
        hdr += f" {'sim STREAM':>10s} {'sim g':>8s}"
    print(hdr)
    rows = []
    for name in bf:
        if name not in bg:
            continue
        kind, ch, beats, d = parse_name(name)
        fc, gc = bf[name]['cycles'], bg[name]['cycles']
        ratio = fc / gc if fc and gc else 0.0
        line = f"{name:22s} {ch:2d} {beats:6d} {d:2d} {fc:11d} {gc:12d} {ratio:5.2f} {mbps(bf[name]):11.1f} {mbps(bg[name]):8.1f}"
        if have_sim:
            def mark(sim, board):
                if name not in sim or sim[name]['cycles'] is None:
                    return '--'
                return 'same' if sim[name]['cycles'] == board else f"{sim[name]['cycles']}"
            line += f" {mark(sf, fc):>10s} {mark(sg, gc):>8s}"
        print(line)
        rows.append((kind, ch, beats, d, fc, gc, ratio))
    if have_sim:
        for dut, sim, board in (('STREAM', sf, bf), ('stream-g', sg, bg)):
            n = sum(1 for k in sim if k in board and sim[k]['cycles'] is not None)
            same = sum(1 for k in sim if k in board and sim[k]['cycles'] == board[k]['cycles'])
            print(f"sim == board on {dut}: {same} of {n} points cycle-identical")
    if crossover:
        print("\nsmallest bytes per descriptor from which every larger point in the sweep is within the bound:")
        print(f"{'shape':34s} {'within 10%':>11s} {'within 5%':>10s} {'within 1%':>10s}")
        shapes = {}
        for kind, ch, beats, d, fc, gc, ratio in rows:
            shapes.setdefault((kind, ch, d), []).append((beats, ratio))
        for (kind, ch, d), pts in sorted(shapes.items()):
            pts.sort()
            if len(pts) < 3:
                continue
            def first(bound):
                ok_from = None
                for i in range(len(pts)):
                    if all(r >= 1 - bound for _, r in pts[i:]):
                        ok_from = pts[i][0]; break
                return size_label(ok_from * BEAT_BYTES) if ok_from else '> sweep'
            label = f"{'single descriptor' if kind == 'beat' else f'{d}-descriptor chain'}, {ch} ch busy"
            print(f"{label:34s} {first(0.10):>11s} {first(0.05):>10s} {first(0.01):>10s}")


def size_label(n):
    if n >= 1 << 20 and n % (1 << 20) == 0:
        return f"{n >> 20} MB"
    if n >= 1024 and n % 1024 == 0:
        return f"{n >> 10} KB"
    return f"{n} B"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('profile', choices=('gcompare', 'gscale', 'gscale1'))
    ap.add_argument('--date', required=True)
    ap.add_argument('--crossover', action='store_true')
    a = ap.parse_args()
    table(a.profile, a.date, a.crossover)


if __name__ == '__main__':
    main()
