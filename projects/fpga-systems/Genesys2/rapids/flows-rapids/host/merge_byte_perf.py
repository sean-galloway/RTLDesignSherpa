#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: merge_byte_perf
# Purpose: Merge the per-chunk results JSONs of the sim campaign (one
#          run_characterization.py --byte-perf --chunk K/N each, plus the
#          --byte-seq sequence runs) into ONE results file that
#          reports/make_byte_perf_report.py --results consumes. Marked
#          transport=sim-uart: sim data, not a board measurement.
#
# Documentation: projects/fpga-systems/Genesys2/rapids/flows-rapids/
# Subsystem: rapids_byte_harness

"""Usage: merge_byte_perf.py --out merged.json chunk1.json chunk2.json ...

Points are unioned by id (a duplicate id keeps the first and is reported),
sessions concatenated, device_stable recomputed as all-sessions-stable, and
`complete` recomputed against the full planned set of the profile -- a merge
of a partial chunk set must not claim completeness."""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import byte_perf  # noqa: E402


def merge(docs):
    perf = [d for d in docs if 'points' in d]
    seq = [s for d in docs for s in d.get('sequences', [])]
    if not perf and not seq:
        raise SystemExit("merge: no perf points and no sequences in any input")
    base = dict(perf[0]) if perf else {'schema': byte_perf.SCHEMA, 'profile': 'standard',
                                        'design': docs[0].get('design', {}), 'points': []}
    profiles = {d['profile'] for d in perf}
    if len(profiles) > 1:
        raise SystemExit(f"merge: chunks disagree on the profile: {sorted(profiles)}")
    points, dup = {}, []
    for d in perf:
        for r in d['points']:
            (dup.append(r['id']) if r['id'] in points else points.__setitem__(r['id'], r))
    sessions = [s for d in perf for s in d.get('sessions', [])]
    planned = byte_perf.build_points(base['profile'])
    base.update({
        'points': list(points.values()),
        'sessions': sessions,
        'sequences': seq,
        'planned': len(planned),
        'passed': sum(1 for r in points.values() if r['pass']),
        'failed': sum(1 for r in points.values() if not r['pass']),
        'complete': all(p['id'] in points for p in planned),
        'device_stable': all(s.get('stable') or s.get('aborted') for s in sessions),
        'transport': 'sim-uart',
        'sim': True,
        'merged_from': len(docs),
        'duplicate_ids': dup,
        'axi_monitor': _sum_monitors(docs),
        'rtl_states': [d['rtl_state'] for d in docs if 'rtl_state' in d],
    })
    base.pop('aborted', None)
    return base


def _sum_monitors(docs):
    keys = ('ar_bursts', 'aw_bursts', 'ends_on_4k', 'crosses_4k')
    tot = {k: sum(d.get('axi_monitor', {}).get(k, 0) for d in docs) for k in keys}
    tot['violations'] = [v for d in docs for v in d.get('axi_monitor', {}).get('violations', [])]
    return tot


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', required=True)
    ap.add_argument('inputs', nargs='+')
    a = ap.parse_args(argv)
    docs = []
    for p in a.inputs:
        with open(p) as fh:
            docs.append(json.load(fh))
    m = merge(docs)
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, 'w') as fh:
        json.dump(m, fh, indent=1)
    print(f"merged {len(docs)} files -> {a.out}: {len(m['points'])}/{m['planned']} points "
          f"({m['passed']} pass, {m['failed']} fail), complete={m['complete']}, "
          f"{len(m['sequences'])} sequence runs, duplicates={len(m['duplicate_ids'])}")
    return 0 if m['failed'] == 0 and all(s['pass'] for s in m['sequences']) else 1


if __name__ == '__main__':
    sys.exit(main())
