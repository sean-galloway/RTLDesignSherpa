#!/usr/bin/env python3
"""Merge per-test coverage into a component report.

Replaces the (syntactically broken) inline `python -c` in the dv/tests Makefile
`coverage-report` target. Run from a component's `dv/tests` directory; it
auto-discovers every `<level>/coverage_data/per_test/*_summary.json` (protocol /
functional coverage) and every `<level>/local_sim_build/**/coverage.dat`
(Verilator line coverage), and writes markdown + json into an output dir.

Usage:
    python3 merge_testlevel_coverage.py [OUT_DIR=coverage_reports] [COMPONENT_NAME]
"""
import glob
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from datetime import datetime


def merge_protocol():
    merged = {'test_count': 0, 'tests': [], 'groups': {}}
    tp = tl = 0.0
    # Recursive so this works at a leaf area (coverage_data/... directly) AND at
    # a dispatcher level (fub/coverage_data/..., etc.). Level = the dir just
    # above coverage_data, or '.' when the area IS the cwd.
    for summ in sorted(glob.glob('**/coverage_data/per_test/*_summary.json', recursive=True)):
        _p = summ.split('/'); _i = _p.index('coverage_data')
        level = _p[_i - 1] if _i > 0 else '.'
        try:
            data = json.load(open(summ))
        except Exception:
            continue
        o = data.get('overall', {})
        merged['tests'].append({'name': data.get('test_name', os.path.basename(summ)),
                                'level': level,
                                'protocol_pct': o.get('protocol_pct', 0)})
        tp += o.get('protocol_pct', 0)
        merged['test_count'] += 1
        for gn, gd in data.get('protocol_coverage', {}).get('groups', {}).items():
            g = merged['groups'].setdefault(gn, {'points': {}})
            for pn, pd in gd.get('points', {}).items():
                p = g['points'].setdefault(pn, {'hits': 0, 'goal': pd.get('goal', 1)})
                p['hits'] += pd.get('hits', 0)
    if merged['test_count']:
        merged['overall_protocol_pct'] = tp / merged['test_count']
    else:
        merged['overall_protocol_pct'] = 0.0
    for gn, gd in merged['groups'].items():
        cov = sum(1 for p in gd['points'].values() if p['hits'] >= p['goal'])
        gd['covered'], gd['total'] = cov, len(gd['points'])
        gd['coverage_pct'] = (cov / len(gd['points']) * 100) if gd['points'] else 0
    return merged


def merge_line_coverage():
    """Merge every coverage.dat and compute per-RTL-file line coverage %."""
    # Recursive: matches leaf-area local_sim_build/**/coverage.dat AND
    # dispatcher-level <area>/local_sim_build/**/coverage.dat in one pass.
    dats = glob.glob('**/local_sim_build/**/coverage.dat', recursive=True)
    per_file = {}   # rtl file -> (covered, total)
    overall_cov = overall_tot = 0
    if not dats:
        return {}, 0.0, 0
    with tempfile.TemporaryDirectory() as ann:
        merged_dat = os.path.join(ann, 'merged.dat')
        # verilator_coverage --write accumulates matching points across .dat files
        try:
            subprocess.run(['verilator_coverage', '--write', merged_dat] + dats,
                           capture_output=True, text=True, timeout=600)
        except Exception:
            merged_dat = None
        src = merged_dat if merged_dat and os.path.exists(merged_dat) else None
        if src is None:
            return {}, 0.0, len(dats)
        adir = os.path.join(ann, 'annot')
        subprocess.run(['verilator_coverage', '--annotate', adir, src],
                       capture_output=True, text=True, timeout=600)
        for sv in glob.glob(os.path.join(adir, '*.sv')):
            cov = tot = 0
            lines = open(sv).read().splitlines()
            for ln in lines:
                m = re.match(r'^([ %])0*(\d+)', ln)   # coverage point line
                if m:
                    tot += 1
                    if int(m.group(2)) > 0:
                        cov += 1
            if tot:
                per_file[os.path.basename(sv)] = (cov, tot)
                overall_cov += cov
                overall_tot += tot
    pct = (overall_cov / overall_tot * 100) if overall_tot else 0.0
    return per_file, pct, len(dats)


def main():
    out_dir = sys.argv[1] if len(sys.argv) > 1 else 'coverage_reports'
    comp = sys.argv[2] if len(sys.argv) > 2 else os.path.basename(os.getcwd())
    os.makedirs(out_dir, exist_ok=True)

    m = merge_protocol()
    per_file, line_pct, n_dat = merge_line_coverage()
    ts = datetime.now().strftime('%Y%m%d_%H%M%S')
    m['overall_line_pct'] = line_pct
    m['line_files'] = {k: {'covered': v[0], 'total': v[1],
                           'pct': round(v[0] / v[1] * 100, 1)} for k, v in per_file.items()}
    json.dump(m, open(f'{out_dir}/latest_merged_coverage.json', 'w'), indent=2)
    json.dump(m, open(f'{out_dir}/merged_coverage_{ts}.json', 'w'), indent=2)

    R = [f'# {comp.upper()} Combined Coverage Report', '',
         f'**Generated:** {datetime.now():%Y-%m-%d %H:%M:%S}',
         f'**Tests:** {m["test_count"]}   **Coverage .dat merged:** {n_dat}', '',
         '## Summary', '', '| Metric | Coverage | Target | Status |', '|---|---|---|---|']
    ps = 'PASS' if m['overall_protocol_pct'] >= 80 else 'FAIL'
    ls = 'PASS' if line_pct >= 80 else 'FAIL'
    R += [f'| Protocol (functional) | {m["overall_protocol_pct"]:.1f}% | 80% | {ps} |',
          f'| Line (Verilator) | {line_pct:.1f}% | 80% | {ls} |', '',
          '## Tests by Level', '', '| Level | Tests |', '|---|---|']
    for lvl, c in sorted(Counter(t['level'] for t in m['tests']).items()):
        R.append(f'| {lvl} | {c} |')
    R += ['', '## Line Coverage by RTL File', '', '| File | Covered | Total | % |', '|---|---|---|---|']
    for f, d in sorted(m['line_files'].items(), key=lambda kv: kv[1]['pct']):
        R.append(f'| {f} | {d["covered"]} | {d["total"]} | {d["pct"]}% |')
    R += ['', '## Protocol Coverage by Group', '', '| Group | Covered | Total | % |', '|---|---|---|---|']
    for gn, gd in sorted(m['groups'].items()):
        R.append(f'| {gn} | {gd["covered"]} | {gd["total"]} | {gd.get("coverage_pct", 0):.1f}% |')
    gaps = [f'- **{gn}**: {pn}' for gn, gd in m['groups'].items()
            for pn, pd in gd['points'].items() if pd['hits'] < pd['goal']]
    R += ['', '## Uncovered Protocol Points', '']
    R += ([f'{len(gaps)} points not hit:', ''] + gaps[:150]) if gaps else ['All protocol points hit.']
    open(f'{out_dir}/latest_coverage_report.md', 'w').write('\n'.join(R))
    open(f'{out_dir}/coverage_report_{ts}.md', 'w').write('\n'.join(R))
    print(f'Coverage report: {out_dir}/latest_coverage_report.md')
    print(f'  Tests: {m["test_count"]}  Protocol: {m["overall_protocol_pct"]:.1f}%  '
          f'Line: {line_pct:.1f}%  (.dat merged: {n_dat})')


if __name__ == '__main__':
    main()
