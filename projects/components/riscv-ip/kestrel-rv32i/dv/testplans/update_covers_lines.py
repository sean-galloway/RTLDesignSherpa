#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Regenerate a kestrel testplan's covers_lines from real Verilator coverage.

For each functional scenario with a test_function, merges the coverage.dat
of every cell of that test (dv/tests/local_sim_build/<test>_<level>/, all
levels), annotates it with verilator_coverage, and writes the lines of the
plan's rtl_file the test covered -- the annotate numbering and hit rule
bin/cov_utils/verify_testplan_coverage.py checks with.  Only the
covers_lines lines of the YAML are rewritten (comments and layout stay); a
scenario without one gets it after its `status:` line.  Scenarios that share
a test get the same lines: this records what each test exercises, nothing
finer.  A scenario whose cells are named apart from their cocotb test (the
same test built with different parameters) names them with `sim_cell:`.

Run AFTER a clean coverage regression (in kestrel-rv32i/dv/tests):

    make clean-all && COVERAGE=1 make run-all-full-parallel
    python3 ../testplans/update_covers_lines.py kestrel_core_testplan.yaml ...

Then check with the repo verifier (merged data from `make coverage-report`).
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

import yaml

TESTPLANS = Path(__file__).resolve().parent
SIM_ROOT = TESTPLANS.parent / 'tests' / 'local_sim_build'
REPO = TESTPLANS.parents[5]
ANNOTATED_RE = re.compile(r'^([ %~])0*(\d+)')
LEVELS = ('gate', 'func', 'full')


def cell_dats(test_function: str) -> list[str]:
    """coverage.dat of every level cell of one cocotb test.  Cells are named
    <cocotb test>_<level>, or <pytest function>_<level> for the tests whose
    runner names them after the pytest wrapper (test_kestrel_regfile)."""
    prefixes = {test_function, test_function.replace('cocotb_test_', 'test_', 1)}
    dats = []
    for p in prefixes:
        for lvl in LEVELS:
            dat = SIM_ROOT / f'{p}_{lvl}' / 'coverage.dat'
            if dat.exists():
                dats.append(str(dat))
    return sorted(set(dats))


def covered_lines(dats: list[str], rtl_basename: str) -> list[int]:
    """Lines of rtl_basename with a hit count > 0 in the merged dats."""
    with tempfile.TemporaryDirectory() as tmp:
        merged = dats[0]
        if len(dats) > 1:
            merged = str(Path(tmp) / 'merged.dat')
            subprocess.run(['verilator_coverage', '--write', merged] + dats,
                           check=True, capture_output=True)
        ann = Path(tmp) / 'ann'
        ann.mkdir()
        subprocess.run(['verilator_coverage', '--annotate', str(ann), merged],
                       check=True, capture_output=True)
        src = ann / rtl_basename
        if not src.exists():
            return []
        lines = src.read_text(errors='replace').splitlines()
        offset = 1 if lines and 'verilator_coverage annotation' in lines[0] else 0
        return [n for n, line in enumerate(lines[offset:], start=1)
                if (m := ANNOTATED_RE.match(line)) and int(m.group(2)) > 0]


def fmt_lines(nums: list[int], indent: str = '    ') -> list[str]:
    """covers_lines: [...] wrapped at 80 columns, continuation aligned."""
    head = f'{indent}covers_lines: ['
    out, cur = [], head
    for i, n in enumerate(nums):
        tok = f'{n}' + (', ' if i < len(nums) - 1 else '')
        if len(cur) + len(tok.rstrip()) > 79:
            out.append(cur.rstrip())
            cur = ' ' * len(head) + tok
        else:
            cur += tok
    out.append(cur + ']')
    return out


def update(plan_path: Path) -> None:
    plan = yaml.safe_load(plan_path.read_text())
    rtl = Path(plan['rtl_file']).name
    wanted = {}
    for sc in plan.get('functional_scenarios', []):
        tf = sc.get('test_function', '')
        dats = cell_dats(sc.get('sim_cell', tf))   # sim_cell: a cell named apart from its test
        if not dats:
            print(f'  {sc["id"]:8} {tf}: no coverage cells -- left unchanged')
            continue
        wanted[sc['id']] = covered_lines(dats, rtl)
        print(f'  {sc["id"]:8} {tf}: {len(dats)} cells, {len(wanted[sc["id"]])} lines of {rtl}')

    missing = {sc['id'] for sc in plan.get('functional_scenarios', [])
               if 'covers_lines' not in sc}
    text = plan_path.read_text().splitlines()
    out, sid, i = [], None, 0
    while i < len(text):
        line = text[i]
        m = re.match(r'\s*- id:\s*(\S+)', line)
        if m:
            sid = m.group(1)
        if sid in wanted and re.match(r'\s*covers_lines:', line):
            while not text[i].rstrip().endswith(']'):    # drop a wrapped list
                i += 1
            out += fmt_lines(wanted.pop(sid))
            i += 1
            continue
        out.append(line)
        if sid in wanted and sid in missing and re.match(r'\s*status:', line):
            out += fmt_lines(wanted.pop(sid))
        i += 1
    plan_path.write_text('\n'.join(out) + '\n')
    if wanted:
        sys.exit(f'{plan_path.name}: scenarios not rewritten: {sorted(wanted)}')


def main(argv: list[str]) -> None:
    if not argv:
        sys.exit(__doc__)
    for name in argv:
        p = TESTPLANS / name
        print(p.name)
        update(p)


if __name__ == '__main__':
    main(sys.argv[1:])
