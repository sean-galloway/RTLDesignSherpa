#!/usr/bin/env python3
"""Regenerate stale `covers_lines` in testplan YAMLs from real per-scenario coverage.

The hand-written `covers_lines` in the STREAM testplans drifted off the RTL (they
pointed at license/header lines). This tool, run from a component's `dv/tests`
directory AFTER a coverage run, finds the Verilator `coverage.dat` of the test
that implements each `functional_scenario` and rewrites `covers_lines` to the RTL
lines that scenario's test actually covers. It edits the YAML with targeted text
surgery so comments/formatting are preserved (only the list items change).

Usage:
    python3 regen_covers_lines.py <testplan.yaml> [more.yaml ...]
    python3 regen_covers_lines.py --all <testplans_dir>
"""
import glob
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_testplan_coverage import get_covered_lines  # the fixed extractor

try:
    import yaml
except ImportError:
    sys.exit("PyYAML required")


def dats_for(test_function):
    """Map a testplan test_function to its coverage.dat file(s).

    Some testplans use param-matching scenario keys ("test_scheduler (basic_flow)"
    -> dir test_scheduler_basic_flow_*); others use descriptive keys ("func level")
    that don't appear in the pytest param id. When the key-specific glob misses,
    fall back to every .dat of that wrapper/module (the module's full coverage)."""
    m = re.match(r'\s*(\S+)\s*\(([^)]+)\)', test_function or '')
    wrapper = (m.group(1) if m else (test_function or '')).strip()
    out = []
    if m:
        key = m.group(2).strip()
        for p in (f'*/local_sim_build/{wrapper}_{key}_*/coverage.dat',
                  f'*/local_sim_build/{wrapper}_{key}/coverage.dat'):
            out += glob.glob(p)
    if not out and wrapper:
        # fallback: all tests of this wrapper/module (prefix match)
        out = glob.glob(f'*/local_sim_build/{wrapper}_*/coverage.dat')
    return out


def covered_lines(dats, module_basename):
    if not dats:
        return set()
    if len(dats) == 1:
        return get_covered_lines(dats[0], module_basename)
    with tempfile.TemporaryDirectory() as d:
        merged = os.path.join(d, 'm.dat')
        subprocess.run(['verilator_coverage', '--write', merged] + dats,
                       capture_output=True, timeout=300)
        return get_covered_lines(merged, module_basename) if os.path.exists(merged) else set()


def modules_of(tp, scenario):
    """The RTL file basename(s) a scenario's covers_lines refer to (multi-module
    testplans list several)."""
    rfs = ([scenario['rtl_file']] if scenario.get('rtl_file') else []) \
        or ([tp['rtl_file']] if tp.get('rtl_file') else []) \
        or tp.get('rtl_files', []) or []
    return [os.path.basename(r) for r in rfs]


def regen(yp, merged_dat=None, add_missing=False):
    with open(yp) as f:
        tp = yaml.safe_load(f)
    scns = tp.get('functional_scenarios', []) or []
    # module-level covered lines from the merged coverage (robust fallback when a
    # scenario's specific test .dat can't be name-matched).
    mod_cache = {}

    def module_lines(mods):
        key = tuple(mods)
        if key not in mod_cache:
            s = set()
            for m in mods:
                s |= get_covered_lines(merged_dat, m)
            mod_cache[key] = sorted(s)
        return mod_cache[key]

    new_lines = {}
    insert_ids = set()          # scenarios that need a NEW covers_lines inserted
    for s in scns:
        if 'covers_lines' not in s:
            if not add_missing:
                continue
            insert_ids.add(s.get('id'))
        mods = modules_of(tp, s)
        # Use the module(s)' covered lines from the SAME merged .dat that
        # verify_testplan_coverage checks against, so the two are consistent and
        # every scenario verifies fully. (Per-scenario .dat merges disagree with
        # the global merge on which lines are covered -- see regen notes.) When no
        # merged .dat is supplied, fall back to the scenario's own test .dat.
        cov = module_lines(mods) if merged_dat else \
            sorted(covered_lines(dats_for(s.get('test_function', '')), mods[0] if mods else ''))
        if cov:
            new_lines[s['id']] = cov
    if not new_lines:
        print(f"  {os.path.basename(yp)}: no scenarios updated (no coverage for module)")
        return
    # Targeted text surgery: track the current scenario id and rewrite its
    # covers_lines, handling BOTH inline (`covers_lines: [..]`) and block
    # (`covers_lines:` then `- N` lines) YAML formats. Emit inline to stay compact.
    lines = open(yp).read().split('\n')
    out = []
    cur = None
    i = 0
    changed = 0
    while i < len(lines):
        ln = lines[i]
        mid = re.match(r'^\s*-?\s*id:\s*["\']?([A-Za-z0-9_.\-]+)', ln)
        if mid:
            cur = mid.group(1)
        mcl = re.match(r'^(\s*)covers_lines:\s*(.*)$', ln)
        if mcl and cur in new_lines:
            indent = mcl.group(1)
            rest = mcl.group(2).strip()
            out.append(f'{indent}covers_lines: [{", ".join(str(n) for n in new_lines[cur])}]')
            i += 1
            if not rest:  # block form -> skip the following "- N" item lines
                while i < len(lines) and re.match(r'^\s*-\s*\d+\s*$', lines[i]):
                    i += 1
            changed += 1
            continue
        out.append(ln)
        # add-missing: insert covers_lines right after the scenario's status line
        ms = re.match(r'^(\s*)status:\s', ln)
        if ms and cur in insert_ids:
            out.append(f'{ms.group(1)}covers_lines: '
                       f'[{", ".join(str(n) for n in new_lines[cur])}]')
            insert_ids.discard(cur)
            changed += 1
        i += 1
    open(yp, 'w').write('\n'.join(out))
    print(f"  {os.path.basename(yp)}: regenerated covers_lines for {changed} scenario(s)")


def main():
    args = sys.argv[1:]
    merged = None
    add_missing = False
    if '--add-missing' in args:
        add_missing = True
        args.remove('--add-missing')
    if '--merged' in args:
        k = args.index('--merged')
        merged = args[k + 1]
        del args[k:k + 2]
    if not args:
        sys.exit(__doc__)
    if args[0] == '--all':
        yps = sorted(glob.glob(os.path.join(args[1], '*.yaml')))
    else:
        yps = args
    for yp in yps:
        regen(yp, merged_dat=merged, add_missing=add_missing)


if __name__ == '__main__':
    main()
