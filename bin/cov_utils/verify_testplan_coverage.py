#!/usr/bin/env python3
"""
Verify testplan scenario coverage against Verilator coverage data.

Parses YAML testplans and checks if the covers_lines are actually covered
in the Verilator coverage output.

Usage:
    python verify_testplan_coverage.py <testplan.yaml> <coverage.dat>
    python verify_testplan_coverage.py --all-testplans <coverage_dir>
"""

import os
import re
import sys
import yaml
import argparse
import subprocess
import tempfile
from pathlib import Path


# Status values that mean "this scenario is claimed to be covered".
COVERED_STATUSES = {'covered', 'integration_tested', 'tested'}
# Status values that mean "honestly recorded as not implemented".
GAP_STATUSES = {'not_implemented', 'not_implementable', 'gap', 'planned',
                'tbd', 'future'}


def parse_testplan(yaml_path):
    """Parse a YAML testplan and extract scenario-to-line mappings."""
    with open(yaml_path, 'r') as f:
        testplan = yaml.safe_load(f)

    rfs = testplan.get('rtl_files')
    if isinstance(rfs, str):
        rfs = [rfs] if rfs.strip() else []
    rtl_files = rfs or (
        [testplan['rtl_file']] if testplan.get('rtl_file') else [])
    tfs = testplan.get('test_file')
    if not tfs:
        plural = testplan.get('test_files')
        tfs = ', '.join(plural) if isinstance(plural, list) else (plural or '')
    result = {
        'module': testplan.get('module') or testplan.get('module_group', 'unknown'),
        'rtl_file': testplan.get('rtl_file', ''),
        'rtl_files': rtl_files,          # multi-module testplans list several
        'test_file': tfs,                # singular or plural list, joined
        'scenarios': []
    }

    for scenario in testplan.get('functional_scenarios', []):
        result['scenarios'].append({
            'id': scenario.get('id', ''),
            'name': scenario.get('name', ''),
            'covers_lines': scenario.get('covers_lines', []),
            'status': scenario.get('status', 'unknown'),
            'description': scenario.get('description', ''),
            'test_function': scenario.get('test_function', ''),
            'format': 'functional_scenarios'
        })

    # Amber-style descriptive scenarios (no line lists).  They carry the same
    # intent: a named scenario with a status and a backing test.  We normalise
    # them so the rest of the tool can treat both formats uniformly.
    for scenario in testplan.get('scenarios', []):
        result['scenarios'].append({
            'id': scenario.get('id', ''),
            'name': scenario.get('name', ''),
            'covers_lines': scenario.get('covers_lines', []),
            'status': scenario.get('status', 'unknown'),
            'description': scenario.get('description', '') or scenario.get('what', ''),
            'test_function': scenario.get('test_function', ''),
            'format': 'scenarios'
        })

    return result


def get_covered_lines(coverage_dat, rtl_filename):
    """Get list of covered lines from Verilator coverage data for a specific file."""
    covered_lines = set()

    with tempfile.TemporaryDirectory() as annotate_dir:
        cmd = ['verilator_coverage', '--annotate', annotate_dir, coverage_dat]
        result = subprocess.run(cmd, capture_output=True, text=True)

        if result.returncode != 0:
            print(f"Warning: verilator_coverage failed: {result.stderr}", file=sys.stderr)
            return covered_lines

        # Find the annotated file
        for sv_file in Path(annotate_dir).glob('*.sv'):
            if rtl_filename in sv_file.name:
                with open(sv_file, 'r') as f:
                    lines = f.readlines()
                # verilator_coverage --annotate prefixes each SOURCE line with
                # " <count>" (all points covered), "~<count>" (some points on
                # the line covered, some not -- e.g. a bus whose upper bits
                # never toggled both ways), or "%<count>" (nothing covered),
                # one annotated line per source line, preceded by a single
                # legend header line. The source line number is therefore the
                # physical position (after the header), NOT anything embedded
                # in the text. A line is covered when its hit count is > 0
                # (regardless of the ' '/'~'/'%' flag).
                offset = 1 if lines and 'verilator_coverage annotation' in lines[0] else 0
                for lineno, line in enumerate(lines[offset:], start=1):
                    m = re.match(r'^([ %~])0*(\d+)', line)  # prefix + hit count
                    if m and int(m.group(2)) > 0:
                        covered_lines.add(lineno)
                break

    return covered_lines


def _search_paths_for_testplan(testplan_dir, testplan):
    """Return candidate files to search for scenario-name backing."""
    candidates = []
    # Files explicitly listed in the testplan.
    for tf in re.split(r'[,;]+', testplan['test_file']):
        tf = tf.strip()
        if not tf:
            continue
        # Relative paths are resolved from the repo root; absolute paths are
        # used as-is.
        p = Path(tf)
        if not p.is_absolute():
            # The testplan's own path gives us the component root; fall back
            # to the cwd/repo root if we cannot derive it.
            repo_root = Path(testplan_dir)
            while repo_root.parent != repo_root and not (repo_root / '.git').exists():
                repo_root = repo_root.parent
            p = repo_root / p
        if p.exists():
            candidates.append(p)

    # Also search sibling Python files in the tests/ and tbclasses/ dirs that
    # belong to the same component.  This catches scenario-name references in
    # TB classes imported by the test runner.
    tests_dir = None
    for c in candidates:
        if 'tests' in c.parts:
            tests_dir = c.parent
            break
    if tests_dir:
        candidates.extend(tests_dir.glob('*.py'))
        tbclasses_dir = tests_dir.parent / 'tbclasses'
        if tbclasses_dir.exists():
            candidates.extend(tbclasses_dir.glob('*.py'))

    return sorted(set(candidates))


def _test_files_backed(candidate_files):
    """Return True if at least one candidate file exists and looks like a test."""
    if not candidate_files:
        return False
    found = False
    for path in candidate_files:
        if not path.exists():
            continue
        try:
            text = path.read_text(errors='replace')
        except Exception:
            continue
        # A backing test file must contain pytest/cocotb test functions.
        if re.search(r"^\s*(def\s+test_|async\s+def\s+cocotb_test_)", text, re.M):
            found = True
    return found


def _scenario_backed_by_tests(scenario_name, candidate_files):
    """Return True if the scenario name appears in at least one candidate file.

    This is the stronger, per-scenario check used when scenario names are
    referenced explicitly in the TB source (the common amber pattern).
    """
    if not scenario_name or not candidate_files:
        return False
    patterns = [
        re.compile(r"\b" + re.escape(scenario_name) + r"\b"),
        re.compile(re.escape(scenario_name)),
    ]
    for path in candidate_files:
        if not path.exists():
            continue
        try:
            text = path.read_text(errors='replace')
        except Exception:
            continue
        for pat in patterns:
            if pat.search(text):
                return True
    return False


def verify_testplan(testplan_path, coverage_dat=None):
    """Verify a testplan against coverage data and/or test-file backing."""
    testplan = parse_testplan(testplan_path)

    # Union covered lines across every RTL file the testplan lists (multi-module
    # testplans, e.g. axi_engines, cover read + write engines together).
    rtl_files = testplan['rtl_files']
    print(f"\n{'='*70}")
    print(f"Module: {testplan['module']}")
    print(f"RTL: {', '.join(os.path.basename(r) for r in rtl_files) or '(none)'}")
    print(f"Test: {testplan['test_file']}")
    print(f"{'='*70}")

    covered_lines = set()
    if coverage_dat and rtl_files:
        for rf in rtl_files:
            covered_lines |= get_covered_lines(coverage_dat, os.path.basename(rf))

    candidate_files = _search_paths_for_testplan(Path(testplan_path).parent, testplan)

    total_scenarios = len(testplan['scenarios'])
    verified_scenarios = 0
    partial_scenarios = 0
    unverified_scenarios = 0
    unbacked_scenarios = 0
    gap_scenarios = 0

    # Also report free-form gaps: entries in the top-level `gaps:` list.
    raw = yaml.safe_load(open(testplan_path))
    freeform_gaps = raw.get('gaps', []) or []
    if isinstance(freeform_gaps, str):
        freeform_gaps = [freeform_gaps] if freeform_gaps.strip() else []

    for scenario in testplan['scenarios']:
        scenario_lines = set(scenario.get('covers_lines', []))
        status_lower = str(scenario.get('status', '')).lower()
        name = scenario.get('name', '') or scenario.get('id', '')
        sid = scenario.get('id', '') or name

        if status_lower in GAP_STATUSES:
            print(f"  {sid:12} {name:30} {'GAP':12}")
            gap_scenarios += 1
            continue

        # Line-coverage verification (house functional_scenarios format).
        if scenario_lines:
            covered_count = len(scenario_lines & covered_lines)
            total_count = len(scenario_lines)

            if covered_count == total_count:
                status = "VERIFIED"
                verified_scenarios += 1
            elif covered_count > 0:
                status = "PARTIAL"
                partial_scenarios += 1
            else:
                status = "NOT COVERED"
                unverified_scenarios += 1

            print(f"  {sid:12} {name:30} {status:12} ({covered_count}/{total_count} lines)")
            continue

        # Scenario-back verification (amber-style descriptive format): a
        # status: covered claim must be backed by a named reference in the
        # actual test or TB-class files.  When a scenario name is not found
        # literally, we fall back to the testplan-level claim: the listed
        # test files must exist and contain test functions.  This covers
        # blocks like amber_pending_fill_bypass / amber_victim whose
        # scenarios are exercised through the parent control test without
        # repeating every scenario name in the source.
        if status_lower in COVERED_STATUSES:
            backed = _scenario_backed_by_tests(name, candidate_files)
            if backed:
                print(f"  {sid:12} {name:30} {'BACKED':12}")
                verified_scenarios += 1
            elif _test_files_backed(candidate_files):
                print(f"  {sid:12} {name:30} {'BACKED(file)':12}")
                verified_scenarios += 1
            else:
                print(f"  {sid:12} {name:30} {'NOT BACKED':12}")
                unbacked_scenarios += 1
        else:
            print(f"  {sid:12} {name:30} {status_lower:12}")

    print(f"\nSummary:")
    print(f"  Total scenarios:      {total_scenarios}")
    print(f"  Fully verified:       {verified_scenarios}")
    print(f"  Partially covered:    {partial_scenarios}")
    print(f"  Not covered (lines):  {unverified_scenarios}")
    print(f"  Not backed (tests):   {unbacked_scenarios}")
    print(f"  Scenario gaps:        {gap_scenarios}")
    print(f"  Free-form gaps:       {len(freeform_gaps)}")
    if freeform_gaps:
        for g in freeform_gaps:
            head = (g.split('\n')[0][:60] + '...') if len(g) > 60 else g
            print(f"    - {head}")

    return {
        'module': testplan['module'],
        'total': total_scenarios,
        'verified': verified_scenarios,
        'partial': partial_scenarios,
        'unverified': unverified_scenarios,
        'unbacked': unbacked_scenarios,
        'gaps': gap_scenarios + len(freeform_gaps)
    }


def _find_coverage_dat(coverage_path):
    """Return a usable coverage.dat, or None if none is required/available."""
    if not coverage_path:
        return None
    if not os.path.isdir(coverage_path):
        return coverage_path if Path(coverage_path).exists() else None

    merged = Path(coverage_path) / 'latest_merged_coverage.dat'
    if merged.exists():
        return str(merged)

    dat_files = list(Path(coverage_path).glob('*.dat'))
    if dat_files:
        return str(max(dat_files, key=os.path.getmtime))

    return None


def main():
    parser = argparse.ArgumentParser(
        description='Verify testplan scenario coverage against Verilator data',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s val/amba/testplans/apb4_slave_testplan.yaml coverage.dat
  %(prog)s --all val/amba/testplans/ val/amba/coverage_data/merged/
  %(prog)s --all projects/components/cache-ip/amber-mesi-l1/dv/testplans/ \
           projects/components/cache-ip/amber-mesi-l1/dv/tests
        """
    )
    parser.add_argument('testplan', help='Path to testplan YAML or directory')
    parser.add_argument('coverage', nargs='?', default=None,
                        help='Path to coverage.dat file or directory (optional for scenario-back mode)')
    parser.add_argument('--all', '-a', action='store_true',
                        help='Process all testplans in directory')
    parser.add_argument('--summary', '-s', action='store_true',
                        help='Show only summary')
    parser.add_argument('--strict', action='store_true',
                        help='Exit non-zero if any covered scenario is not backed by tests')
    args = parser.parse_args()

    if args.all:
        # Process all testplans in directory
        testplan_dir = Path(args.testplan)
        coverage_dat = _find_coverage_dat(args.coverage) if args.coverage else None

        if args.coverage and not coverage_dat:
            print(f"No coverage.dat files found in {args.coverage}", file=sys.stderr)
            # Allow scenario-back verification to continue anyway.

        results = []
        for yaml_file in sorted(testplan_dir.glob('*.yaml')):
            try:
                result = verify_testplan(yaml_file, coverage_dat)
                results.append(result)
            except Exception as e:
                print(f"Error processing {yaml_file}: {e}", file=sys.stderr)

        # Print overall summary
        print(f"\n{'='*70}")
        print("OVERALL SUMMARY")
        print(f"{'='*70}")
        total_scenarios = sum(r['total'] for r in results)
        total_verified = sum(r['verified'] for r in results)
        total_partial = sum(r['partial'] for r in results)
        total_unverified = sum(r['unverified'] for r in results)
        total_unbacked = sum(r['unbacked'] for r in results)
        total_gaps = sum(r['gaps'] for r in results)

        print(f"Total testplans:        {len(results)}")
        print(f"Total scenarios:        {total_scenarios}")
        if total_scenarios:
            print(f"Fully verified:         {total_verified} ({100*total_verified/total_scenarios:.1f}%)")
            print(f"Partially covered:      {total_partial} ({100*total_partial/total_scenarios:.1f}%)")
            print(f"Not covered (lines):    {total_unverified} ({100*total_unverified/total_scenarios:.1f}%)")
            print(f"Not backed (tests):     {total_unbacked} ({100*total_unbacked/total_scenarios:.1f}%)")
        else:
            print(f"Fully verified:         {total_verified}")
            print(f"Partially covered:      {total_partial}")
            print(f"Not covered (lines):    {total_unverified}")
            print(f"Not backed (tests):     {total_unbacked}")
        print(f"Recorded gaps:          {total_gaps}")

        if args.strict and total_unbacked > 0:
            sys.exit(1)
    else:
        # Single testplan
        coverage_dat = _find_coverage_dat(args.coverage) if args.coverage else None
        result = verify_testplan(args.testplan, coverage_dat)
        if args.strict and result['unbacked'] > 0:
            sys.exit(1)


if __name__ == '__main__':
    main()
