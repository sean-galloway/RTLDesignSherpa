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


def parse_testplan(yaml_path):
    """Parse a YAML testplan and extract scenario-to-line mappings."""
    with open(yaml_path, 'r') as f:
        testplan = yaml.safe_load(f)

    result = {
        'module': testplan.get('module', 'unknown'),
        'rtl_file': testplan.get('rtl_file', ''),
        'test_file': testplan.get('test_file', ''),
        'scenarios': []
    }

    for scenario in testplan.get('functional_scenarios', []):
        result['scenarios'].append({
            'id': scenario.get('id', ''),
            'name': scenario.get('name', ''),
            'covers_lines': scenario.get('covers_lines', []),
            'status': scenario.get('status', 'unknown')
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
                    for line in f:
                        # Match lines with coverage count > 0
                        # Format: " 000123  <code>" (covered) or "%000000  <code>" (not covered)
                        match = re.match(r'^([% ])(\d{6})\s', line)
                        if match:
                            prefix = match.group(1)
                            count = int(match.group(2))
                            # Get line number from position in file
                            # This is approximate - verilator annotation includes line numbers
                            if prefix == ' ' or count > 0:
                                # Extract actual line number if present
                                line_match = re.search(r'//.*line\s+(\d+)', line)
                                if line_match:
                                    covered_lines.add(int(line_match.group(1)))
                break

    return covered_lines


def verify_testplan(testplan_path, coverage_dat):
    """Verify a testplan against coverage data."""
    testplan = parse_testplan(testplan_path)

    # Get RTL filename from path
    rtl_file = testplan['rtl_file']
    rtl_filename = os.path.basename(rtl_file) if rtl_file else ''

    print(f"\n{'='*70}")
    print(f"Module: {testplan['module']}")
    print(f"RTL: {rtl_file}")
    print(f"Test: {testplan['test_file']}")
    print(f"{'='*70}")

    # Get covered lines from coverage data
    covered_lines = get_covered_lines(coverage_dat, rtl_filename)

    total_scenarios = len(testplan['scenarios'])
    verified_scenarios = 0
    partial_scenarios = 0
    unverified_scenarios = 0

    for scenario in testplan['scenarios']:
        scenario_lines = set(scenario['covers_lines'])
        if not scenario_lines:
            continue

        # Check how many lines are covered
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

        print(f"  {scenario['id']:12} {scenario['name']:30} {status:12} ({covered_count}/{total_count} lines)")

    print(f"\nSummary:")
    print(f"  Total scenarios:      {total_scenarios}")
    print(f"  Fully verified:       {verified_scenarios}")
    print(f"  Partially covered:    {partial_scenarios}")
    print(f"  Not covered:          {unverified_scenarios}")

    return {
        'module': testplan['module'],
        'total': total_scenarios,
        'verified': verified_scenarios,
        'partial': partial_scenarios,
        'unverified': unverified_scenarios
    }


def main():
    parser = argparse.ArgumentParser(
        description='Verify testplan scenario coverage against Verilator data',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s val/amba/testplans/apb_slave_testplan.yaml coverage.dat
  %(prog)s --all val/amba/testplans/ val/amba/coverage_data/merged/
        """
    )
    parser.add_argument('testplan', help='Path to testplan YAML or directory')
    parser.add_argument('coverage', help='Path to coverage.dat file or directory')
    parser.add_argument('--all', '-a', action='store_true',
                        help='Process all testplans in directory')
    parser.add_argument('--summary', '-s', action='store_true',
                        help='Show only summary')
    args = parser.parse_args()

    if args.all:
        # Process all testplans in directory
        testplan_dir = Path(args.testplan)
        coverage_path = args.coverage

        # Find coverage file
        if os.path.isdir(coverage_path):
            # Look for merged coverage or latest .dat
            merged = Path(coverage_path) / 'latest_merged_coverage.dat'
            if merged.exists():
                coverage_dat = str(merged)
            else:
                dat_files = list(Path(coverage_path).glob('*.dat'))
                if dat_files:
                    coverage_dat = str(max(dat_files, key=os.path.getmtime))
                else:
                    print(f"No coverage.dat files found in {coverage_path}", file=sys.stderr)
                    sys.exit(1)
        else:
            coverage_dat = coverage_path

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

        print(f"Total testplans:        {len(results)}")
        print(f"Total scenarios:        {total_scenarios}")
        print(f"Fully verified:         {total_verified} ({100*total_verified/total_scenarios:.1f}%)")
        print(f"Partially covered:      {total_partial} ({100*total_partial/total_scenarios:.1f}%)")
        print(f"Not covered:            {total_unverified} ({100*total_unverified/total_scenarios:.1f}%)")
    else:
        # Single testplan
        verify_testplan(args.testplan, args.coverage)


if __name__ == '__main__':
    main()
