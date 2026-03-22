#!/usr/bin/env python3
"""
Functional Coverage Tracker

Tracks functional test scenarios and computes implied line coverage
based on scenario-to-line mappings defined in testplan YAML files.

This addresses Verilator's limitation with combinational logic coverage
by allowing us to declare "if this test scenario passes, these lines
are considered covered."

Usage:
    python functional_coverage_tracker.py --testplan <testplan.yaml>
    python functional_coverage_tracker.py --testplans-dir <dir> --report
"""

import os
import re
import sys
import argparse
import yaml
import glob
import xml.etree.ElementTree as ET
from pathlib import Path
from datetime import datetime


# Cache parsed JUnit XML results per directory to avoid re-parsing
_junit_cache = {}


def load_testplan(filepath):
    """Load a testplan YAML file."""
    with open(filepath, 'r') as f:
        return yaml.safe_load(f)


def _parse_junit_xml(xml_path):
    """
    Parse a JUnit XML file and return a dict mapping test_name -> status.

    Handles both pytest-style and standard JUnit XML formats.
    Status values: 'passed', 'failed', 'skipped', 'error'

    JUnit XML structure:
      <testsuites>
        <testsuite>
          <testcase name="test_name" classname="...">
            <!-- no children = passed -->
            <failure .../>    <!-- failed -->
            <skipped .../>    <!-- skipped -->
            <error .../>      <!-- error -->
          </testcase>
        </testsuite>
      </testsuites>
    """
    results = {}
    try:
        tree = ET.parse(xml_path)
        root = tree.getroot()

        # Handle both <testsuites> wrapper and direct <testsuite>
        if root.tag == 'testsuites':
            testsuites = root.findall('testsuite')
        elif root.tag == 'testsuite':
            testsuites = [root]
        else:
            return results

        for testsuite in testsuites:
            for testcase in testsuite.findall('testcase'):
                name = testcase.get('name', '')
                classname = testcase.get('classname', '')

                # Determine status from child elements
                if testcase.find('failure') is not None:
                    status = 'failed'
                elif testcase.find('error') is not None:
                    status = 'error'
                elif testcase.find('skipped') is not None:
                    status = 'skipped'
                else:
                    status = 'passed'

                # Store by test name (bare name)
                results[name] = status

                # Also store by classname.name for more specific matching
                if classname:
                    results[f"{classname}.{name}"] = status

    except (ET.ParseError, OSError) as e:
        print(f"Warning: Failed to parse {xml_path}: {e}", file=sys.stderr)

    return results


def _get_junit_results(test_results_dir):
    """
    Get cached JUnit XML results for a directory.

    Parses all *.xml files in the directory on first call, then
    returns cached results on subsequent calls for the same directory.
    """
    test_results_dir = os.path.abspath(test_results_dir)
    if test_results_dir in _junit_cache:
        return _junit_cache[test_results_dir]

    combined = {}
    xml_files = glob.glob(os.path.join(test_results_dir, '*.xml'))
    for xml_path in xml_files:
        parsed = _parse_junit_xml(xml_path)
        combined.update(parsed)

    _junit_cache[test_results_dir] = combined
    return combined


def check_scenario_status(scenario, test_results_dir=None):
    """
    Check if a scenario's test function has been executed.

    Returns: 'verified', 'partial', 'not_tested', or 'not_applicable'
    """
    status = scenario.get('status', 'not_tested')

    # If manually marked, use that
    if status in ['verified', 'not_applicable']:
        return status

    # Auto-check from pytest JUnit XML results
    if test_results_dir and os.path.isdir(test_results_dir):
        test_function = scenario.get('test_function')
        test_module = scenario.get('test_module')

        if test_function or test_module:
            results = _get_junit_results(test_results_dir)

            if test_function:
                # Try exact match on test function name
                xml_status = results.get(test_function)

                # If no exact match, search for partial match
                # (handles pytest parametrized names like "test_foo[param1-param2]")
                if xml_status is None:
                    for result_name, result_status in results.items():
                        if result_name == test_function or result_name.startswith(test_function + '['):
                            xml_status = result_status
                            break

            elif test_module:
                # Match any test in the module (classname contains test_module)
                xml_status = None
                for result_name, result_status in results.items():
                    if test_module in result_name:
                        # If any test in the module failed, consider it not covered
                        if result_status in ('failed', 'error'):
                            xml_status = 'failed'
                            break
                        elif result_status == 'passed':
                            xml_status = 'passed'

            if xml_status == 'passed':
                return 'verified'
            elif xml_status in ('failed', 'error'):
                return 'not_tested'
            # If not found in XML, fall through to manual status

    return status


def compute_implied_coverage(testplan, test_results_dir=None):
    """
    Compute implied coverage based on scenario statuses.

    Returns dict with:
    - total_points: Total coverage points
    - verilator_covered: Points covered per Verilator
    - scenario_covered: Points covered by scenarios
    - implied_covered: Union of both
    - implied_percentage: Implied coverage percentage
    - scenario_status: Dict of scenario_id -> status
    """
    coverage_points = testplan.get('coverage_points', [])
    scenarios = testplan.get('functional_scenarios', [])

    # Track which lines are covered by each method
    verilator_covered_lines = set()
    scenario_covered_lines = set()

    # Get Verilator coverage
    for pt in coverage_points:
        if pt.get('covered', False):
            verilator_covered_lines.add(pt['line'])

    # Get scenario coverage
    scenario_status = {}
    for scenario in scenarios:
        sid = scenario.get('id', 'unknown')
        status = check_scenario_status(scenario, test_results_dir)
        scenario_status[sid] = status

        if status in ['verified', 'partial']:
            covers_lines = scenario.get('covers_lines', [])
            for line in covers_lines:
                scenario_covered_lines.add(line)

    # Compute implied coverage (union)
    implied_covered_lines = verilator_covered_lines | scenario_covered_lines

    total_points = len(coverage_points)
    verilator_count = len(verilator_covered_lines)
    scenario_count = len(scenario_covered_lines)
    implied_count = len(implied_covered_lines)

    return {
        'total_points': total_points,
        'verilator_covered': verilator_count,
        'scenario_covered': scenario_count,
        'implied_covered': implied_count,
        'verilator_percentage': (verilator_count / total_points * 100) if total_points else 0,
        'scenario_percentage': (scenario_count / total_points * 100) if total_points else 0,
        'implied_percentage': (implied_count / total_points * 100) if total_points else 0,
        'scenario_status': scenario_status,
        'uncovered_lines': [pt['line'] for pt in coverage_points
                           if pt['line'] not in implied_covered_lines]
    }


def generate_report(testplans, output_format='text', test_results_dir=None):
    """Generate coverage report for multiple testplans."""
    results = []

    for tp_path in testplans:
        try:
            testplan = load_testplan(tp_path)
            module = testplan.get('module', Path(tp_path).stem)
            coverage = compute_implied_coverage(testplan, test_results_dir)
            results.append({
                'module': module,
                'testplan': tp_path,
                **coverage
            })
        except Exception as e:
            print(f"Error processing {tp_path}: {e}", file=sys.stderr)

    # Sort by implied coverage
    results.sort(key=lambda x: x['implied_percentage'])

    if output_format == 'text':
        return format_text_report(results)
    elif output_format == 'markdown':
        return format_markdown_report(results)
    elif output_format == 'csv':
        return format_csv_report(results)
    else:
        return results


def format_text_report(results):
    """Format results as text report."""
    lines = [
        "=" * 80,
        "FUNCTIONAL COVERAGE REPORT",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 80,
        "",
        f"{'Module':<35} {'Verilator':>10} {'Scenario':>10} {'Implied':>10}",
        "-" * 80,
    ]

    below_95 = []
    above_95 = []

    for r in results:
        line = f"{r['module']:<35} {r['verilator_percentage']:>9.1f}% {r['scenario_percentage']:>9.1f}% {r['implied_percentage']:>9.1f}%"
        if r['implied_percentage'] < 95:
            below_95.append((r, line))
        else:
            above_95.append((r, line))

    lines.append("")
    lines.append(f"MODULES BELOW 95% ({len(below_95)}):")
    lines.append("-" * 80)
    for r, line in below_95:
        lines.append(line)
        if r['uncovered_lines']:
            lines.append(f"    Uncovered lines: {r['uncovered_lines'][:10]}{'...' if len(r['uncovered_lines']) > 10 else ''}")

    lines.append("")
    lines.append(f"MODULES AT OR ABOVE 95% ({len(above_95)}):")
    lines.append("-" * 80)
    for r, line in above_95:
        lines.append(line)

    lines.append("")
    lines.append("=" * 80)
    lines.append(f"SUMMARY: {len(above_95)}/{len(results)} modules at or above 95% implied coverage")
    lines.append("=" * 80)

    return '\n'.join(lines)


def format_markdown_report(results):
    """Format results as markdown."""
    lines = [
        "# Functional Coverage Report",
        "",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        "## Coverage Summary",
        "",
        "| Module | Verilator | Scenario | Implied |",
        "|--------|-----------|----------|---------|",
    ]

    for r in results:
        status = "good" if r['implied_percentage'] >= 95 else "warn" if r['implied_percentage'] >= 80 else "bad"
        lines.append(f"| {r['module']} | {r['verilator_percentage']:.1f}% | {r['scenario_percentage']:.1f}% | {r['implied_percentage']:.1f}% |")

    above_95 = sum(1 for r in results if r['implied_percentage'] >= 95)
    lines.extend([
        "",
        f"**Summary:** {above_95}/{len(results)} modules at or above 95% implied coverage",
    ])

    return '\n'.join(lines)


def format_csv_report(results):
    """Format results as CSV."""
    lines = ["module,verilator_pct,scenario_pct,implied_pct,uncovered_count"]
    for r in results:
        lines.append(f"{r['module']},{r['verilator_percentage']:.1f},{r['scenario_percentage']:.1f},{r['implied_percentage']:.1f},{len(r['uncovered_lines'])}")
    return '\n'.join(lines)


def update_testplan_with_coverage(testplan_path, coverage_dat_path=None):
    """
    Update a testplan's coverage_points section with fresh Verilator data.
    """
    # TODO: Implement this to auto-update testplans after test runs
    pass


def main():
    parser = argparse.ArgumentParser(description='Functional Coverage Tracker')
    parser.add_argument('--testplan', help='Single testplan YAML file')
    parser.add_argument('--testplans-dir', help='Directory containing testplan YAML files')
    parser.add_argument('--report', action='store_true', help='Generate coverage report')
    parser.add_argument('--format', choices=['text', 'markdown', 'csv'], default='text',
                       help='Report format (default: text)')
    parser.add_argument('--output', '-o', help='Output file (default: stdout)')
    parser.add_argument('--results-dir', help='Directory with pytest results XML files')
    args = parser.parse_args()

    testplans = []

    if args.testplan:
        testplans.append(args.testplan)
    elif args.testplans_dir:
        testplans = glob.glob(os.path.join(args.testplans_dir, '*.yaml'))
        testplans += glob.glob(os.path.join(args.testplans_dir, '*.yml'))

    if not testplans:
        print("No testplans specified. Use --testplan or --testplans-dir", file=sys.stderr)
        sys.exit(1)

    if args.report:
        report = generate_report(testplans, args.format, args.results_dir)
        if args.output:
            with open(args.output, 'w') as f:
                f.write(report)
            print(f"Report written to {args.output}")
        else:
            print(report)
    else:
        # Single testplan analysis
        for tp_path in testplans:
            testplan = load_testplan(tp_path)
            module = testplan.get('module', Path(tp_path).stem)
            coverage = compute_implied_coverage(testplan, args.results_dir)

            print(f"Module: {module}")
            print(f"  Verilator coverage: {coverage['verilator_covered']}/{coverage['total_points']} ({coverage['verilator_percentage']:.1f}%)")
            print(f"  Scenario coverage:  {coverage['scenario_covered']}/{coverage['total_points']} ({coverage['scenario_percentage']:.1f}%)")
            print(f"  Implied coverage:   {coverage['implied_covered']}/{coverage['total_points']} ({coverage['implied_percentage']:.1f}%)")
            print(f"  Scenarios: {coverage['scenario_status']}")
            if coverage['uncovered_lines']:
                print(f"  Uncovered lines: {coverage['uncovered_lines'][:20]}{'...' if len(coverage['uncovered_lines']) > 20 else ''}")
            print()


if __name__ == '__main__':
    main()
