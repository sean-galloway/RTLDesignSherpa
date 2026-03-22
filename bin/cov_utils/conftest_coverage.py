# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: conftest_coverage
# Purpose: Shared coverage aggregation helpers for conftest.py files
#
# Author: sean galloway
# Created: 2025-03-20

"""
Shared Coverage Aggregation Helpers for conftest.py

Provides reusable functions that conftest.py files across the repository can
call instead of duplicating coverage collection and reporting logic. Every
conftest.py that performs coverage aggregation at session end duplicates the
same pattern; this module eliminates that duplication.

Design goals:
    - Standalone: only stdlib + logging, no third-party imports
    - Drop-in: conftest.py calls one or two functions, gets everything
    - Correct deduplication: protocol coverage uses MAX hits (not SUM) so
      the same coverage point hit by multiple tests is counted once
    - Verilator merge: delegates to ``verilator_coverage --write`` for
      correct line/toggle/branch deduplication

Typical conftest.py usage::

    from cov_utils.conftest_coverage import aggregate_all_coverage

    @pytest.hookimpl(trylast=True)
    def pytest_sessionfinish(session, exitstatus):
        if os.environ.get('COVERAGE', '0') == '1':
            aggregate_all_coverage(
                base_dir=os.path.dirname(os.path.abspath(__file__)),
                component_name='STREAM FUB',
            )

Or, for finer control::

    from cov_utils.conftest_coverage import (
        aggregate_verilator_coverage,
        aggregate_protocol_coverage,
        generate_conftest_report,
        get_coverage_compile_args,
    )
"""

import glob
import json
import logging
import os
import shutil
import subprocess
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Public helpers
# ---------------------------------------------------------------------------

def get_coverage_compile_args() -> List[str]:
    """Return Verilator compile flags for coverage when ``COVERAGE=1``.

    When the ``COVERAGE`` environment variable is set to ``'1'``, returns the
    standard set of Verilator flags that enable line, toggle, and underscore
    coverage collection.  Otherwise returns an empty list so callers can
    unconditionally extend their compile-arg lists.

    Returns:
        List of Verilator CLI flags, or empty list when coverage is disabled.

    Example::

        compile_args = ['-Wall', '-Wno-fatal']
        compile_args.extend(get_coverage_compile_args())
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []

    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]


# ---------------------------------------------------------------------------
# Verilator coverage aggregation
# ---------------------------------------------------------------------------

def aggregate_verilator_coverage(base_dir: str) -> Optional[str]:
    """Find, merge, and save Verilator ``coverage.dat`` files.

    Walks **all** subdirectories under ``<base_dir>/local_sim_build/`` to
    locate ``coverage.dat`` files (parameterised tests create deeply-nested
    build directories).  Merges them with ``verilator_coverage --write`` and
    saves both a timestamped file and a ``latest`` copy.

    Args:
        base_dir: Root directory that contains ``local_sim_build/``.
            Typically ``os.path.dirname(os.path.abspath(__file__))`` in a
            conftest.py.

    Returns:
        Absolute path to the merged ``.dat`` file, or ``None`` if no
        coverage files were found or the merge failed.
    """
    coverage_dir = os.path.join(base_dir, 'coverage_data')
    merged_dir = os.path.join(coverage_dir, 'merged')
    os.makedirs(merged_dir, exist_ok=True)

    # Discover coverage.dat files by walking the entire sim build tree.
    dat_files: List[str] = []
    sim_build_root = os.path.join(base_dir, 'local_sim_build')
    if os.path.isdir(sim_build_root):
        for root, _dirs, files in os.walk(sim_build_root):
            if 'coverage.dat' in files:
                dat_files.append(os.path.join(root, 'coverage.dat'))

    if not dat_files:
        log.info('No coverage.dat files found under %s', sim_build_root)
        return None

    log.info('Found %d coverage.dat files to merge', len(dat_files))

    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    merged_file = os.path.join(merged_dir, f'merged_coverage_{timestamp}.dat')
    latest_file = os.path.join(merged_dir, 'latest_merged_coverage.dat')

    try:
        cmd = ['verilator_coverage', '--write', merged_file] + dat_files
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        if result.returncode != 0:
            log.warning('verilator_coverage merge failed: %s', result.stderr)
            return None

        log.info('Verilator coverage merged: %s', merged_file)
        shutil.copy2(merged_file, latest_file)
        return merged_file

    except FileNotFoundError:
        log.warning(
            'verilator_coverage not found on PATH -- '
            'Verilator coverage aggregation skipped'
        )
    except subprocess.TimeoutExpired:
        log.warning('verilator_coverage merge timed out after 120 s')
    except Exception as exc:
        log.warning('Verilator coverage aggregation error: %s', exc)

    return None


# ---------------------------------------------------------------------------
# Protocol coverage aggregation
# ---------------------------------------------------------------------------

def aggregate_protocol_coverage(base_dir: str) -> Optional[Dict[str, Any]]:
    """Merge per-test protocol coverage JSON summaries using MAX hits.

    Searches ``<base_dir>/coverage_data/per_test/`` for ``*_summary.json``
    files produced by individual tests.  For each coverage point the
    **maximum** hit count across all tests is retained -- this is the correct
    deduplication strategy because a coverage point that was exercised by
    *any* test should be marked as covered regardless of how many tests
    exercised it, and summing would inflate counts beyond their goal.

    Args:
        base_dir: Root directory that contains ``coverage_data/per_test/``.

    Returns:
        Merged protocol coverage dictionary, or ``None`` if no summary
        files were found.  The dictionary has the shape::

            {
                'test_count': int,
                'tests': [{'name': str, 'protocol_pct': float, 'line_pct': float}, ...],
                'groups': {
                    '<group_name>': {
                        'covered': int,
                        'total': int,
                        'coverage_pct': float,
                        'points': {
                            '<point_name>': {'hits': int, 'goal': int},
                            ...
                        }
                    },
                    ...
                },
                'overall_protocol_pct': float,
                'overall_line_pct': float,
            }
    """
    coverage_dir = os.path.join(base_dir, 'coverage_data')
    per_test_dir = os.path.join(coverage_dir, 'per_test')
    merged_dir = os.path.join(coverage_dir, 'merged')
    os.makedirs(merged_dir, exist_ok=True)

    summary_files = sorted(glob.glob(os.path.join(per_test_dir, '*_summary.json')))
    if not summary_files:
        log.info('No protocol coverage summary files found in %s', per_test_dir)
        return None

    merged: Dict[str, Any] = {
        'test_count': 0,
        'tests': [],
        'groups': {},
        'overall_protocol_pct': 0.0,
        'overall_line_pct': 0.0,
    }

    total_protocol_pct = 0.0
    total_line_pct = 0.0

    for summary_file in summary_files:
        try:
            with open(summary_file, 'r') as fh:
                data = json.load(fh)
        except Exception as exc:
            log.warning('Failed to parse %s: %s', summary_file, exc)
            continue

        test_name = data.get('test_name', os.path.basename(summary_file))
        test_protocol_pct = data.get('overall', {}).get('protocol_pct', 0.0)
        test_line_pct = data.get('overall', {}).get('line_pct', 0.0)

        merged['tests'].append({
            'name': test_name,
            'protocol_pct': test_protocol_pct,
            'line_pct': test_line_pct,
        })

        total_protocol_pct += test_protocol_pct
        total_line_pct += test_line_pct
        merged['test_count'] += 1

        # Merge protocol group coverage points using MAX hits.
        protocol_data = data.get('protocol_coverage', {})
        for group_name, group_data in protocol_data.get('groups', {}).items():
            if group_name not in merged['groups']:
                merged['groups'][group_name] = {
                    'covered': 0,
                    'total': 0,
                    'coverage_pct': 0.0,
                    'points': {},
                }

            mg = merged['groups'][group_name]
            for point_name, point_data in group_data.get('points', {}).items():
                incoming_hits = point_data.get('hits', 0)
                incoming_goal = point_data.get('goal', 1)

                if point_name not in mg['points']:
                    mg['points'][point_name] = {
                        'hits': incoming_hits,
                        'goal': incoming_goal,
                    }
                else:
                    # MAX deduplication: retain the highest hit count seen
                    # across any single test.  This correctly represents
                    # whether the point was covered without inflating counts.
                    existing_hits = mg['points'][point_name]['hits']
                    mg['points'][point_name]['hits'] = max(existing_hits, incoming_hits)

    # Compute averaged overall percentages.
    if merged['test_count'] > 0:
        merged['overall_protocol_pct'] = total_protocol_pct / merged['test_count']
        merged['overall_line_pct'] = total_line_pct / merged['test_count']

    # Recompute per-group covered/total/pct from merged point data.
    for _group_name, group_data in merged['groups'].items():
        points = group_data.get('points', {})
        covered = sum(
            1 for p in points.values() if p['hits'] >= p.get('goal', 1)
        )
        total = len(points)
        group_data['covered'] = covered
        group_data['total'] = total
        group_data['coverage_pct'] = (covered / total * 100.0) if total > 0 else 0.0

    # Persist merged data.
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    merged_file = os.path.join(merged_dir, f'merged_coverage_{timestamp}.json')
    latest_file = os.path.join(merged_dir, 'latest_merged_coverage.json')

    try:
        with open(merged_file, 'w') as fh:
            json.dump(merged, fh, indent=2)
        with open(latest_file, 'w') as fh:
            json.dump(merged, fh, indent=2)
        log.info('Protocol coverage merged: %s', merged_file)
    except Exception as exc:
        log.warning('Failed to write merged protocol coverage: %s', exc)

    return merged


# ---------------------------------------------------------------------------
# Markdown report generation
# ---------------------------------------------------------------------------

# Default coverage targets (matching CoverageGoals in config_base.py).
_DEFAULT_TARGETS = {
    'line': 80.0,
    'branch': 75.0,
    'toggle': 70.0,
    'protocol': 80.0,
}


def generate_conftest_report(
    merged_protocol: Dict[str, Any],
    reports_dir: str,
    component_name: str,
    timestamp: str,
    *,
    targets: Optional[Dict[str, float]] = None,
) -> str:
    """Generate a Markdown coverage report from merged protocol data.

    The report includes:
    - Executive summary with PASS/FAIL against configurable targets
    - Per-group breakdown (covered / total / percentage)
    - Per-group line/branch/toggle breakdown when the data includes those
      keys (future-proofing)
    - Per-test results table
    - Coverage gaps listing uncovered points

    Args:
        merged_protocol: Merged data dictionary as returned by
            :func:`aggregate_protocol_coverage`.
        reports_dir: Directory to write the report files into.
        component_name: Human-readable component name used in the report
            title (e.g. ``'STREAM FUB'``, ``'RAPIDS Macro'``).
        timestamp: Timestamp string (``'%Y%m%d_%H%M%S'``) for the filename.
        targets: Optional dict overriding default coverage targets.  Keys
            are ``'line'``, ``'branch'``, ``'toggle'``, ``'protocol'``.

    Returns:
        Absolute path to the generated report file.
    """
    os.makedirs(reports_dir, exist_ok=True)
    tgt = {**_DEFAULT_TARGETS, **(targets or {})}

    def _status(pct: float, target: float) -> str:
        if pct >= target:
            return 'PASS'
        if pct >= target * 0.8:
            return 'WARN'
        return 'FAIL'

    lines: List[str] = []

    # -- Header ---------------------------------------------------------------
    lines.append(f'# {component_name} Coverage Report')
    lines.append('')
    lines.append(f'**Generated:** {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}')
    lines.append(f'**Tests Run:** {merged_protocol.get("test_count", 0)}')
    lines.append('')

    # -- Summary --------------------------------------------------------------
    lines.append('## Summary')
    lines.append('')
    lines.append('| Metric | Coverage | Target | Status |')
    lines.append('|--------|----------|--------|--------|')

    protocol_pct = merged_protocol.get('overall_protocol_pct', 0.0)
    line_pct = merged_protocol.get('overall_line_pct', 0.0)

    lines.append(
        f'| Protocol Coverage | {protocol_pct:.1f}% '
        f'| {tgt["protocol"]:.0f}% '
        f'| {_status(protocol_pct, tgt["protocol"])} |'
    )
    lines.append(
        f'| Line Coverage | {line_pct:.1f}% '
        f'| {tgt["line"]:.0f}% '
        f'| {_status(line_pct, tgt["line"])} |'
    )

    # If branch/toggle data is present at the top level, include it.
    for metric_key, metric_label in [('branch', 'Branch Coverage'),
                                     ('toggle', 'Toggle Coverage')]:
        metric_pct = merged_protocol.get(f'overall_{metric_key}_pct')
        if metric_pct is not None:
            lines.append(
                f'| {metric_label} | {metric_pct:.1f}% '
                f'| {tgt[metric_key]:.0f}% '
                f'| {_status(metric_pct, tgt[metric_key])} |'
            )

    lines.append('')

    # -- Protocol coverage by group -------------------------------------------
    groups = merged_protocol.get('groups', {})
    if groups:
        lines.append('## Protocol Coverage by Group')
        lines.append('')
        lines.append('| Group | Covered | Total | Percentage |')
        lines.append('|-------|---------|-------|------------|')

        for group_name in sorted(groups):
            gd = groups[group_name]
            covered = gd.get('covered', 0)
            total = gd.get('total', 0)
            pct = gd.get('coverage_pct', 0.0)
            lines.append(f'| {group_name} | {covered} | {total} | {pct:.1f}% |')

            # Include per-group line/branch/toggle if available.
            for sub_metric in ('line', 'branch', 'toggle'):
                sub_data = gd.get(sub_metric)
                if isinstance(sub_data, dict) and 'pct' in sub_data:
                    sub_covered = sub_data.get('covered', 0)
                    sub_total = sub_data.get('total', 0)
                    sub_pct = sub_data['pct']
                    lines.append(
                        f'|   {sub_metric} | {sub_covered} '
                        f'| {sub_total} | {sub_pct:.1f}% |'
                    )

        lines.append('')

    # -- Per-test results -----------------------------------------------------
    tests = merged_protocol.get('tests', [])
    if tests:
        lines.append('## Per-Test Results')
        lines.append('')
        lines.append('| Test Name | Protocol | Line |')
        lines.append('|-----------|----------|------|')

        for test in sorted(tests, key=lambda t: t.get('name', '')):
            name = test.get('name', 'unknown')
            # Truncate long test names for readability.
            if len(name) > 70:
                name = name[:67] + '...'
            t_prot = test.get('protocol_pct', 0.0)
            t_line = test.get('line_pct', 0.0)
            lines.append(f'| {name} | {t_prot:.1f}% | {t_line:.1f}% |')

        lines.append('')

    # -- Coverage gaps --------------------------------------------------------
    uncovered: List[str] = []
    for group_name in sorted(groups):
        gd = groups[group_name]
        for point_name, point_data in sorted(gd.get('points', {}).items()):
            if point_data.get('hits', 0) < point_data.get('goal', 1):
                uncovered.append(
                    f'- **{group_name}**: {point_name} '
                    f'({point_data.get("hits", 0)} hits)'
                )

    lines.append('## Coverage Gaps')
    lines.append('')
    if uncovered:
        lines.append('The following coverage points were NOT hit:')
        lines.append('')
        lines.extend(uncovered[:50])
        if len(uncovered) > 50:
            lines.append(f'... and {len(uncovered) - 50} more')
    else:
        lines.append('All coverage points were hit!')

    lines.append('')
    lines.append('---')
    lines.append(f'*Report generated by {component_name} coverage infrastructure*')

    # -- Write files ----------------------------------------------------------
    report_content = '\n'.join(lines)

    report_file = os.path.join(reports_dir, f'coverage_report_{timestamp}.md')
    latest_file = os.path.join(reports_dir, 'latest_coverage_report.md')

    try:
        with open(report_file, 'w') as fh:
            fh.write(report_content)
        with open(latest_file, 'w') as fh:
            fh.write(report_content)
        log.info('Coverage report written: %s', report_file)
    except Exception as exc:
        log.warning('Failed to write coverage report: %s', exc)

    return report_file


# ---------------------------------------------------------------------------
# Convenience: aggregate everything in one call
# ---------------------------------------------------------------------------

def aggregate_all_coverage(
    base_dir: str,
    component_name: str,
    *,
    targets: Optional[Dict[str, float]] = None,
) -> Tuple[Optional[str], Optional[Dict[str, Any]], Optional[str]]:
    """Run all coverage aggregation steps and generate a report.

    This is the single entry-point that most conftest.py files should call.
    It chains :func:`aggregate_verilator_coverage`,
    :func:`aggregate_protocol_coverage`, and :func:`generate_conftest_report`.

    Args:
        base_dir: Root directory for the test area (the directory that
            contains ``local_sim_build/`` and ``coverage_data/``).
        component_name: Human-readable name for the report title.
        targets: Optional dict of coverage targets (see
            :func:`generate_conftest_report`).

    Returns:
        A 3-tuple of ``(verilator_merged_path, protocol_merged_dict,
        report_path)``.  Any element may be ``None`` if the corresponding
        step found no data or failed.

    Example::

        verilator_dat, protocol_data, report_path = aggregate_all_coverage(
            base_dir=os.path.dirname(os.path.abspath(__file__)),
            component_name='RAPIDS FUB-Beats',
        )
        if protocol_data:
            logging.info(
                'Protocol coverage: %.1f%%',
                protocol_data['overall_protocol_pct'],
            )
    """
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')

    # Step 1: Verilator line/toggle/branch coverage.
    verilator_merged = aggregate_verilator_coverage(base_dir)

    # Step 2: Protocol coverage JSON summaries.
    protocol_merged = aggregate_protocol_coverage(base_dir)

    # Step 3: Markdown report (only if protocol data exists).
    report_path: Optional[str] = None
    if protocol_merged is not None:
        reports_dir = os.path.join(base_dir, 'coverage_data', 'reports')
        report_path = generate_conftest_report(
            merged_protocol=protocol_merged,
            reports_dir=reports_dir,
            component_name=component_name,
            timestamp=timestamp,
            targets=targets,
        )

        log.info(
            'Coverage aggregated: %d tests',
            protocol_merged.get('test_count', 0),
        )
        log.info(
            '  Overall Protocol: %.1f%%',
            protocol_merged.get('overall_protocol_pct', 0.0),
        )
        log.info(
            '  Overall Line:     %.1f%%',
            protocol_merged.get('overall_line_pct', 0.0),
        )
        if report_path:
            log.info('  Report: %s', report_path)

    return verilator_merged, protocol_merged, report_path
