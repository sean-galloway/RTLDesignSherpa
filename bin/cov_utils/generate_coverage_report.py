#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: generate_coverage_report
# Purpose: GENERIC coverage report generator for any component
#
# Documentation: /GLOBAL_REQUIREMENTS.md
#
# Author: sean galloway
# Created: 2025-01-17

"""
Generic Coverage Report Generator

This script generates comprehensive coverage reports for any RTL Design Sherpa
component. It aggregates coverage data from all tests and generates:
1. Per-test coverage summaries
2. Merged coverage report (JSON)
3. Human-readable coverage report (Markdown)
4. HTML coverage report (optional)
5. Legal coverage analysis (optional, if component has legal config)

Usage:
    # Auto-detect component from current directory
    python bin/cov_utils/generate_coverage_report.py

    # Specify component explicitly
    python bin/cov_utils/generate_coverage_report.py --component stream
    python bin/cov_utils/generate_coverage_report.py --component rapids

    # Specify custom coverage directory
    python bin/cov_utils/generate_coverage_report.py -c /path/to/tests

    # Generate HTML report
    python bin/cov_utils/generate_coverage_report.py --html

    # Show detailed per-point coverage
    python bin/cov_utils/generate_coverage_report.py --detailed

    # Include legal coverage analysis
    python bin/cov_utils/generate_coverage_report.py --legal

The script will:
1. Search for coverage.dat files in local_sim_build/ directories
2. Merge coverage using verilator_coverage tool
3. Generate reports in the component's coverage_data/reports/ directory
"""

import os
import sys
import json
import glob
import argparse
import subprocess
import tempfile
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


def get_repo_root() -> str:
    """Get repository root directory."""
    # Try git-based detection
    try:
        result = subprocess.run(
            ['git', 'rev-parse', '--show-toplevel'],
            capture_output=True, text=True, timeout=5
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass

    # Fallback: look for known marker files
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / 'CLAUDE.md').exists() and (current / 'bin').exists():
            return str(current)
        current = current.parent

    return str(Path(__file__).resolve().parent.parent.parent)


def detect_component() -> Optional[str]:
    """Detect component name from current directory."""
    cwd = Path.cwd()

    # Check if we're in a component directory structure
    # Expected: projects/components/{component}/...
    for parent in [cwd] + list(cwd.parents):
        if parent.parent.name == 'components' and parent.parent.parent.name == 'projects':
            return parent.name

    return None


def get_component_paths(component: str, repo_root: str) -> Dict[str, str]:
    """Get standard paths for a component.

    Args:
        component: Component name (e.g., 'stream', 'rapids')
        repo_root: Repository root directory

    Returns:
        Dict with paths: base_dir, tests_dir, coverage_dir, reports_dir
    """
    base_dir = os.path.join(repo_root, 'projects', 'components', component)

    # Handle different test directory structures
    # RAPIDS beats: dv/tests/fub_beats, dv/tests/macro_beats
    # STREAM: dv/tests/fub, dv/tests/macro, dv/tests/top
    tests_dir = os.path.join(base_dir, 'dv', 'tests')

    coverage_dir = os.path.join(tests_dir, 'coverage_data')
    reports_dir = os.path.join(coverage_dir, 'reports')

    return {
        'base_dir': base_dir,
        'tests_dir': tests_dir,
        'coverage_dir': coverage_dir,
        'reports_dir': reports_dir,
    }


def find_coverage_files(tests_dir: str) -> Dict[str, List[str]]:
    """Find all coverage files in the tests directory tree.

    Searches for coverage.dat files in:
    - */local_sim_build/test_*/coverage.dat
    - coverage_data/per_test/*.dat

    Args:
        tests_dir: Base tests directory

    Returns:
        Dict with categorized file lists
    """
    files = {
        'summaries': [],        # JSON summary files
        'protocols': [],        # Protocol coverage JSON
        'verilator': [],        # coverage.dat files in coverage_data
        'sim_build_coverage': [],  # coverage.dat files in sim_build dirs
    }

    # Search for local_sim_build directories at all levels
    for sim_build in Path(tests_dir).rglob('local_sim_build'):
        for test_dir in sim_build.glob('test_*'):
            coverage_dat = test_dir / 'coverage.dat'
            if coverage_dat.exists():
                files['sim_build_coverage'].append(str(coverage_dat))

    # Check for coverage_data/per_test directory
    per_test_dir = os.path.join(tests_dir, 'coverage_data', 'per_test')
    if os.path.exists(per_test_dir):
        files['summaries'] = glob.glob(os.path.join(per_test_dir, '*_summary.json'))
        files['protocols'] = glob.glob(os.path.join(per_test_dir, '*_protocol.json'))
        files['verilator'] = [f for f in glob.glob(os.path.join(per_test_dir, '*.dat'))
                              if 'verFiles' not in f]

    return files


def load_json_file(filepath: str) -> Optional[Dict]:
    """Load a JSON file, returning None on error."""
    try:
        with open(filepath, 'r') as f:
            return json.load(f)
    except Exception as e:
        print(f"Warning: Failed to load {filepath}: {e}")
        return None


def get_merged_verilator_coverage(coverage_files: List[str]) -> Tuple[float, int, int]:
    """Use verilator_coverage to properly merge coverage and get accurate line coverage.

    Verilator's coverage merging correctly handles overlapping lines across tests.

    Args:
        coverage_files: List of paths to coverage.dat files

    Returns:
        Tuple of (coverage_percent, lines_covered, lines_total)
    """
    if not coverage_files:
        return (0.0, 0, 0)

    # Filter to only coverage.dat files (not verFiles.dat)
    dat_files = [f for f in coverage_files if 'verFiles.dat' not in f and f.endswith('.dat')]

    if not dat_files:
        return (0.0, 0, 0)

    try:
        # Create temp file for merged output
        with tempfile.NamedTemporaryFile(suffix='.dat', delete=False) as tmp:
            merged_dat = tmp.name

        # Run verilator_coverage to merge all files
        cmd = ['verilator_coverage', '--write', merged_dat] + dat_files
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)

        if result.returncode != 0:
            print(f"Warning: verilator_coverage merge failed: {result.stderr}")
            return (0.0, 0, 0)

        # Create temp dir for annotation
        with tempfile.TemporaryDirectory() as annotate_dir:
            # Run verilator_coverage --annotate to get coverage percentage
            cmd = ['verilator_coverage', '--annotate', annotate_dir, merged_dat]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)

            # Parse output for coverage percentage
            # Format: "Total coverage (131/229) 57.00%"
            for line in result.stdout.split('\n'):
                if 'Total coverage' in line:
                    match = re.search(r'\((\d+)/(\d+)\)\s+([\d.]+)%', line)
                    if match:
                        covered = int(match.group(1))
                        total = int(match.group(2))
                        pct = float(match.group(3))
                        return (pct, covered, total)

        # Cleanup
        os.unlink(merged_dat)

    except Exception as e:
        print(f"Warning: Failed to get merged coverage: {e}")

    return (0.0, 0, 0)


def parse_verilator_coverage(coverage_files: List[str]) -> Dict[str, Dict]:
    """Parse Verilator coverage.dat files and return per-test coverage stats.

    Args:
        coverage_files: List of paths to coverage.dat files

    Returns:
        Dict mapping test_name -> {line: {covered, total}, toggle: {...}, branch: {...}}
    """
    result = {}

    for filepath in coverage_files:
        # Skip non-coverage files
        if 'verFiles.dat' in filepath:
            continue

        # Extract test name from path
        test_dir = os.path.dirname(filepath)
        test_name = os.path.basename(test_dir)

        stats = {
            'line': {'covered': 0, 'total': 0},
            'toggle': {'covered': 0, 'total': 0},
            'branch': {'covered': 0, 'total': 0},
        }

        try:
            with open(filepath, 'r') as f:
                for line in f:
                    if line.startswith('#') or not line.strip():
                        continue

                    if line.startswith('C '):
                        parts = line.rsplit(' ', 1)
                        if len(parts) != 2:
                            continue

                        try:
                            count = int(parts[1].strip())
                        except ValueError:
                            continue

                        metadata = parts[0]

                        if 'v_toggle' in metadata or 'pagev_toggle' in metadata:
                            stats['toggle']['total'] += 1
                            if count > 0:
                                stats['toggle']['covered'] += 1
                        elif 'v_line' in metadata or 'pagev_line' in metadata:
                            stats['line']['total'] += 1
                            if count > 0:
                                stats['line']['covered'] += 1
                        elif 'v_branch' in metadata or 'pagev_branch' in metadata:
                            stats['branch']['total'] += 1
                            if count > 0:
                                stats['branch']['covered'] += 1

            result[test_name] = stats

        except Exception as e:
            print(f"Warning: Failed to parse coverage file {filepath}: {e}")

    return result


def merge_coverage_data(coverage_files: Dict[str, List[str]]) -> Dict[str, Any]:
    """Merge coverage data from multiple tests.

    Args:
        coverage_files: Dict of file lists from find_coverage_files()

    Returns:
        Merged coverage data dictionary
    """
    merged = {
        'timestamp': datetime.now().isoformat(),
        'test_count': 0,
        'tests': [],
        'protocol_groups': {},
        'code_coverage': {
            'line': {'covered': 0, 'total': 0},
            'toggle': {'covered': 0, 'total': 0},
            'branch': {'covered': 0, 'total': 0},
        },
        'overall': {
            'protocol_pct': 0.0,
            'line_pct': 0.0,
            'toggle_pct': 0.0,
        }
    }

    # Parse Verilator coverage.dat files from sim_build directories
    sim_build_coverage = parse_verilator_coverage(coverage_files.get('sim_build_coverage', []))

    total_protocol = 0.0
    total_line = 0.0
    total_toggle = 0.0

    # Process each summary file
    for summary_file in coverage_files.get('summaries', []):
        data = load_json_file(summary_file)
        if not data:
            continue

        test_name = data.get('test_name', os.path.basename(summary_file).replace('_summary.json', ''))

        # Get line coverage from sim_build coverage.dat (overrides summary if available)
        line_pct = data.get('overall', {}).get('line_pct', 0)
        toggle_pct = data.get('overall', {}).get('toggle_pct', 0)

        if test_name in sim_build_coverage:
            sim_stats = sim_build_coverage[test_name]
            if sim_stats['line']['total'] > 0:
                line_pct = sim_stats['line']['covered'] / sim_stats['line']['total'] * 100
            if sim_stats['toggle']['total'] > 0:
                toggle_pct = sim_stats['toggle']['covered'] / sim_stats['toggle']['total'] * 100

        # Extract test-level stats
        test_info = {
            'name': test_name,
            'protocol_pct': data.get('overall', {}).get('protocol_pct', 0),
            'line_pct': line_pct,
            'toggle_pct': toggle_pct,
        }
        merged['tests'].append(test_info)
        merged['test_count'] += 1

        total_protocol += test_info['protocol_pct']
        total_line += test_info['line_pct']
        total_toggle += test_info['toggle_pct']

        # Merge protocol coverage groups
        protocol_data = data.get('protocol_coverage', {})
        for group_name, group_data in protocol_data.get('groups', {}).items():
            if group_name not in merged['protocol_groups']:
                merged['protocol_groups'][group_name] = {
                    'description': group_data.get('description', ''),
                    'points': {},
                }

            mg = merged['protocol_groups'][group_name]
            for point_name, point_data in group_data.get('points', {}).items():
                if point_name not in mg['points']:
                    mg['points'][point_name] = {
                        'name': point_data.get('name', point_name),
                        'description': point_data.get('description', ''),
                        'hits': 0,
                        'goal': point_data.get('goal', 1),
                    }
                mg['points'][point_name]['hits'] += point_data.get('hits', 0)

        # Aggregate code coverage from sim_build
        if test_name in sim_build_coverage:
            for metric in ['line', 'toggle', 'branch']:
                merged['code_coverage'][metric]['covered'] += sim_build_coverage[test_name][metric]['covered']
                merged['code_coverage'][metric]['total'] += sim_build_coverage[test_name][metric]['total']

    # If no summary files, just use sim_build coverage
    if not coverage_files.get('summaries') and sim_build_coverage:
        for test_name, stats in sim_build_coverage.items():
            line_pct = (stats['line']['covered'] / stats['line']['total'] * 100
                        if stats['line']['total'] > 0 else 0.0)
            toggle_pct = (stats['toggle']['covered'] / stats['toggle']['total'] * 100
                          if stats['toggle']['total'] > 0 else 0.0)

            test_info = {
                'name': test_name,
                'protocol_pct': 0.0,  # No protocol data without summaries
                'line_pct': line_pct,
                'toggle_pct': toggle_pct,
            }
            merged['tests'].append(test_info)
            merged['test_count'] += 1

            total_line += line_pct
            total_toggle += toggle_pct

            for metric in ['line', 'toggle', 'branch']:
                merged['code_coverage'][metric]['covered'] += stats[metric]['covered']
                merged['code_coverage'][metric]['total'] += stats[metric]['total']

    # Calculate final percentages
    if merged['test_count'] > 0:
        merged['overall']['protocol_pct'] = total_protocol / merged['test_count']

    # For line coverage, use verilator_coverage to properly merge coverage.dat files
    sim_build_files = coverage_files.get('sim_build_coverage', [])
    if sim_build_files:
        merged_line_pct, lines_covered, lines_total = get_merged_verilator_coverage(sim_build_files)
        if lines_total > 0:
            merged['overall']['line_pct'] = merged_line_pct
            merged['code_coverage']['line']['covered'] = lines_covered
            merged['code_coverage']['line']['total'] = lines_total
        else:
            merged['overall']['line_pct'] = total_line / merged['test_count'] if merged['test_count'] > 0 else 0.0
    else:
        merged['overall']['line_pct'] = total_line / merged['test_count'] if merged['test_count'] > 0 else 0.0

    merged['overall']['toggle_pct'] = total_toggle / merged['test_count'] if merged['test_count'] > 0 else 0.0

    # Calculate per-group coverage
    for group_name, group_data in merged['protocol_groups'].items():
        covered = sum(1 for p in group_data['points'].values() if p['hits'] >= p['goal'])
        total = len(group_data['points'])
        group_data['covered'] = covered
        group_data['total'] = total
        group_data['coverage_pct'] = (covered / total * 100) if total > 0 else 0.0

    return merged


def generate_markdown_report(data: Dict[str, Any], component: str, detailed: bool = False) -> str:
    """Generate a markdown coverage report.

    Args:
        data: Merged coverage data
        component: Component name (for headers)
        detailed: Include detailed per-point coverage

    Returns:
        Markdown formatted report string
    """
    lines = []

    component_upper = component.upper()
    lines.append(f"# {component_upper} Component Coverage Report")
    lines.append("")
    lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"**Tests Analyzed:** {data['test_count']}")
    lines.append("")

    # Executive Summary
    lines.append("## Executive Summary")
    lines.append("")
    lines.append("| Metric | Coverage | Target | Status |")
    lines.append("|--------|----------|--------|--------|")

    protocol_pct = data['overall']['protocol_pct']
    line_pct = data['overall']['line_pct']

    def status(pct, target):
        if pct >= target:
            return "PASS"
        elif pct >= target * 0.8:
            return "WARN"
        else:
            return "FAIL"

    if data['protocol_groups']:
        lines.append(f"| **Protocol Coverage** | {protocol_pct:.1f}% | 80% | {status(protocol_pct, 80)} |")

    line_covered = data.get('code_coverage', {}).get('line', {}).get('covered', 0)
    line_total = data.get('code_coverage', {}).get('line', {}).get('total', 0)
    if line_total > 0:
        lines.append(f"| **Line Coverage** | {line_pct:.1f}% ({line_covered}/{line_total}) | 80% | {status(line_pct, 80)} |")
    else:
        lines.append(f"| **Line Coverage** | {line_pct:.1f}% | 80% | {status(line_pct, 80)} |")
    lines.append("")

    # Protocol Coverage by Group (if available)
    if data['protocol_groups']:
        lines.append("## Protocol Coverage by Group")
        lines.append("")
        lines.append("| Group | Covered | Total | Coverage | Status |")
        lines.append("|-------|---------|-------|----------|--------|")

        for group_name, group_data in sorted(data['protocol_groups'].items()):
            covered = group_data.get('covered', 0)
            total = group_data.get('total', 0)
            pct = group_data.get('coverage_pct', 0)
            lines.append(f"| {group_name} | {covered} | {total} | {pct:.1f}% | {status(pct, 80)} |")

        lines.append("")

    # Detailed per-point coverage
    if detailed and data['protocol_groups']:
        lines.append("## Detailed Coverage Points")
        lines.append("")

        for group_name, group_data in sorted(data['protocol_groups'].items()):
            lines.append(f"### {group_name}")
            lines.append("")
            lines.append("| Point | Hits | Goal | Covered |")
            lines.append("|-------|------|------|---------|")

            for point_name, point_data in sorted(group_data['points'].items()):
                hits = point_data.get('hits', 0)
                goal = point_data.get('goal', 1)
                is_covered = "Yes" if hits >= goal else "No"
                lines.append(f"| {point_name} | {hits} | {goal} | {is_covered} |")

            lines.append("")

    # Per-Test Results
    lines.append("## Per-Test Coverage")
    lines.append("")
    if data['protocol_groups']:
        lines.append("| Test Name | Protocol | Line |")
        lines.append("|-----------|----------|------|")
        for test in sorted(data['tests'], key=lambda x: x['name']):
            lines.append(f"| {test['name'][:60]} | {test['protocol_pct']:.1f}% | {test['line_pct']:.1f}% |")
    else:
        lines.append("| Test Name | Line |")
        lines.append("|-----------|------|")
        for test in sorted(data['tests'], key=lambda x: x['name']):
            lines.append(f"| {test['name'][:60]} | {test['line_pct']:.1f}% |")

    lines.append("")

    # Coverage Gaps
    if data['protocol_groups']:
        lines.append("## Coverage Gaps")
        lines.append("")

        uncovered = []
        for group_name, group_data in data['protocol_groups'].items():
            for point_name, point_data in group_data.get('points', {}).items():
                if point_data.get('hits', 0) < point_data.get('goal', 1):
                    uncovered.append({
                        'group': group_name,
                        'point': point_name,
                        'hits': point_data.get('hits', 0),
                        'goal': point_data.get('goal', 1),
                    })

        if uncovered:
            lines.append(f"**{len(uncovered)} coverage points not hit:**")
            lines.append("")
            for item in uncovered[:30]:
                lines.append(f"- **{item['group']}**: {item['point']} ({item['hits']}/{item['goal']} hits)")
            if len(uncovered) > 30:
                lines.append(f"- ... and {len(uncovered) - 30} more")
        else:
            lines.append("All protocol coverage points were hit!")

        lines.append("")

    lines.append("---")
    lines.append("")
    lines.append("## Recommendations")
    lines.append("")

    if data['protocol_groups'] and protocol_pct < 80:
        lines.append("- **Increase Protocol Coverage**: Add tests for uncovered transaction types")
    if line_pct < 80:
        lines.append("- **Increase Line Coverage**: Add tests for untested code paths")
    if (not data['protocol_groups'] or protocol_pct >= 80) and line_pct >= 80:
        lines.append("- Coverage goals met! Consider adding edge case tests for robustness.")

    lines.append("")
    lines.append("---")
    lines.append(f"*Report generated by RTLDesignSherpa coverage infrastructure*")
    lines.append(f"*Component: {component}*")

    return '\n'.join(lines)


def generate_html_report(data: Dict[str, Any], component: str) -> str:
    """Generate an HTML coverage report.

    Args:
        data: Merged coverage data
        component: Component name

    Returns:
        HTML formatted report string
    """
    protocol_pct = data['overall']['protocol_pct']
    line_pct = data['overall']['line_pct']
    component_upper = component.upper()

    html = f"""<!DOCTYPE html>
<html>
<head>
    <title>{component_upper} Coverage Report</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; margin: 40px; }}
        h1 {{ color: #333; }}
        h2 {{ color: #555; border-bottom: 1px solid #ddd; padding-bottom: 10px; }}
        table {{ border-collapse: collapse; width: 100%; margin: 20px 0; }}
        th, td {{ border: 1px solid #ddd; padding: 12px; text-align: left; }}
        th {{ background-color: #4a90d9; color: white; }}
        tr:nth-child(even) {{ background-color: #f9f9f9; }}
        .pass {{ color: #28a745; font-weight: bold; }}
        .warn {{ color: #ffc107; font-weight: bold; }}
        .fail {{ color: #dc3545; font-weight: bold; }}
        .summary-box {{ display: flex; gap: 20px; margin: 20px 0; }}
        .metric-card {{ background: #f5f5f5; padding: 20px; border-radius: 8px; flex: 1; text-align: center; }}
        .metric-value {{ font-size: 48px; font-weight: bold; }}
        .metric-label {{ color: #666; margin-top: 10px; }}
        .progress-bar {{ background: #e0e0e0; border-radius: 10px; height: 20px; overflow: hidden; }}
        .progress-fill {{ height: 100%; transition: width 0.3s; }}
        .progress-fill.good {{ background: #28a745; }}
        .progress-fill.ok {{ background: #ffc107; }}
        .progress-fill.bad {{ background: #dc3545; }}
        footer {{ margin-top: 40px; color: #666; font-size: 12px; }}
    </style>
</head>
<body>
    <h1>{component_upper} Component Coverage Report</h1>
    <p><strong>Generated:</strong> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
    <p><strong>Tests Analyzed:</strong> {data['test_count']}</p>

    <div class="summary-box">
"""

    if data['protocol_groups']:
        html += f"""        <div class="metric-card">
            <div class="metric-value" style="color: {'#28a745' if protocol_pct >= 80 else '#dc3545'}">
                {protocol_pct:.1f}%
            </div>
            <div class="metric-label">Protocol Coverage</div>
            <div class="progress-bar">
                <div class="progress-fill {'good' if protocol_pct >= 80 else 'bad'}" style="width: {min(100, protocol_pct)}%"></div>
            </div>
        </div>
"""

    html += f"""        <div class="metric-card">
            <div class="metric-value" style="color: {'#28a745' if line_pct >= 80 else '#dc3545'}">
                {line_pct:.1f}%
            </div>
            <div class="metric-label">Line Coverage</div>
            <div class="progress-bar">
                <div class="progress-fill {'good' if line_pct >= 80 else 'bad'}" style="width: {min(100, line_pct)}%"></div>
            </div>
        </div>
    </div>
"""

    if data['protocol_groups']:
        html += """
    <h2>Protocol Coverage by Group</h2>
    <table>
        <tr><th>Group</th><th>Covered</th><th>Total</th><th>Coverage</th><th>Status</th></tr>
"""
        for group_name, group_data in sorted(data['protocol_groups'].items()):
            covered = group_data.get('covered', 0)
            total = group_data.get('total', 0)
            pct = group_data.get('coverage_pct', 0)
            status_class = 'pass' if pct >= 80 else 'warn' if pct >= 60 else 'fail'
            status_text = 'PASS' if pct >= 80 else 'WARN' if pct >= 60 else 'FAIL'
            html += f'        <tr><td>{group_name}</td><td>{covered}</td><td>{total}</td><td>{pct:.1f}%</td><td class="{status_class}">{status_text}</td></tr>\n'
        html += "    </table>\n"

    html += """
    <h2>Per-Test Coverage</h2>
    <table>
"""
    if data['protocol_groups']:
        html += "        <tr><th>Test Name</th><th>Protocol</th><th>Line</th></tr>\n"
        for test in sorted(data['tests'], key=lambda x: x['name']):
            html += f'        <tr><td>{test["name"][:60]}</td><td>{test["protocol_pct"]:.1f}%</td><td>{test["line_pct"]:.1f}%</td></tr>\n'
    else:
        html += "        <tr><th>Test Name</th><th>Line</th></tr>\n"
        for test in sorted(data['tests'], key=lambda x: x['name']):
            html += f'        <tr><td>{test["name"][:60]}</td><td>{test["line_pct"]:.1f}%</td></tr>\n'

    html += f"""    </table>

    <footer>
        <p>Report generated by RTLDesignSherpa coverage infrastructure</p>
        <p>Component: {component}</p>
    </footer>
</body>
</html>
"""
    return html


def try_load_legal_config(component: str, repo_root: str):
    """Try to load legal coverage configuration for a component.

    Args:
        component: Component name
        repo_root: Repository root

    Returns:
        LegalCoverageConfig instance or None
    """
    try:
        sys.path.insert(0, os.path.join(repo_root, 'bin'))
        sys.path.insert(0, repo_root)

        # Try component-specific config first
        module_name = f"projects.components.{component}.dv.{component}_coverage.coverage_config"

        # Try import
        import importlib
        config_module = importlib.import_module(module_name)
        if hasattr(config_module, 'LegalCoverageConfig'):
            return config_module.LegalCoverageConfig.load(component)
    except (ImportError, ModuleNotFoundError, AttributeError) as e:
        # Legal config is optional
        pass
    except Exception as e:
        print(f"Note: Could not load legal config for {component}: {e}")

    return None


def calculate_legal_coverage(data: Dict[str, Any], legal_config, component: str) -> Dict[str, Any]:
    """Calculate coverage against legal points only.

    Args:
        data: Merged coverage data
        legal_config: LegalCoverageConfig instance
        component: Component name

    Returns:
        Dictionary with legal coverage stats
    """
    legal_points = legal_config.get_all_legal_points()

    result = {
        'legal_total': 0,
        'legal_covered': 0,
        'categories': {},
    }

    # Standard category to group mappings (works for most components)
    category_to_groups = {
        'axi_burst_type': ['axi_read_burst_type', 'axi_write_burst_type'],
        'axi_burst_size': ['axi_read_burst_size', 'axi_write_burst_size'],
        'axi_burst_length': ['axi_read_burst_length', 'axi_write_burst_length'],
        'axi_response': ['axi_read_response', 'axi_write_response'],
        'apb': ['apb_transactions'],
        'alignment': ['address_alignment'],
        'handshake': ['handshakes'],
        'scenario': ['scenarios'],
        'cross': ['burst_type_x_size'],
    }

    for cat_name, legal_pts in legal_points.items():
        cat_result = {
            'legal_points': list(legal_pts),
            'covered': [],
            'missing': [],
        }

        groups = category_to_groups.get(cat_name, [])
        for group_name in groups:
            if group_name not in data['protocol_groups']:
                continue

            group_data = data['protocol_groups'][group_name]
            for point_name in legal_pts:
                if point_name in group_data.get('points', {}):
                    point = group_data['points'][point_name]
                    if point.get('hits', 0) >= point.get('goal', 1):
                        if point_name not in cat_result['covered']:
                            cat_result['covered'].append(point_name)
                    else:
                        if point_name not in cat_result['missing']:
                            cat_result['missing'].append(point_name)

        result['legal_total'] += len(cat_result['covered']) + len(cat_result['missing'])
        result['legal_covered'] += len(cat_result['covered'])

        cat_total = len(cat_result['covered']) + len(cat_result['missing'])
        cat_result['coverage_pct'] = (len(cat_result['covered']) / cat_total * 100) if cat_total > 0 else 0.0

        result['categories'][cat_name] = cat_result

    result['legal_coverage_pct'] = (
        result['legal_covered'] / result['legal_total'] * 100
        if result['legal_total'] > 0 else 0.0
    )

    return result


def generate_legal_coverage_section(data: Dict[str, Any], legal_result: Dict[str, Any], component: str) -> str:
    """Generate markdown section for legal coverage."""
    lines = []
    component_upper = component.upper()

    lines.append(f"## Legal Coverage ({component_upper}-Specific)")
    lines.append("")
    lines.append(f"This section shows coverage against **legal variations only** - the AXI/APB")
    lines.append(f"transaction types that {component_upper} actually uses, rather than the full protocol space.")
    lines.append("")

    lines.append(f"**Overall Legal Coverage: {legal_result['legal_coverage_pct']:.1f}%**")
    lines.append(f"({legal_result['legal_covered']}/{legal_result['legal_total']} legal points covered)")
    lines.append("")

    lines.append("### Legal Coverage by Category")
    lines.append("")
    lines.append("| Category | Covered | Total | Coverage |")
    lines.append("|----------|---------|-------|----------|")

    for cat_name, cat_data in sorted(legal_result['categories'].items()):
        covered = len(cat_data['covered'])
        total = covered + len(cat_data['missing'])
        pct = cat_data['coverage_pct']
        lines.append(f"| {cat_name} | {covered} | {total} | {pct:.1f}% |")

    lines.append("")

    all_missing = []
    for cat_name, cat_data in legal_result['categories'].items():
        for point in cat_data['missing']:
            all_missing.append(f"{cat_name}: {point}")

    if all_missing:
        lines.append("### Missing Legal Coverage Points")
        lines.append("")
        for item in all_missing:
            lines.append(f"- {item}")
        lines.append("")
    else:
        lines.append("All legal coverage points hit!")
        lines.append("")

    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description='Generate coverage report for RTL Design Sherpa components',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Auto-detect component from current directory
  python generate_coverage_report.py

  # Specify component
  python generate_coverage_report.py --component rapids
  python generate_coverage_report.py --component stream

  # Custom coverage directory
  python generate_coverage_report.py -c /path/to/tests

  # Generate HTML and include legal coverage
  python generate_coverage_report.py --html --legal
        """)
    parser.add_argument('--component', '-C',
                        help='Component name (stream, rapids, bridge, etc.). Auto-detected if not specified.')
    parser.add_argument('--coverage-dir', '-c',
                        help='Path to tests directory. Defaults to component\'s dv/tests/')
    parser.add_argument('--output-dir', '-o',
                        help='Output directory for reports. Defaults to coverage_data/reports/')
    parser.add_argument('--detailed', '-d',
                        action='store_true',
                        help='Include detailed per-point coverage')
    parser.add_argument('--html',
                        action='store_true',
                        help='Generate HTML report in addition to Markdown')
    parser.add_argument('--json',
                        action='store_true',
                        help='Output merged coverage data as JSON')
    parser.add_argument('--legal', '-l',
                        action='store_true',
                        help='Include legal coverage analysis (if component has legal config)')

    args = parser.parse_args()

    # Get repo root
    repo_root = get_repo_root()

    # Determine component
    component = args.component or detect_component()
    if not component:
        print("Error: Could not detect component. Please specify with --component")
        print("Example: python generate_coverage_report.py --component rapids")
        return 1

    # Get paths
    paths = get_component_paths(component, repo_root)

    if not os.path.exists(paths['base_dir']):
        print(f"Error: Component directory not found: {paths['base_dir']}")
        return 1

    # Determine coverage directory
    tests_dir = args.coverage_dir or paths['tests_dir']
    output_dir = args.output_dir or paths['reports_dir']
    os.makedirs(output_dir, exist_ok=True)

    print("=" * 70)
    print(f"{component.upper()} Coverage Report Generator")
    print("=" * 70)
    print(f"Repository root: {repo_root}")
    print(f"Component: {component}")
    print(f"Tests directory: {tests_dir}")
    print(f"Output directory: {output_dir}")
    print()

    # Find coverage files
    files = find_coverage_files(tests_dir)

    if not files['sim_build_coverage'] and not files['summaries']:
        print("No coverage data found!")
        print(f"Looking for coverage.dat files in: {tests_dir}/*/local_sim_build/")
        print("\nTo collect coverage, run tests with:")
        print(f"  COVERAGE=1 pytest projects/components/{component}/dv/tests/ -v")
        return 1

    print(f"Found {len(files.get('sim_build_coverage', []))} coverage.dat files")
    if files.get('summaries'):
        print(f"Found {len(files['summaries'])} summary files")

    # Merge coverage data
    merged = merge_coverage_data(files)

    # Generate timestamp for filenames
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')

    # Save merged JSON
    if args.json:
        json_path = os.path.join(output_dir, f'merged_coverage_{timestamp}.json')
        with open(json_path, 'w') as f:
            json.dump(merged, f, indent=2)
        print(f"Saved JSON: {json_path}")

    # Always save latest merged
    latest_json = os.path.join(output_dir, 'latest_merged_coverage.json')
    with open(latest_json, 'w') as f:
        json.dump(merged, f, indent=2)

    # Generate Markdown report
    md_report = generate_markdown_report(merged, component, detailed=args.detailed)

    # Add legal coverage analysis if requested
    legal_result = None
    if args.legal:
        legal_config = try_load_legal_config(component, repo_root)
        if legal_config:
            legal_result = calculate_legal_coverage(merged, legal_config, component)
            legal_section = generate_legal_coverage_section(merged, legal_result, component)
            # Insert legal coverage section after executive summary
            lines = md_report.split('\n')
            insert_idx = None
            for i, line in enumerate(lines):
                if line.startswith('## Protocol Coverage by Group') or line.startswith('## Per-Test Coverage'):
                    insert_idx = i
                    break
            if insert_idx:
                lines.insert(insert_idx, legal_section)
                lines.insert(insert_idx, '')
                md_report = '\n'.join(lines)
        else:
            print(f"Note: No legal coverage config found for {component}")

    md_path = os.path.join(output_dir, f'coverage_report_{timestamp}.md')
    with open(md_path, 'w') as f:
        f.write(md_report)
    print(f"Saved Markdown: {md_path}")

    # Save as latest
    latest_md = os.path.join(output_dir, 'latest_coverage_report.md')
    with open(latest_md, 'w') as f:
        f.write(md_report)

    # Generate HTML report
    if args.html:
        html_report = generate_html_report(merged, component)
        html_path = os.path.join(output_dir, f'coverage_report_{timestamp}.html')
        with open(html_path, 'w') as f:
            f.write(html_report)
        print(f"Saved HTML: {html_path}")

        latest_html = os.path.join(output_dir, 'latest_coverage_report.html')
        with open(latest_html, 'w') as f:
            f.write(html_report)

    # Print summary
    print()
    print("=" * 70)
    print("COVERAGE SUMMARY")
    print("=" * 70)
    print(f"Tests analyzed:     {merged['test_count']}")
    if merged['protocol_groups']:
        print(f"Protocol Coverage:  {merged['overall']['protocol_pct']:.1f}% (full protocol space)")
    print(f"Line Coverage:      {merged['overall']['line_pct']:.1f}%")

    if legal_result:
        print()
        print(f"Legal Coverage:     {legal_result['legal_coverage_pct']:.1f}% ({component.upper()}-specific points)")
        print(f"  Covered: {legal_result['legal_covered']}/{legal_result['legal_total']} legal points")
    print()

    protocol_ok = merged['overall']['protocol_pct'] >= 80 if merged['protocol_groups'] else True
    line_ok = merged['overall']['line_pct'] >= 80
    legal_ok = legal_result is None or legal_result['legal_coverage_pct'] >= 80

    if protocol_ok and line_ok:
        print("Status: PASS - Coverage goals met!")
        return 0
    elif legal_result and legal_ok:
        print("Status: PASS - Legal coverage goal met!")
        print(f"  (Full protocol coverage low, but all {component.upper()}-specific points covered)")
        return 0
    else:
        print("Status: BELOW TARGET - Coverage below 80%")
        if legal_result and not legal_ok:
            print(f"  Missing {component.upper()}-specific legal coverage points!")
        return 1


if __name__ == '__main__':
    sys.exit(main())
