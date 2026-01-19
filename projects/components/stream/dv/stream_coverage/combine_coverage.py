# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: combine_coverage
# Purpose: Combine coverage from fub/macro/top test environments with deduplication
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream/dv/coverage
#
# Author: sean galloway
# Created: 2025-01-17

"""
Combined Coverage Report Generator for STREAM Component

Merges coverage data from all three test environments (fub, macro, top)
with DEDUPLICATION - if the same coverage point is hit in any environment,
it only counts once. This gives realistic aggregate coverage numbers.

Usage:
    python combine_coverage.py                    # Generate combined report
    python combine_coverage.py --output report.md # Specify output file

Or use via Makefile:
    make coverage-combined

Coverage data locations:
    tests/fub/coverage_data/per_test/
    tests/macro/coverage_data/per_test/
    tests/top/coverage_data/per_test/

Combined report location:
    tests/combined_coverage/
"""

import os
import sys
import json
import glob
import argparse
import logging
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Set, Any, Tuple, Optional

# Import legal coverage config for filtering
try:
    from .coverage_config import LegalCoverageConfig
    LEGAL_CONFIG_AVAILABLE = True
except ImportError:
    try:
        from coverage_config import LegalCoverageConfig
        LEGAL_CONFIG_AVAILABLE = True
    except ImportError:
        LEGAL_CONFIG_AVAILABLE = False
        LegalCoverageConfig = None


logging.basicConfig(level=logging.INFO, format='%(message)s')
log = logging.getLogger(__name__)


def get_legal_config() -> Optional['LegalCoverageConfig']:
    """Load legal coverage configuration for STREAM component."""
    if not LEGAL_CONFIG_AVAILABLE:
        return None
    try:
        return LegalCoverageConfig()
    except Exception as e:
        log.warning(f"Could not load legal config: {e}")
        return None


def is_legal_point(group_name: str, point_name: str,
                   legal_config: Optional['LegalCoverageConfig']) -> bool:
    """Check if a coverage point is legal for STREAM component.

    Args:
        group_name: Coverage group name (e.g., 'axi_read_burst_type')
        point_name: Coverage point name (e.g., 'INCR')
        legal_config: Legal coverage configuration

    Returns:
        True if point is legal (should be counted), False otherwise
    """
    if legal_config is None:
        return True  # No filtering if no config

    # Map group names to legal config categories
    category_map = {
        'axi_read_burst_type': 'axi_burst_type',
        'axi_write_burst_type': 'axi_burst_type',
        'axi_read_burst_size': 'axi_burst_size',
        'axi_write_burst_size': 'axi_burst_size',
        'axi_read_burst_length': 'axi_burst_length',
        'axi_write_burst_length': 'axi_burst_length',
        'axi_read_response': 'axi_response',
        'axi_write_response': 'axi_response',
        'apb_transactions': 'apb',
        'address_alignment': 'alignment',
        'handshakes': 'handshake',
        'scenarios': 'scenario',
        'burst_type_x_size': 'cross',
    }

    category = category_map.get(group_name)
    if category is None:
        return True  # Unknown group, assume legal

    return legal_config.is_legal(category, point_name)


def find_tests_dir() -> Path:
    """Find the tests directory containing fub/macro/top."""
    # Start from current file location
    current = Path(__file__).parent.parent  # stream_coverage -> dv

    if (current / 'tests' / 'fub').exists():
        return current / 'tests'

    # Try from cwd
    cwd = Path.cwd()
    for parent in [cwd] + list(cwd.parents):
        if (parent / 'dv' / 'tests' / 'fub').exists():
            return parent / 'dv' / 'tests'

    raise FileNotFoundError("Could not find tests directory with fub/macro/top")


def collect_coverage_files(tests_dir: Path) -> Dict[str, List[Path]]:
    """
    Collect all coverage summary files from each test environment.

    Returns:
        Dict mapping env name to list of summary JSON file paths
    """
    environments = ['fub', 'macro', 'top']
    result = {}

    for env in environments:
        per_test_dir = tests_dir / env / 'coverage_data' / 'per_test'
        if per_test_dir.exists():
            summary_files = list(per_test_dir.glob('*_summary.json'))
            result[env] = summary_files
            log.info(f"  {env}: Found {len(summary_files)} summary files")
        else:
            result[env] = []
            log.info(f"  {env}: No coverage_data directory found")

    return result


def merge_coverage_data(files_by_env: Dict[str, List[Path]],
                        legal_config: Optional['LegalCoverageConfig'] = None) -> Dict[str, Any]:
    """
    Merge coverage data from all environments with deduplication.

    A coverage point is considered "covered" if it was hit in ANY environment.
    This prevents double-counting when the same point is exercised in multiple
    test environments.

    Args:
        files_by_env: Dict mapping environment name to list of summary file paths
        legal_config: Optional legal coverage config for filtering to legal points only

    Returns:
        Merged coverage summary dictionary
    """
    merged = {
        'timestamp': datetime.now().isoformat(),
        'legal_mode': legal_config is not None,
        'environments': {},
        'tests': [],
        'groups': {},  # Merged coverage groups with deduplication
        'overall': {
            'protocol_pct': 0.0,
            'line_pct': 0.0,
            'toggle_pct': 0.0,
        }
    }

    # Track all coverage points across all environments
    # Key: (group_name, point_name) -> max hits across all envs
    all_points: Dict[Tuple[str, str], Dict[str, Any]] = {}

    # Per-environment stats
    env_stats = {}

    total_tests = 0
    total_protocol_pct = 0.0
    total_line_pct = 0.0

    for env_name, files in files_by_env.items():
        env_stats[env_name] = {
            'test_count': 0,
            'avg_protocol_pct': 0.0,
            'avg_line_pct': 0.0,
        }

        env_protocol_total = 0.0
        env_line_total = 0.0

        for summary_file in files:
            try:
                with open(summary_file, 'r') as f:
                    data = json.load(f)

                test_name = data.get('test_name', summary_file.stem)
                protocol_pct = data.get('overall', {}).get('protocol_pct', 0.0)
                line_pct = data.get('overall', {}).get('line_pct', 0.0)

                merged['tests'].append({
                    'name': test_name,
                    'environment': env_name,
                    'protocol_pct': protocol_pct,
                    'line_pct': line_pct,
                })

                env_protocol_total += protocol_pct
                env_line_total += line_pct
                env_stats[env_name]['test_count'] += 1
                total_tests += 1
                total_protocol_pct += protocol_pct
                total_line_pct += line_pct

                # Extract protocol coverage points
                protocol_data = data.get('protocol_coverage', {})
                for group_name, group_data in protocol_data.get('groups', {}).items():
                    for point_name, point_data in group_data.get('points', {}).items():
                        # Filter for legal points if legal_config is provided
                        if not is_legal_point(group_name, point_name, legal_config):
                            continue

                        key = (group_name, point_name)
                        hits = point_data.get('hits', 0)
                        goal = point_data.get('goal', 1)

                        if key not in all_points:
                            all_points[key] = {'hits': 0, 'goal': goal}

                        # Take the MAX hits across all environments
                        # This is the deduplication - if a point is hit in any env, it's covered
                        all_points[key]['hits'] = max(all_points[key]['hits'], hits)

            except Exception as e:
                log.warning(f"Failed to parse {summary_file}: {e}")

        # Calculate env averages
        if env_stats[env_name]['test_count'] > 0:
            count = env_stats[env_name]['test_count']
            env_stats[env_name]['avg_protocol_pct'] = env_protocol_total / count
            env_stats[env_name]['avg_line_pct'] = env_line_total / count

    merged['environments'] = env_stats

    # Build merged coverage groups from deduplicated points
    for (group_name, point_name), point_data in all_points.items():
        if group_name not in merged['groups']:
            merged['groups'][group_name] = {
                'covered': 0,
                'total': 0,
                'coverage_pct': 0.0,
                'points': {}
            }

        merged['groups'][group_name]['points'][point_name] = point_data

    # Calculate per-group coverage from deduplicated points
    for group_name, group_data in merged['groups'].items():
        covered = sum(1 for p in group_data['points'].values() if p['hits'] >= p['goal'])
        total = len(group_data['points'])
        group_data['covered'] = covered
        group_data['total'] = total
        group_data['coverage_pct'] = (covered / total * 100) if total > 0 else 0.0

    # Calculate overall coverage from deduplicated points
    total_points = len(all_points)
    covered_points = sum(1 for p in all_points.values() if p['hits'] >= p['goal'])

    merged['overall'] = {
        'total_tests': total_tests,
        'total_points': total_points,
        'covered_points': covered_points,
        'protocol_pct': (covered_points / total_points * 100) if total_points > 0 else 0.0,
        'line_pct': (total_line_pct / total_tests) if total_tests > 0 else 0.0,
        'avg_protocol_pct': (total_protocol_pct / total_tests) if total_tests > 0 else 0.0,
    }

    return merged


def generate_combined_report(merged_data: Dict[str, Any], output_path: Path) -> str:
    """
    Generate a combined coverage report in markdown format.

    Args:
        merged_data: Merged coverage data
        output_path: Path to write the report

    Returns:
        Report content as string
    """
    lines = []

    legal_mode = merged_data.get('legal_mode', False)
    mode_str = "Legal Coverage" if legal_mode else "All Coverage Points"

    lines.append("# STREAM Combined Coverage Report")
    lines.append("")
    lines.append(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"**Total Tests:** {merged_data['overall']['total_tests']}")
    lines.append(f"**Coverage Mode:** {mode_str}")
    lines.append("")

    lines.append("## Coverage Summary (Deduplicated)")
    lines.append("")
    if legal_mode:
        lines.append("> **Legal Coverage Mode**: Only counting coverage points that are applicable")
        lines.append("> to the STREAM component (e.g., INCR bursts, 64-byte transfers).")
        lines.append("> Illegal points (FIXED/WRAP bursts, small transfer sizes) are excluded.")
    else:
        lines.append("> Coverage points hit in ANY environment count once. This gives realistic")
        lines.append("> aggregate coverage rather than inflated per-environment numbers.")
    lines.append("")

    overall = merged_data['overall']
    lines.append("| Metric | Value | Target | Status |")
    lines.append("|--------|-------|--------|--------|")

    protocol_pct = overall['protocol_pct']
    protocol_status = "PASS" if protocol_pct >= 80 else ("WARN" if protocol_pct >= 60 else "FAIL")
    lines.append(f"| Protocol Coverage (deduplicated) | {protocol_pct:.1f}% | 80% | {protocol_status} |")

    line_pct = overall['line_pct']
    line_status = "PASS" if line_pct >= 80 else ("WARN" if line_pct >= 60 else "FAIL")
    lines.append(f"| Line Coverage (average) | {line_pct:.1f}% | 80% | {line_status} |")

    lines.append(f"| Coverage Points | {overall['covered_points']}/{overall['total_points']} | - | - |")
    lines.append("")

    lines.append("## Coverage by Environment")
    lines.append("")
    lines.append("| Environment | Tests | Avg Protocol | Avg Line |")
    lines.append("|-------------|-------|--------------|----------|")

    for env_name, env_data in merged_data['environments'].items():
        count = env_data['test_count']
        protocol = env_data['avg_protocol_pct']
        line = env_data['avg_line_pct']
        lines.append(f"| {env_name} | {count} | {protocol:.1f}% | {line:.1f}% |")

    lines.append("")

    lines.append("## Protocol Coverage by Group (Deduplicated)")
    lines.append("")
    lines.append("| Group | Covered | Total | Percentage |")
    lines.append("|-------|---------|-------|------------|")

    for group_name, group_data in sorted(merged_data['groups'].items()):
        covered = group_data['covered']
        total = group_data['total']
        pct = group_data['coverage_pct']
        status = "OK" if pct >= 80 else ("!!" if pct < 50 else "")
        lines.append(f"| {group_name} | {covered} | {total} | {pct:.1f}% {status}|")

    lines.append("")

    lines.append("## Coverage Gaps (Uncovered Points)")
    lines.append("")

    uncovered = []
    for group_name, group_data in merged_data['groups'].items():
        for point_name, point_data in group_data.get('points', {}).items():
            if point_data['hits'] < point_data['goal']:
                uncovered.append(f"- **{group_name}**: `{point_name}`")

    if uncovered:
        lines.append(f"Found {len(uncovered)} uncovered coverage points:")
        lines.append("")
        lines.extend(uncovered[:100])  # Limit to first 100
        if len(uncovered) > 100:
            lines.append(f"... and {len(uncovered) - 100} more")
    else:
        lines.append("All coverage points were hit! Great job!")

    lines.append("")
    lines.append("## Per-Test Results")
    lines.append("")
    lines.append("<details>")
    lines.append("<summary>Click to expand test details</summary>")
    lines.append("")
    lines.append("| Test Name | Environment | Protocol | Line |")
    lines.append("|-----------|-------------|----------|------|")

    for test in sorted(merged_data['tests'], key=lambda x: (x['environment'], x['name'])):
        name = test['name'][:50] + "..." if len(test['name']) > 50 else test['name']
        lines.append(f"| {name} | {test['environment']} | {test['protocol_pct']:.1f}% | {test['line_pct']:.1f}% |")

    lines.append("")
    lines.append("</details>")
    lines.append("")
    lines.append("---")
    lines.append("*Report generated by STREAM combined coverage infrastructure*")
    lines.append("*Deduplication ensures each coverage point is counted only once across all environments.*")

    report_content = '\n'.join(lines)

    # Write to file
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        f.write(report_content)

    return report_content


def main():
    """Main entry point for combined coverage tool."""
    parser = argparse.ArgumentParser(
        description='Generate combined coverage report from fub/macro/top test environments'
    )
    parser.add_argument(
        '--output', '-o',
        type=str,
        default=None,
        help='Output path for markdown report (default: tests/combined_coverage/combined_report.md)'
    )
    parser.add_argument(
        '--json',
        type=str,
        default=None,
        help='Also output merged data as JSON to this path'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--legal', '-l',
        action='store_true',
        default=True,
        help='Filter for legal coverage points only (default: True)'
    )
    parser.add_argument(
        '--all-points',
        action='store_true',
        help='Include ALL coverage points (disable legal filtering)'
    )

    args = parser.parse_args()

    # Handle legal coverage mode
    use_legal = args.legal and not args.all_points

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    log.info("=" * 80)
    log.info("STREAM Combined Coverage Report Generator")
    log.info("=" * 80)
    log.info("")

    # Find tests directory
    try:
        tests_dir = find_tests_dir()
        log.info(f"Tests directory: {tests_dir}")
    except FileNotFoundError as e:
        log.error(str(e))
        sys.exit(1)

    log.info("")
    log.info("Collecting coverage files from all environments:")

    # Collect coverage files
    files_by_env = collect_coverage_files(tests_dir)

    total_files = sum(len(f) for f in files_by_env.values())
    if total_files == 0:
        log.warning("No coverage files found. Run tests with COVERAGE=1 first.")
        sys.exit(1)

    log.info("")
    log.info(f"Total coverage files: {total_files}")
    log.info("")

    # Load legal coverage config if requested
    legal_config = None
    if use_legal:
        legal_config = get_legal_config()
        if legal_config:
            log.info(f"Legal coverage mode: filtering to {legal_config.count_legal_points()} legal points")
        else:
            log.warning("Legal config not available, showing all coverage points")

    log.info("Merging coverage data with deduplication...")

    # Merge coverage data
    merged_data = merge_coverage_data(files_by_env, legal_config)

    # Determine output path
    if args.output:
        output_path = Path(args.output)
    else:
        combined_dir = tests_dir / 'combined_coverage'
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        output_path = combined_dir / f'combined_report_{timestamp}.md'

    # Generate report
    report_content = generate_combined_report(merged_data, output_path)

    # Also save as latest
    latest_path = output_path.parent / 'combined_report_latest.md'
    with open(latest_path, 'w') as f:
        f.write(report_content)

    # Optionally save JSON
    if args.json:
        json_path = Path(args.json)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        with open(json_path, 'w') as f:
            json.dump(merged_data, f, indent=2)
        log.info(f"JSON data saved: {json_path}")

    # Also save JSON by default
    json_default = output_path.parent / 'combined_coverage.json'
    with open(json_default, 'w') as f:
        json.dump(merged_data, f, indent=2)

    log.info("")
    log.info("=" * 80)
    mode_label = "LEGAL" if merged_data.get('legal_mode', False) else "ALL"
    log.info(f"COMBINED COVERAGE SUMMARY ({mode_label} POINTS - Deduplicated)")
    log.info("=" * 80)
    log.info("")

    overall = merged_data['overall']
    log.info(f"  Total Tests:       {overall['total_tests']}")
    log.info(f"  Coverage Points:   {overall['covered_points']}/{overall['total_points']}")
    log.info(f"  Protocol Coverage: {overall['protocol_pct']:.1f}%")
    log.info(f"  Line Coverage:     {overall['line_pct']:.1f}% (average)")

    if merged_data.get('legal_mode', False):
        log.info("")
        log.info("  Note: Legal mode excludes FIXED/WRAP bursts, small transfer sizes,")
        log.info("        and other points not applicable to STREAM design.")
    log.info("")

    log.info("Per-Environment:")
    for env_name, env_data in merged_data['environments'].items():
        log.info(f"  {env_name:6s}: {env_data['test_count']:3d} tests, "
                f"protocol={env_data['avg_protocol_pct']:5.1f}%, "
                f"line={env_data['avg_line_pct']:5.1f}%")

    log.info("")
    log.info(f"Report saved: {output_path}")
    log.info(f"Latest link:  {latest_path}")
    log.info("")

    # Return non-zero if coverage is below threshold
    if overall['protocol_pct'] < 60:
        log.warning("Protocol coverage is below 60% threshold!")
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
