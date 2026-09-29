#!/usr/bin/env python3
"""
RAPIDS Beats Coverage Analyzer

Analyzes coverage data and filters to only RAPIDS beats modules,
excluding infrastructure files (packages, monitors, GAXI, etc.)

Usage:
    python analyze_beats_coverage.py merged.info
    python analyze_beats_coverage.py --all-rapids merged.info
"""

import argparse
import sys
from pathlib import Path


def parse_lcov_info(filepath: str) -> list:
    """Parse LCOV .info file and return per-file coverage data."""
    with open(filepath, 'r') as f:
        content = f.read()

    blocks = content.split("end_of_record")
    results = []

    for block in blocks:
        if not block.strip():
            continue

        source_file = None
        lines_hit = 0
        lines_total = 0

        for line in block.split('\n'):
            if line.startswith("SF:"):
                source_file = line[3:]
            elif line.startswith("DA:"):
                parts = line[3:].split(",")
                if len(parts) >= 2:
                    lines_total += 1
                    if int(parts[1]) > 0:
                        lines_hit += 1

        if source_file and lines_total > 0:
            pct = (lines_hit / lines_total) * 100
            filename = Path(source_file).name
            results.append({
                'filename': filename,
                'filepath': source_file,
                'hit': lines_hit,
                'total': lines_total,
                'pct': pct
            })

    return results


def filter_beats_only(results: list) -> list:
    """Filter to only RAPIDS beats modules."""
    return [r for r in results if '_beats.sv' in r['filename'] and 'rapids' in r['filepath']]


def filter_all_rapids(results: list) -> list:
    """Filter to all RAPIDS modules (excluding infrastructure)."""
    exclude_patterns = [
        '_pkg.sv',           # Package files
        '_mon.sv',           # Monitor modules
        'gaxi_',             # GAXI infrastructure
        'monitor_',          # Monitor infrastructure
        'fifo_sync.sv',      # Common FIFO
        'fifo_control.sv',   # FIFO control
        'counter_bin.sv',    # Common counter
    ]

    filtered = []
    for r in results:
        if 'rapids' not in r['filepath']:
            continue

        skip = False
        for pattern in exclude_patterns:
            if pattern in r['filename']:
                skip = True
                break

        if not skip:
            filtered.append(r)

    return filtered


def print_report(results: list, title: str):
    """Print coverage report."""
    # Sort by coverage percentage
    results = sorted(results, key=lambda x: x['pct'], reverse=True)

    print(f"\n{title}")
    print("=" * 80)
    print(f"{'Module':<50} {'Hit':>6} {'Total':>6} {'Pct':>7}")
    print("-" * 80)

    total_hit = 0
    total_lines = 0

    for r in results:
        print(f"{r['filename']:<50} {r['hit']:>6} {r['total']:>6} {r['pct']:>6.1f}%")
        total_hit += r['hit']
        total_lines += r['total']

    print("-" * 80)
    overall_pct = (total_hit / total_lines) * 100 if total_lines > 0 else 0
    print(f"{'TOTAL':<50} {total_hit:>6} {total_lines:>6} {overall_pct:>6.1f}%")
    print("=" * 80)

    return overall_pct


def main():
    parser = argparse.ArgumentParser(description='Analyze RAPIDS beats coverage')
    parser.add_argument('info_file', help='Path to merged LCOV .info file')
    parser.add_argument('--all-rapids', action='store_true',
                       help='Include all RAPIDS modules (not just beats)')
    parser.add_argument('--raw', action='store_true',
                       help='Show all files without filtering')

    args = parser.parse_args()

    if not Path(args.info_file).exists():
        print(f"Error: File not found: {args.info_file}", file=sys.stderr)
        sys.exit(1)

    results = parse_lcov_info(args.info_file)

    if args.raw:
        title = "All Coverage Data (Unfiltered)"
        filtered = results
    elif args.all_rapids:
        title = "RAPIDS Modules Coverage (Excluding Infrastructure)"
        filtered = filter_all_rapids(results)
    else:
        title = "RAPIDS Beats Modules Coverage"
        filtered = filter_beats_only(results)

    if not filtered:
        print("No matching files found in coverage data.", file=sys.stderr)
        sys.exit(1)

    overall = print_report(filtered, title)

    # Summary
    target = 60.0
    if overall >= target:
        print(f"\n[PASS] Coverage {overall:.1f}% meets target {target:.1f}%")
    else:
        print(f"\n[BELOW TARGET] Coverage {overall:.1f}% < target {target:.1f}%")
        print(f"Need {target - overall:.1f}% more coverage")


if __name__ == '__main__':
    main()
