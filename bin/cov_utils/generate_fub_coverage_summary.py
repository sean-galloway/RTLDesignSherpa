#!/usr/bin/env python3
"""
Generate per-FUB line coverage summary from Verilator annotated coverage files.

Parses annotated .sv files from coverage_merged/annotate/ directory and
generates a summary showing line coverage per module.

Usage:
    python generate_fub_coverage_summary.py <annotate_dir> [--output <file.md>]
"""

import argparse
import os
import re
from pathlib import Path
from collections import defaultdict


def parse_annotated_file(filepath: Path) -> dict:
    """
    Parse a Verilator annotated coverage file.

    Verilator annotation formats:
    - '%NNNNNN  content' = toggle coverage (signal declarations)
    - ' NNNNNN  content' = line coverage (behavioral code)

    Returns dict with:
        - total_lines: count of annotatable lines (line coverage only)
        - covered_lines: count of lines with hits > 0
        - uncovered_lines: list of (line_num, content) for uncovered lines
        - hit_counts: dict of line_num -> hit_count
        - toggle_total: count of toggle coverage points
        - toggle_covered: count of toggled signals
    """
    result = {
        'total_lines': 0,
        'covered_lines': 0,
        'uncovered_lines': [],
        'hit_counts': {},
        'toggle_total': 0,
        'toggle_covered': 0
    }

    # Pattern matches Verilator LINE coverage: ' NNNNNN  content' (space prefix)
    # where NNNNNN is hit count (6 digits, leading zeros)
    line_coverage_pattern = re.compile(r'^ (\d{6})\s+(.*)$')

    # Pattern matches Verilator TOGGLE coverage: '%NNNNNN  content' (% prefix)
    toggle_coverage_pattern = re.compile(r'^%(\d{6})\s+(.*)$')

    try:
        with open(filepath, 'r') as f:
            for line_num, line in enumerate(f, 1):
                # Check line coverage first (this is what we care about)
                match = line_coverage_pattern.match(line)
                if match:
                    hit_count = int(match.group(1))
                    content = match.group(2).strip()

                    result['total_lines'] += 1
                    result['hit_counts'][line_num] = hit_count

                    if hit_count > 0:
                        result['covered_lines'] += 1
                    else:
                        result['uncovered_lines'].append((line_num, content))
                    continue

                # Check toggle coverage (track separately)
                match = toggle_coverage_pattern.match(line)
                if match:
                    hit_count = int(match.group(1))
                    result['toggle_total'] += 1
                    if hit_count > 0:
                        result['toggle_covered'] += 1

    except Exception as e:
        print(f"Error parsing {filepath}: {e}")

    return result


def categorize_module(filename: str) -> str:
    """Categorize module by type (FUB, MACRO, common, etc.)"""
    fub_modules = [
        'scheduler', 'descriptor_engine', 'axi_read_engine', 'axi_write_engine',
        'sram_controller', 'sram_controller_unit', 'stream_latency_bridge',
        'stream_alloc_ctrl', 'stream_drain_ctrl', 'apbtodescr', 'perf_profiler'
    ]

    macro_modules = [
        'datapath_rd_test', 'datapath_wr_test', 'scheduler_group',
        'scheduler_group_array', 'monbus_axil_group', 'stream_core'
    ]

    common_modules = [
        'arbiter', 'counter', 'fifo', 'gaxi'
    ]

    name = filename.replace('.sv', '')

    if any(name.startswith(fub) or name == fub for fub in fub_modules):
        return 'FUB'
    elif any(name.startswith(macro) or name == macro for macro in macro_modules):
        return 'MACRO'
    elif any(name.startswith(c) for c in common_modules):
        return 'common'
    elif 'pkg' in name:
        return 'package'
    else:
        return 'other'


def generate_report(annotate_dir: Path, output_file: Path = None):
    """Generate coverage summary report."""

    results = {}
    category_totals = defaultdict(lambda: {'total': 0, 'covered': 0})

    # Parse all annotated files
    for sv_file in sorted(annotate_dir.glob('*.sv')):
        coverage = parse_annotated_file(sv_file)
        if coverage['total_lines'] > 0:
            results[sv_file.name] = coverage

            category = categorize_module(sv_file.name)
            category_totals[category]['total'] += coverage['total_lines']
            category_totals[category]['covered'] += coverage['covered_lines']

    # Generate report
    lines = []
    lines.append("# STREAM FUB Line Coverage Summary\n")
    lines.append(f"**Generated:** {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    lines.append(f"**Source:** `{annotate_dir}`\n")
    lines.append("")

    # Overall totals
    grand_total = sum(r['total_lines'] for r in results.values())
    grand_covered = sum(r['covered_lines'] for r in results.values())
    grand_pct = (grand_covered / grand_total * 100) if grand_total > 0 else 0

    lines.append("## Overall Summary\n")
    lines.append(f"| Metric | Value |")
    lines.append(f"|--------|-------|")
    lines.append(f"| **Total Lines** | {grand_total} |")
    lines.append(f"| **Covered Lines** | {grand_covered} |")
    lines.append(f"| **Line Coverage** | {grand_pct:.1f}% |")
    lines.append("")

    # Category breakdown
    lines.append("## Coverage by Category\n")
    lines.append("| Category | Covered | Total | Coverage |")
    lines.append("|----------|---------|-------|----------|")

    for category in ['FUB', 'MACRO', 'common', 'package', 'other']:
        if category in category_totals:
            totals = category_totals[category]
            pct = (totals['covered'] / totals['total'] * 100) if totals['total'] > 0 else 0
            lines.append(f"| {category} | {totals['covered']} | {totals['total']} | {pct:.1f}% |")

    lines.append("")

    # Per-module breakdown
    lines.append("## Coverage by Module\n")
    lines.append("| Module | Covered | Total | Coverage | Category |")
    lines.append("|--------|---------|-------|----------|----------|")

    # Sort by coverage percentage (lowest first)
    sorted_results = sorted(
        results.items(),
        key=lambda x: (x[1]['covered_lines'] / x[1]['total_lines'] if x[1]['total_lines'] > 0 else 0)
    )

    for filename, coverage in sorted_results:
        total = coverage['total_lines']
        covered = coverage['covered_lines']
        pct = (covered / total * 100) if total > 0 else 0
        category = categorize_module(filename)

        # Status indicator
        if pct >= 80:
            status = "PASS"
        elif pct >= 60:
            status = "FAIR"
        else:
            status = "LOW"

        lines.append(f"| {filename} | {covered} | {total} | {pct:.1f}% | {category} |")

    lines.append("")

    # FUB-specific detail
    lines.append("## FUB Module Details\n")

    fub_results = [(f, c) for f, c in results.items() if categorize_module(f) == 'FUB']
    fub_results.sort(key=lambda x: x[1]['covered_lines'] / x[1]['total_lines'] if x[1]['total_lines'] > 0 else 0)

    for filename, coverage in fub_results:
        total = coverage['total_lines']
        covered = coverage['covered_lines']
        pct = (covered / total * 100) if total > 0 else 0

        lines.append(f"### {filename}\n")
        lines.append(f"- **Coverage:** {covered}/{total} lines ({pct:.1f}%)")
        lines.append(f"- **Uncovered:** {total - covered} lines")

        # Show first 10 uncovered lines
        if coverage['uncovered_lines']:
            lines.append(f"\n**Sample uncovered lines:**")
            for line_num, content in coverage['uncovered_lines'][:10]:
                # Truncate long lines
                if len(content) > 80:
                    content = content[:77] + "..."
                lines.append(f"  - Line {line_num}: `{content}`")
            if len(coverage['uncovered_lines']) > 10:
                lines.append(f"  - ... and {len(coverage['uncovered_lines']) - 10} more")

        lines.append("")

    report = '\n'.join(lines)

    # Output
    if output_file:
        with open(output_file, 'w') as f:
            f.write(report)
        print(f"Report written to: {output_file}")
    else:
        print(report)

    return results


def main():
    parser = argparse.ArgumentParser(description='Generate per-FUB line coverage summary')
    parser.add_argument('annotate_dir', help='Directory containing annotated .sv files')
    parser.add_argument('--output', '-o', help='Output file (markdown)')

    args = parser.parse_args()

    annotate_dir = Path(args.annotate_dir)
    if not annotate_dir.exists():
        print(f"Error: Directory not found: {annotate_dir}")
        return 1

    output_file = Path(args.output) if args.output else None

    generate_report(annotate_dir, output_file)
    return 0


if __name__ == '__main__':
    exit(main())
