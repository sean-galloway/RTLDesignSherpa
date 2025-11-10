#!/usr/bin/env python3
"""
Update performance markdown reports from JSON test results.

Purpose: Parse JSON performance results and populate markdown report tables.
         Run this after performance tests complete to update reports.

Author: RTL Design Sherpa
Created: 2025-10-28
"""

import json
import re
import argparse
from pathlib import Path
from typing import Dict, List, Tuple


def parse_json_results(json_dir: Path) -> Dict[str, Dict]:
    """Parse all JSON results from performance tests.

    Args:
        json_dir: Directory containing JSON result files

    Returns:
        Dictionary mapping config keys to result data
    """
    results = {}

    for json_file in json_dir.glob('*.json'):
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)

            # Extract config parameters
            config = data['config']
            metrics = data['metrics']

            # Create key from config
            version = config['version']
            engine = config['engine']
            data_width = config['data_width_bits']
            burst_size = config['burst_size_bytes']
            memory_type = config['memory_type']

            key = (version, engine, data_width, burst_size, memory_type)
            results[key] = {
                'config': config,
                'metrics': metrics
            }

        except Exception as e:
            print(f"Warning: Could not parse {json_file}: {e}")

    return results


def format_metric(value: float, precision: int = 2) -> str:
    """Format metric value for markdown table.

    Args:
        value: Metric value
        precision: Number of decimal places

    Returns:
        Formatted string
    """
    if isinstance(value, float):
        return f"{value:.{precision}f}"
    elif isinstance(value, int):
        return f"{value:,}"
    else:
        return str(value)


def update_report_table(report_path: Path, results: Dict[str, Dict],
                        version: str, engine: str) -> bool:
    """Update markdown report with actual performance data.

    Args:
        report_path: Path to markdown report file
        results: Dictionary of test results
        version: Version (v1, v2, v3)
        engine: Engine type (read, write)

    Returns:
        True if report was updated, False otherwise
    """
    if not report_path.exists():
        print(f"Error: Report not found: {report_path}")
        return False

    # Read current report
    with open(report_path, 'r') as f:
        lines = f.readlines()

    modified = False
    new_lines = []

    i = 0
    while i < len(lines):
        line = lines[i]
        new_lines.append(line)

        # Check if this is a table row with TBD values
        if '|' in line and 'TBD' in line:
            # Extract memory type and latency from the row
            match = re.search(r'\|\s*(\w+)\s*\|\s*(\d+)', line)
            if match:
                memory_type = match.group(1)
                latency = int(match.group(2))

                # Determine data width and burst size from context
                # Look backwards for section headers
                data_width = None
                burst_size = None

                for j in range(i-1, max(0, i-20), -1):
                    if 'Data Width' in lines[j] and 'bits' in lines[j]:
                        dw_match = re.search(r'(\d+)\s*bits', lines[j])
                        if dw_match:
                            data_width = int(dw_match.group(1))
                    if 'Burst Size' in lines[j] and 'bytes' in lines[j]:
                        bs_match = re.search(r'(\d+)\s*bytes', lines[j])
                        if bs_match:
                            burst_size = int(bs_match.group(1))
                    if data_width and burst_size:
                        break

                # Look up result
                if data_width and burst_size:
                    key = (version, engine, data_width, burst_size, memory_type)

                    if key in results:
                        result = results[key]
                        metrics = result['metrics']

                        # Replace TBD values with actual metrics
                        new_line = line

                        # Total cycles
                        new_line = re.sub(r'TBD(?=\s*\|[^|]*\|[^|]*\|)',
                                        format_metric(metrics['total_cycles']),
                                        new_line, count=1)

                        # Total beats (already known from config, but update anyway)
                        new_line = re.sub(r'TBD(?=\s*\|[^|]*\|)',
                                        format_metric(metrics['total_beats']),
                                        new_line, count=1)

                        # Bandwidth (beats/cycle)
                        new_line = re.sub(r'TBD(?=\s*\|[^|]*\|)',
                                        format_metric(metrics['bandwidth_beats_per_cycle'], 4),
                                        new_line, count=1)

                        # Bandwidth (GB/s)
                        new_line = re.sub(r'TBD(?=\s*\|)',
                                        format_metric(metrics['bandwidth_gbps'], 2),
                                        new_line, count=1)

                        # Efficiency (%)
                        new_line = re.sub(r'TBD',
                                        format_metric(metrics['efficiency_percent'], 2),
                                        new_line, count=1)

                        # Update the line if it changed
                        if new_line != line:
                            new_lines[-1] = new_line
                            modified = True
                            print(f"Updated: {memory_type} @ {latency} cycles (DW={data_width}, BS={burst_size})")

        i += 1

    # Write updated report if modified
    if modified:
        with open(report_path, 'w') as f:
            f.writelines(new_lines)
        print(f"✓ Updated: {report_path}")
        return True
    else:
        print(f"  No updates needed: {report_path}")
        return False


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Update performance markdown reports from JSON test results'
    )
    parser.add_argument(
        '--json-dir',
        type=Path,
        default=Path('dv/tests/performance_results'),
        help='Directory containing JSON result files'
    )
    parser.add_argument(
        '--reports-dir',
        type=Path,
        default=Path('reports'),
        help='Directory containing markdown reports'
    )
    parser.add_argument(
        '--version',
        choices=['v1', 'v2', 'v3', 'all'],
        default='all',
        help='Which version reports to update'
    )
    parser.add_argument(
        '--engine',
        choices=['read', 'write', 'all'],
        default='all',
        help='Which engine reports to update'
    )

    args = parser.parse_args()

    # Resolve paths relative to script location
    script_dir = Path(__file__).parent.parent
    json_dir = script_dir / args.json_dir
    reports_dir = script_dir / args.reports_dir

    if not json_dir.exists():
        print(f"Error: JSON directory not found: {json_dir}")
        return 1

    if not reports_dir.exists():
        print(f"Error: Reports directory not found: {reports_dir}")
        return 1

    print(f"Parsing JSON results from: {json_dir}")
    results = parse_json_results(json_dir)
    print(f"Found {len(results)} test results")

    # Determine which reports to update
    versions = ['v1', 'v2', 'v3'] if args.version == 'all' else [args.version]
    engines = ['read', 'write'] if args.engine == 'all' else [args.engine]

    updated_count = 0

    for version in versions:
        for engine in engines:
            report_name = f"{version}_{engine}_performance.md"
            report_path = reports_dir / report_name

            print(f"\nProcessing: {report_name}")

            if update_report_table(report_path, results, version, engine):
                updated_count += 1

    print(f"\n{'='*80}")
    print(f"Summary: Updated {updated_count} reports")
    print(f"{'='*80}")

    return 0


if __name__ == '__main__':
    exit(main())
