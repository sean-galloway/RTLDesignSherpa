#!/usr/bin/env python3
"""
Update RAPIDS testplans with coverage hit counts.

This script:
1. Parses Verilator coverage .dat files
2. Aggregates line hit counts
3. Updates YAML testplans with coverage_points and hit_count data

Usage:
    python3 bin/update_testplan_coverage.py
"""

import os
import sys
import re
import yaml
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple

def parse_coverage_dat(dat_file: Path) -> Dict[Tuple[str, int], int]:
    """
    Parse Verilator coverage .dat file.

    Verilator uses control characters as delimiters:
      ^A = 0x01 (field separator)
      ^B = 0x02 (value separator)

    Format: C '^Af^B<filepath>^Al^B<linenum>^An^B...' <count>

    Returns:
        Dict mapping (filename, line_num) -> hit_count
    """
    coverage = defaultdict(int)

    with open(dat_file, 'r') as f:
        for line in f:
            # Verilator coverage format: C '...' count
            if not line.startswith('C '):
                continue

            # Extract hit count (last field after quote)
            parts = line.strip().split("'")
            if len(parts) < 3:
                continue
            try:
                hit_count = int(parts[-1].strip())
            except (ValueError, IndexError):
                continue

            # Parse Verilator control character format
            # Fields are separated by ^A (0x01), values by ^B (0x02)
            fields = parts[1].split('\x01')  # Split by ^A

            filepath = None
            line_num = None

            for field in fields:
                if '\x02' not in field:
                    continue
                key, value = field.split('\x02', 1)  # Split by ^B

                if key == 'f':  # File
                    filepath = value
                elif key == 'l':  # Line number
                    try:
                        line_num = int(value)
                    except ValueError:
                        continue

            if filepath and line_num is not None and filepath.endswith('.sv'):
                # Only store basename for matching
                filename = os.path.basename(filepath)
                coverage[(filename, line_num)] = max(coverage[(filename, line_num)], hit_count)

    return coverage

def merge_coverage_files(coverage_dir: Path, module_name: str) -> Dict[Tuple[str, int], int]:
    """
    Merge all coverage files for a module.

    Args:
        coverage_dir: Directory containing coverage.dat files
        module_name: Name of module (e.g., 'scheduler_beats')

    Returns:
        Merged coverage dict
    """
    merged = defaultdict(int)
    files_found = 0

    # Find all coverage.dat files in local_sim_build subdirectories
    for coverage_file in coverage_dir.rglob('coverage.dat'):
        # Read coverage file and check if it contains our module
        file_coverage = parse_coverage_dat(coverage_file)

        # Check if any coverage data is for our module
        has_module_data = False
        for (filename, line_num), count in file_coverage.items():
            if module_name in filename:
                has_module_data = True
                break

        if not has_module_data:
            continue

        files_found += 1
        print(f"    Found coverage: {coverage_file.parent.name}")

        # Merge (take max hit count)
        for key, count in file_coverage.items():
            merged[key] = max(merged[key], count)

    print(f"  Merged {files_found} coverage files")
    return merged

def create_coverage_points(rtl_file: Path, coverage: Dict[Tuple[str, int], int]) -> List[Dict]:
    """
    Create coverage_points from RTL file analysis and coverage data.

    Args:
        rtl_file: Path to RTL .sv file
        coverage: Coverage hit counts

    Returns:
        List of coverage point dicts
    """
    coverage_points = []
    rtl_filename = os.path.basename(rtl_file)

    # Read RTL file to identify key sections
    with open(rtl_file, 'r') as f:
        lines = f.readlines()

    # Simple heuristic: group by major sections
    # This is simplified - real version would do deeper analysis
    in_parameters = False
    in_ports = False

    for i, line in enumerate(lines, 1):
        line_stripped = line.strip()

        # Detect parameter section
        if 'parameter' in line_stripped and not line_stripped.startswith('//'):
            if not in_parameters:
                in_parameters = True
                param_start = i

        # Detect port section
        if '(' in line_stripped and ('input' in line_stripped or 'output' in line_stripped):
            if not in_ports and not in_parameters:
                in_ports = True
                port_start = i

    # Create basic coverage points for parameters and ports
    # Note: This is a simplified version - full version would analyze FSMs, assignments, etc.

    # For now, create aggregate coverage points
    total_lines = len(lines)
    total_hits = sum(1 for (f, l), count in coverage.items() if f == rtl_filename and count > 0)
    coverage_pct = (total_hits / total_lines * 100) if total_lines > 0 else 0

    coverage_points.append({
        'line': f'1-{total_lines}',
        'type': 'module_coverage',
        'content': f'Overall module coverage ({coverage_pct:.1f}%)',
        'tracked_by': 'toggle_coverage',
        'total_lines': total_lines,
        'lines_hit': total_hits,
        'hit_count': sum(count for (f, l), count in coverage.items() if f == rtl_filename)
    })

    return coverage_points

def update_testplan(testplan_file: Path, coverage_dir: Path) -> None:
    """
    Update testplan YAML with coverage data.

    Args:
        testplan_file: Path to testplan YAML
        coverage_dir: Directory with coverage data
    """
    print(f"Processing {testplan_file.name}...")

    # Load existing testplan
    with open(testplan_file, 'r') as f:
        testplan = yaml.safe_load(f)

    module_name = testplan.get('module', '')
    rtl_file_rel = testplan.get('rtl_file', '')

    if not module_name or not rtl_file_rel:
        print(f"  Skipping - missing module or rtl_file")
        return

    # Build absolute RTL path
    repo_root = Path('/mnt/data/github/rtldesignsherpa')
    rtl_file = repo_root / rtl_file_rel

    if not rtl_file.exists():
        print(f"  Skipping - RTL file not found: {rtl_file}")
        return

    # Merge coverage data
    print(f"  Merging coverage for {module_name}...")
    coverage = merge_coverage_files(coverage_dir, module_name)

    if not coverage:
        print(f"  No coverage data found for {module_name}")
        return

    # Create coverage points
    coverage_points = create_coverage_points(rtl_file, coverage)

    # Update testplan
    testplan['coverage_points'] = coverage_points

    # Update coverage metrics
    if 'implied_coverage' in testplan:
        total_lines = coverage_points[0]['total_lines']
        lines_hit = coverage_points[0]['lines_hit']
        testplan['coverage_stats'] = {
            'total_lines': total_lines,
            'lines_covered': lines_hit,
            'line_coverage_pct': round(lines_hit / total_lines * 100, 1) if total_lines > 0 else 0,
            'total_hits': coverage_points[0]['hit_count']
        }

    # Write updated testplan
    with open(testplan_file, 'w') as f:
        yaml.dump(testplan, f, default_flow_style=False, sort_keys=False, indent=2)

    print(f"  Updated! Added {len(coverage_points)} coverage points")
    print(f"  Line coverage: {coverage_points[0]['lines_hit']}/{coverage_points[0]['total_lines']} " +
          f"({coverage_points[0]['lines_hit']/coverage_points[0]['total_lines']*100:.1f}%)")

def main():
    """Main entry point."""
    repo_root = Path('/mnt/data/github/rtldesignsherpa')

    # Process RAPIDS beats testplans
    testplan_dir = repo_root / 'projects/components/rapids/dv/testplans'
    coverage_dir = repo_root / 'projects/components/rapids/dv/tests/fub_beats/local_sim_build'

    if not coverage_dir.exists():
        print(f"Coverage directory not found: {coverage_dir}")
        return 1

    # Focus on beats testplans with 100% test coverage
    beats_testplans = [
        'scheduler_beats_testplan.yaml',
        'descriptor_engine_beats_testplan.yaml',
        'alloc_ctrl_beats_testplan.yaml',
        'drain_ctrl_beats_testplan.yaml',
        'latency_bridge_beats_testplan.yaml'
    ]

    for testplan_name in beats_testplans:
        testplan_file = testplan_dir / testplan_name
        if testplan_file.exists():
            try:
                update_testplan(testplan_file, coverage_dir)
            except Exception as e:
                print(f"Error processing {testplan_name}: {e}")
                import traceback
                traceback.print_exc()
        else:
            print(f"Testplan not found: {testplan_file}")

    print("\nDone!")
    return 0

if __name__ == '__main__':
    sys.exit(main())
