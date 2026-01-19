#!/usr/bin/env python3
"""
Update Converter testplans with coverage hit counts.

This script:
1. Parses Verilator coverage .dat files
2. Aggregates line hit counts
3. Updates YAML testplans with coverage_points and hit_count data

Usage:
    python3 bin/update_converter_testplan_coverage.py
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

    Returns:
        Dict mapping (filename, line_num) -> hit_count
    """
    coverage = defaultdict(int)

    with open(dat_file, 'r') as f:
        for line in f:
            # Verilator coverage format: C 'filename.svlXXXn...' count
            if not line.startswith('C '):
                continue

            # Extract filename and line number
            match = re.search(r"'f([^']+\.sv)l(\d+)n", line)
            if not match:
                continue

            filepath = match.group(1)
            line_num = int(match.group(2))

            # Extract hit count (last field)
            parts = line.strip().split()
            if len(parts) < 2:
                continue
            hit_count = int(parts[-1])

            # Only store basename for matching
            filename = os.path.basename(filepath)
            coverage[(filename, line_num)] = max(coverage[(filename, line_num)], hit_count)

    return coverage

def merge_coverage_files(coverage_dir: Path, module_name: str) -> Dict[Tuple[str, int], int]:
    """
    Merge all coverage files for a module.

    Args:
        coverage_dir: Directory containing coverage.dat files
        module_name: Name of module (e.g., 'axi4_dwidth_converter_rd')

    Returns:
        Merged coverage dict
    """
    merged = defaultdict(int)
    files_found = 0

    # Find all coverage.dat files in local_sim_build subdirectories
    coverage_files = list(coverage_dir.rglob('coverage.dat'))
    print(f"  Searching {len(coverage_files)} coverage files...")

    for coverage_file in coverage_files:
        # Read coverage file and check if it contains our module
        file_coverage = parse_coverage_dat(coverage_file)

        # Debug: Show sample filenames from first coverage file
        if files_found == 0 and file_coverage:
            sample_files = list(set([fname for fname, _ in list(file_coverage.keys())[:10]]))
            print(f"    Sample filenames: {sample_files[:3]}")

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
            if module_name in key[0]:  # Only merge data for this module
                merged[key] = max(merged[key], count)

    print(f"  Merged {files_found} coverage files")
    return merged

def update_testplan(testplan_file: Path, coverage_dir: Path):
    """
    Update testplan YAML with coverage data.

    Args:
        testplan_file: Path to testplan YAML file
        coverage_dir: Directory containing coverage data
    """
    print(f"\nProcessing {testplan_file.name}...")

    # Load testplan
    with open(testplan_file, 'r') as f:
        testplan = yaml.safe_load(f)

    # Get module name from testplan
    module_name = testplan.get('module', testplan.get('dut_name', ''))
    if not module_name:
        print(f"  ERROR: No module or dut_name in testplan!")
        return

    print(f"  Module: {module_name}")

    # Merge coverage files
    coverage = merge_coverage_files(coverage_dir, module_name)

    if not coverage:
        print(f"  WARNING: No coverage data found for {module_name}")
        return

    # Update coverage points with hit counts
    if 'coverage_points' not in testplan:
        print(f"  WARNING: No coverage_points in testplan!")
        return

    updated_count = 0
    total_lines = 0
    lines_hit = 0

    for point in testplan['coverage_points']:
        line_num = point.get('line')
        if line_num is None:
            continue

        total_lines += 1

        # Look up hit count
        hit_count = coverage.get((f"{module_name}.sv", line_num), 0)
        point['hit_count'] = hit_count

        # Update covered status
        if hit_count > 0:
            point['covered'] = True
            lines_hit += 1
            updated_count += 1
        else:
            point['covered'] = False

    # Add coverage stats
    testplan['coverage_stats'] = {
        'total_lines': total_lines,
        'lines_covered': lines_hit,
        'line_coverage_pct': round(lines_hit / total_lines * 100, 1) if total_lines > 0 else 0,
    }

    # Write updated testplan
    with open(testplan_file, 'w') as f:
        yaml.dump(testplan, f, default_flow_style=False, sort_keys=False, indent=2)

    print(f"  Updated! {updated_count} coverage points with hit counts")
    print(f"  Line coverage: {lines_hit}/{total_lines} ({lines_hit/total_lines*100:.1f}%)")

def main():
    """Main entry point."""
    repo_root = Path('/mnt/data/github/rtldesignsherpa')

    # Process converter testplans
    testplan_dir = repo_root / 'projects/components/converters/dv/testplans'
    coverage_dir = repo_root / 'projects/components/converters/dv/tests/local_sim_build'

    if not coverage_dir.exists():
        print(f"Coverage directory not found: {coverage_dir}")
        return 1

    if not testplan_dir.exists():
        print(f"Testplan directory not found: {testplan_dir}")
        return 1

    # Find all testplan YAML files
    testplan_files = list(testplan_dir.glob('*_testplan.yaml'))

    if not testplan_files:
        print(f"No testplan files found in {testplan_dir}")
        return 1

    print(f"Found {len(testplan_files)} testplan files")

    for testplan_file in sorted(testplan_files):
        try:
            update_testplan(testplan_file, coverage_dir)
        except Exception as e:
            print(f"Error processing {testplan_file.name}: {e}")
            import traceback
            traceback.print_exc()

    print("\nDone!")
    return 0

if __name__ == '__main__':
    sys.exit(main())
