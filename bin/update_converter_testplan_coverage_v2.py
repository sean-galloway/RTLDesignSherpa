#!/usr/bin/env python3
"""
Update Converter testplans with coverage hit counts.

This script:
1. Merges Verilator coverage .dat files
2. Uses verilator_coverage --annotate to extract hit counts
3. Updates YAML testplans with coverage_points and hit_count data

Usage:
    python3 bin/update_converter_testplan_coverage_v2.py
"""

import os
import sys
import re
import yaml
import subprocess
import tempfile
from pathlib import Path
from collections import defaultdict
from typing import Dict, List

def merge_and_annotate_coverage(coverage_dir: Path, module_name: str) -> Dict[int, int]:
    """
    Merge coverage files and annotate for a module.

    Args:
        coverage_dir: Directory containing coverage.dat files
        module_name: Name of module (e.g., 'axi4_dwidth_converter_rd')

    Returns:
        Dict mapping line_num -> hit_count
    """
    # Find all coverage.dat files
    coverage_files = list(coverage_dir.rglob('coverage.dat'))
    print(f"  Found {len(coverage_files)} coverage files")

    if not coverage_files:
        return {}

    # Create temporary directory for merged coverage
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)

        # Merge all coverage files
        merged_dat = tmpdir_path / 'merged_coverage.dat'
        cmd = ['verilator_coverage', '--write', str(merged_dat)] + [str(f) for f in coverage_files]

        print(f"  Merging {len(coverage_files)} coverage files...")
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  ERROR merging coverage: {result.stderr}")
            return {}

        # Annotate merged coverage
        annotate_dir = tmpdir_path / 'annotated'
        annotate_dir.mkdir()

        cmd = ['verilator_coverage', '--annotate', str(annotate_dir), str(merged_dat)]
        print(f"  Annotating coverage...")
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  ERROR annotating coverage: {result.stderr}")
            return {}

        # Parse annotated file
        annotated_file = annotate_dir / f'{module_name}.sv'
        if not annotated_file.exists():
            print(f"  WARNING: Annotated file not found: {annotated_file}")
            return {}

        return parse_annotated_coverage(annotated_file)

def parse_annotated_coverage(annotated_file: Path) -> Dict[int, int]:
    """
    Parse verilator_coverage annotated file.

    Format:
        %000000 input logic foo;      // Line not covered
        000042 logic bar;              // Line covered 42 times
        //      // comment             // Not a code line

    Returns:
        Dict mapping line_num -> hit_count (line numbers match ORIGINAL source file)
    """
    coverage = {}
    line_num = 1

    # Verilator adds a 1-line header comment, so annotated lines are +1
    # compared to original. To get original line number, subtract 1.
    # But we're iterating through annotated file, so we need to subtract 1
    # from the annotated line number to get the original.
    #
    # Example: Original line 72 -> Annotated line 73
    # When we're at annotated line 73 (line_num=73), we want original 72
    # So: original = line_num - 1
    line_offset = -1

    with open(annotated_file, 'r') as f:
        for line in f:
            # Extract hit count from start of line
            # Format: %NNNNNN (not covered) or  NNNNNN (covered, with leading space) or NNNNNN (no space)
            match = re.match(r'^(%| ?)(\d{6})\s', line)
            if match:
                uncovered = (match.group(1) == '%')
                hit_count = 0 if uncovered else int(match.group(2))
                # Store with original line number (accounting for header offset)
                original_line_num = line_num + line_offset
                coverage[original_line_num] = hit_count

            line_num += 1

    return coverage

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

    # Merge and annotate coverage
    coverage = merge_and_annotate_coverage(coverage_dir, module_name)

    if not coverage:
        print(f"  WARNING: No coverage data found for {module_name}")
        return

    print(f"  Parsed {len(coverage)} lines of coverage data")

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
        hit_count = coverage.get(line_num, 0)
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
