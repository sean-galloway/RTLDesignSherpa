#!/usr/bin/env python3
"""
Calculate coverage excluding verified building blocks.

Supports hierarchical exclusion levels:
  --level common     : Exclude rtl/common modules
  --level amba       : Exclude rtl/common + rtl/amba modules  
  --level fub        : Exclude common + amba + fub modules (for macro/top tests)

Usage:
    python calc_coverage_excluding_building_blocks.py <coverage.dat> --level common
    python calc_coverage_excluding_building_blocks.py <coverage.dat> --level amba
    python calc_coverage_excluding_building_blocks.py <coverage.dat> --level fub
    python calc_coverage_excluding_building_blocks.py <coverage.dat> --include-all
"""

import os
import re
import sys
import argparse
import subprocess
import tempfile
from pathlib import Path


# Exclusion patterns by level (cumulative)
EXCLUSION_LEVELS = {
    'common': [
        # rtl/common building blocks
        'counter_', 'arbiter_', 'fifo_', 'encoder', 'decoder', 
        'math_', 'clock_', 'dataint_', 'shifter_', 'bin2gray', 
        'gray2bin', 'count_leading', 'hex_to_7seg', 'cam_',
        'find_first', 'find_last', 'priority_', 'mux_', 'demux_',
        'edge_detect', 'pulse_', 'sync_', 'debounce',
    ],
    'amba': [
        # rtl/amba building blocks (adds to common)
        'apb_', 'apb5_', 'axi_', 'axi4_', 'axi5_', 'axis_', 'axis5_',
        'gaxi_', 'monbus_', 'monitor_',
    ],
    'fub': [
        # FUB-level blocks (adds to common + amba)
        'scheduler', 'descriptor_', 'axi_read_engine', 'axi_write_engine',
        'alloc_ctrl', 'drain_ctrl', 'latency_bridge', 'sram_controller',
        'apbtodescr', 'ctrlrd_', 'ctrlwr_',
    ],
}


def get_exclusions_for_level(level):
    """Get cumulative exclusion patterns for a level."""
    patterns = []
    levels_order = ['common', 'amba', 'fub']
    
    for lvl in levels_order:
        patterns.extend(EXCLUSION_LEVELS.get(lvl, []))
        if lvl == level:
            break
    
    return patterns


def calculate_coverage(annotate_dir, exclude_patterns=None):
    """Calculate coverage from annotated files, optionally excluding patterns."""
    exclude_patterns = exclude_patterns or []
    
    total_lines = 0
    covered_lines = 0
    excluded_lines = 0
    excluded_files = []
    
    results_by_file = {}
    
    for sv_file in Path(annotate_dir).glob('*.sv'):
        filename = sv_file.name
        
        # Check if this file should be excluded
        excluded = False
        for pattern in exclude_patterns:
            if filename.startswith(pattern) or pattern in filename:
                excluded = True
                break
        
        file_total = 0
        file_covered = 0
        
        with open(sv_file, 'r') as f:
            for line in f:
                match = re.match(r'^([% ])(\d{6})\s', line)
                if match:
                    file_total += 1
                    prefix = match.group(1)
                    count = int(match.group(2))
                    if prefix == ' ' or count > 0:
                        file_covered += 1
        
        if excluded:
            excluded_lines += file_total
            excluded_files.append(filename)
        else:
            total_lines += file_total
            covered_lines += file_covered
            if file_total > 0:
                results_by_file[filename] = {
                    'covered': file_covered,
                    'total': file_total,
                    'pct': file_covered / file_total * 100
                }
    
    return {
        'total_lines': total_lines,
        'covered_lines': covered_lines,
        'excluded_lines': excluded_lines,
        'excluded_files': excluded_files,
        'percentage': (covered_lines / total_lines * 100) if total_lines > 0 else 0,
        'by_file': results_by_file
    }


def main():
    parser = argparse.ArgumentParser(
        description='Calculate coverage excluding verified building blocks',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exclusion levels (cumulative):
  common  : Exclude rtl/common modules (counters, arbiters, FIFOs, math, etc.)
  amba    : Exclude common + rtl/amba modules (APB, AXI, AXIS, monitors)
  fub     : Exclude common + amba + FUB modules (scheduler, engines, etc.)

Examples:
  %(prog)s coverage.dat --level common     # For val/amba tests
  %(prog)s coverage.dat --level amba       # For projects/components FUB tests
  %(prog)s coverage.dat --level fub        # For macro/top level tests
  %(prog)s coverage.dat --include-all      # No exclusions
        """
    )
    parser.add_argument('coverage_dat', help='Path to coverage.dat file')
    parser.add_argument('--level', choices=['common', 'amba', 'fub'],
                        default='common', help='Exclusion level (default: common)')
    parser.add_argument('--include-all', action='store_true',
                        help='Include all modules (no exclusions)')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Show per-file breakdown')
    parser.add_argument('--show-excluded', action='store_true',
                        help='List excluded files')
    args = parser.parse_args()
    
    # Annotate coverage data
    with tempfile.TemporaryDirectory() as annotate_dir:
        cmd = ['verilator_coverage', '--annotate', annotate_dir, args.coverage_dat]
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode != 0:
            print(f"Error running verilator_coverage: {result.stderr}", file=sys.stderr)
            sys.exit(1)
        
        # Get exclusion patterns
        if args.include_all:
            exclude_patterns = []
            level_desc = "none (all included)"
        else:
            exclude_patterns = get_exclusions_for_level(args.level)
            level_desc = f"level={args.level} ({len(exclude_patterns)} patterns)"
        
        # Calculate coverage
        coverage = calculate_coverage(annotate_dir, exclude_patterns)
        
        print(f"Coverage Report")
        print(f"Exclusions: {level_desc}")
        print("=" * 60)
        print(f"Total lines:    {coverage['total_lines']}")
        print(f"Covered lines:  {coverage['covered_lines']}")
        print(f"Excluded lines: {coverage['excluded_lines']} ({len(coverage['excluded_files'])} files)")
        print(f"Coverage:       {coverage['percentage']:.1f}%")
        
        if args.show_excluded and coverage['excluded_files']:
            print(f"\nExcluded files ({len(coverage['excluded_files'])}):")
            for f in sorted(coverage['excluded_files']):
                print(f"  {f}")
        
        if args.verbose and coverage['by_file']:
            print(f"\nIncluded files ({len(coverage['by_file'])}):")
            print("-" * 60)
            for filename, data in sorted(coverage['by_file'].items(), key=lambda x: x[1]['pct']):
                print(f"  {filename:<45} {data['covered']:>4}/{data['total']:<4} ({data['pct']:.1f}%)")


if __name__ == '__main__':
    main()
