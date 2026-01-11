# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: verilator_coverage
# Purpose: Verilator coverage data parsing utilities
#
# Author: sean galloway
# Created: 2025-01-10

"""
Verilator Coverage Parsing Utilities

Provides functions to parse Verilator's coverage.dat files and merge
coverage data across multiple tests.

Verilator SystemC::Coverage-3 format:
    C 'f<filename>l<line>n<col>page<type>/<hierarchy>' <count>

Coverage types:
    - v_line / pagev_line: Line coverage (executable statements)
    - v_toggle / pagev_toggle: Toggle coverage (signal bit transitions)
    - v_branch / pagev_branch: Branch coverage (if/else decisions)

Note: Comments and declarations are never counted in coverage.
      Verilator only instruments executable code.
"""

import os
import re
import glob
import subprocess
import tempfile
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional


@dataclass
class CoverageStats:
    """Coverage statistics from Verilator."""
    line_covered: int = 0
    line_total: int = 0
    toggle_covered: int = 0
    toggle_total: int = 0
    branch_covered: int = 0
    branch_total: int = 0

    @property
    def line_pct(self) -> float:
        return (self.line_covered / self.line_total * 100) if self.line_total > 0 else 0.0

    @property
    def toggle_pct(self) -> float:
        return (self.toggle_covered / self.toggle_total * 100) if self.toggle_total > 0 else 0.0

    @property
    def branch_pct(self) -> float:
        return (self.branch_covered / self.branch_total * 100) if self.branch_total > 0 else 0.0

    def to_dict(self) -> Dict:
        return {
            'line': {'covered': self.line_covered, 'total': self.line_total, 'pct': self.line_pct},
            'toggle': {'covered': self.toggle_covered, 'total': self.toggle_total, 'pct': self.toggle_pct},
            'branch': {'covered': self.branch_covered, 'total': self.branch_total, 'pct': self.branch_pct},
        }


def parse_verilator_coverage_file(filepath: str) -> CoverageStats:
    """Parse a single Verilator coverage.dat file.

    Args:
        filepath: Path to coverage.dat file

    Returns:
        CoverageStats with line/toggle/branch coverage counts
    """
    stats = CoverageStats()

    if not os.path.exists(filepath):
        return stats

    # Skip non-coverage files
    if 'verFiles.dat' in filepath:
        return stats

    try:
        with open(filepath, 'r') as f:
            for line in f:
                # Skip header and comments
                if line.startswith('#') or not line.strip():
                    continue

                # Verilator SystemC coverage format
                # Format: C '<metadata>' <count>
                if line.startswith('C '):
                    # Split on last space to get count
                    parts = line.rsplit(' ', 1)
                    if len(parts) != 2:
                        continue

                    try:
                        count = int(parts[1].strip())
                    except ValueError:
                        continue

                    metadata = parts[0]

                    # Determine coverage type from metadata
                    if 'v_toggle' in metadata or 'pagev_toggle' in metadata:
                        stats.toggle_total += 1
                        if count > 0:
                            stats.toggle_covered += 1
                    elif 'v_line' in metadata or 'pagev_line' in metadata:
                        stats.line_total += 1
                        if count > 0:
                            stats.line_covered += 1
                    elif 'v_branch' in metadata or 'pagev_branch' in metadata:
                        stats.branch_total += 1
                        if count > 0:
                            stats.branch_covered += 1

    except Exception as e:
        print(f"Warning: Failed to parse coverage file {filepath}: {e}")

    return stats


def parse_coverage_stats(coverage_files: List[str]) -> Dict[str, CoverageStats]:
    """Parse multiple Verilator coverage files.

    Args:
        coverage_files: List of paths to coverage.dat files

    Returns:
        Dict mapping test_name -> CoverageStats
    """
    result = {}

    for filepath in coverage_files:
        # Skip non-coverage files
        if 'verFiles.dat' in filepath:
            continue

        # Extract test name from path
        test_dir = os.path.dirname(filepath)
        test_name = os.path.basename(test_dir)

        stats = parse_verilator_coverage_file(filepath)
        result[test_name] = stats

    return result


def get_merged_verilator_coverage(coverage_files: List[str]) -> Tuple[float, int, int]:
    """Use verilator_coverage tool to properly merge coverage data.

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
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

        if result.returncode != 0:
            print(f"Warning: verilator_coverage merge failed: {result.stderr}")
            return (0.0, 0, 0)

        # Create temp dir for annotation
        with tempfile.TemporaryDirectory() as annotate_dir:
            # Run verilator_coverage --annotate to get coverage percentage
            cmd = ['verilator_coverage', '--annotate', annotate_dir, merged_dat]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

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


def find_coverage_files(base_dir: str, pattern: str = "coverage.dat") -> List[str]:
    """Find all coverage.dat files in a directory tree.

    Args:
        base_dir: Root directory to search
        pattern: Filename pattern to match (default: coverage.dat)

    Returns:
        List of paths to coverage files
    """
    files = []

    # Look in sim_build directories
    sim_build_dir = os.path.join(base_dir, 'local_sim_build')
    if os.path.exists(sim_build_dir):
        for test_dir in glob.glob(os.path.join(sim_build_dir, 'test_*')):
            coverage_dat = os.path.join(test_dir, pattern)
            if os.path.exists(coverage_dat):
                files.append(coverage_dat)

    # Also look in per_test directory
    per_test_dir = os.path.join(base_dir, 'coverage_data', 'per_test')
    if os.path.exists(per_test_dir):
        files.extend(glob.glob(os.path.join(per_test_dir, '*.dat')))

    return files


def get_per_file_coverage(merged_dat: str) -> Dict[str, Dict[str, any]]:
    """Get coverage breakdown per source file.

    Uses verilator_coverage --annotate to get per-file coverage details.

    Args:
        merged_dat: Path to merged coverage.dat file

    Returns:
        Dict mapping filename to coverage stats:
        {
            'scheduler.sv': {'line': (covered, total, pct), 'toggle': (...), 'branch': (...)},
            ...
        }
    """
    result = {}

    if not os.path.exists(merged_dat):
        return result

    try:
        with tempfile.TemporaryDirectory() as annotate_dir:
            cmd = ['verilator_coverage', '--annotate', annotate_dir, merged_dat]
            subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            # Parse annotated files
            for annotated_file in glob.glob(os.path.join(annotate_dir, '*.v')):
                filename = os.path.basename(annotated_file)
                # Remove .v suffix added by verilator_coverage
                if filename.endswith('.v'):
                    original_name = filename[:-2]
                else:
                    original_name = filename

                line_covered = 0
                line_total = 0
                toggle_covered = 0
                toggle_total = 0
                branch_covered = 0
                branch_total = 0

                with open(annotated_file, 'r') as f:
                    for line in f:
                        # Verilator annotate format: %nnnnnn  | code
                        # Where nnnnnn is hit count (spaces for 0)
                        if line.startswith('%'):
                            count_str = line[1:7].strip()
                            if count_str:
                                try:
                                    count = int(count_str)
                                    line_total += 1
                                    if count > 0:
                                        line_covered += 1
                                except ValueError:
                                    pass
                            else:
                                # Zero hits (spaces)
                                line_total += 1

                if line_total > 0:
                    result[original_name] = {
                        'line': {
                            'covered': line_covered,
                            'total': line_total,
                            'pct': (line_covered / line_total * 100)
                        }
                    }

    except Exception as e:
        print(f"Warning: Failed to get per-file coverage: {e}")

    return result
