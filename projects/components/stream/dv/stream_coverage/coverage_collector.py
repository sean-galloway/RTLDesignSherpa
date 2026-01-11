# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: coverage_collector
# Purpose: Main coverage collector for STREAM component
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream/dv/coverage
#
# Author: sean galloway
# Created: 2025-01-10

"""
Coverage Collector for STREAM Component

Integrates:
1. Verilator code coverage (line, toggle, branch)
2. Protocol coverage (AXI/APB transactions)
3. Functional coverage (FSM states, scenarios)

Usage in testbench:
    from projects.components.stream.dv.stream_coverage import CoverageCollector

    class MyTB(TBBase):
        def __init__(self, dut):
            super().__init__(dut)
            self.coverage = CoverageCollector.get_instance("my_test")

        async def run_test(self):
            # Sample protocol coverage
            self.coverage.protocol.sample_axi_read(burst_type=1, burst_size=2, burst_len=7)

            # Sample functional scenarios
            self.coverage.protocol.sample_scenario("concurrent_rw")

        def cleanup(self):
            # Save coverage at end of test
            self.coverage.save()
"""

import os
import json
import logging
import subprocess
import glob
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field

from .protocol_coverage import ProtocolCoverage
from .coverage_config import CoverageConfig


@dataclass
class CodeCoverageStats:
    """Statistics from Verilator code coverage."""
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


class CoverageCollector:
    """
    Main coverage collector for STREAM component.

    Manages both code coverage (via Verilator) and protocol coverage.
    Provides singleton-like access per test for easy integration.

    Supports "legal coverage" mode where coverage is measured against
    only the legal variations that STREAM supports (from YAML config).
    """

    # Class-level registry of collectors per test
    _instances: Dict[str, 'CoverageCollector'] = {}

    def __init__(self, test_name: str, config: Optional[CoverageConfig] = None,
                 log: Optional[logging.Logger] = None,
                 legal_config: Optional['LegalCoverageConfig'] = None):
        """
        Initialize coverage collector.

        Args:
            test_name: Unique name for this test (used for file naming)
            config: Coverage configuration
            log: Logger instance
            legal_config: Optional legal coverage config for STREAM-specific coverage
        """
        self.test_name = test_name
        self.config = config or CoverageConfig.from_environment()
        self.log = log or logging.getLogger(f"coverage.{test_name}")
        self.legal_config = legal_config

        # Protocol coverage collector
        self.protocol = ProtocolCoverage(
            name=f"{test_name}_protocol",
            log=self.log,
            legal_config=legal_config
        )

        # Code coverage stats (populated after simulation)
        self.code_coverage = CodeCoverageStats()

        # Paths - prioritize COVERAGE_OUTPUT_DIR if set (from pytest wrapper)
        explicit_output_dir = os.environ.get('COVERAGE_OUTPUT_DIR')
        if explicit_output_dir:
            # Use the explicit output directory directly
            self._per_test_dir = explicit_output_dir
            self._coverage_dir = os.path.dirname(explicit_output_dir)
            self._base_dir = os.path.dirname(os.path.dirname(self._coverage_dir))
            self.log.info(f"Using COVERAGE_OUTPUT_DIR: {self._per_test_dir}")
        else:
            # Derive paths from base directory
            self._base_dir = self._get_base_dir()
            self._coverage_dir = os.path.join(self._base_dir, self.config.coverage_dir)
            self._per_test_dir = os.path.join(self._coverage_dir, self.config.per_test_dir)
            self.log.info(f"Derived coverage output dir: {self._per_test_dir}")

        self._sim_build_dir: Optional[str] = None

        # Ensure directories exist
        os.makedirs(self._per_test_dir, exist_ok=True)
        self.log.info(f"Coverage data will be saved to: {self._per_test_dir}")

        # Register instance
        CoverageCollector._instances[test_name] = self

    @classmethod
    def get_instance(cls, test_name: str, config: Optional[CoverageConfig] = None,
                     log: Optional[logging.Logger] = None,
                     legal_config: Optional['LegalCoverageConfig'] = None) -> 'CoverageCollector':
        """Get or create a coverage collector for a test."""
        if test_name in cls._instances:
            return cls._instances[test_name]
        return cls(test_name, config, log, legal_config)

    @classmethod
    def clear_instances(cls):
        """Clear all registered instances (for test cleanup)."""
        cls._instances.clear()

    def _get_base_dir(self) -> str:
        """Get base directory for coverage data.

        Priority:
        1. COVERAGE_OUTPUT_DIR environment variable (set by pytest wrapper)
        2. Walk up from module location to find stream component root
        3. Fallback to tests directory (current working directory)
        """
        # Priority 1: Use explicit output directory if set
        output_dir = os.environ.get('COVERAGE_OUTPUT_DIR')
        if output_dir:
            # COVERAGE_OUTPUT_DIR points directly to per_test dir, return parent
            # e.g., ".../coverage_data/per_test" -> return ".../coverage_data"'s parent
            # Actually we need the component root (contains dv/tests/fub)
            # So walk up from output_dir to find it
            current = os.path.dirname(os.path.abspath(output_dir))
            while current != '/':
                if os.path.exists(os.path.join(current, 'dv', 'tests', 'fub')):
                    self.log.debug(f"Found base dir from COVERAGE_OUTPUT_DIR: {current}")
                    return current
                current = os.path.dirname(current)

        # Priority 2: Walk up from module location to find stream component root
        current = os.path.dirname(os.path.abspath(__file__))
        while current != '/':
            if os.path.exists(os.path.join(current, 'dv', 'tests', 'fub')):
                self.log.debug(f"Found base dir from module location: {current}")
                return current
            current = os.path.dirname(current)

        # Priority 3: Fallback - use current working directory's tests area
        cwd = os.getcwd()
        tests_fub = os.path.join(cwd, 'coverage_data')
        if 'tests' in cwd:
            # We're likely in the tests directory already
            # Go up to find the component root
            current = cwd
            while current != '/':
                if os.path.exists(os.path.join(current, 'dv', 'tests', 'fub')):
                    self.log.debug(f"Found base dir from cwd: {current}")
                    return current
                current = os.path.dirname(current)

        # Last resort: module directory
        self.log.warning(f"Could not find component root, using module directory")
        return os.path.dirname(os.path.abspath(__file__))

    def set_sim_build_dir(self, sim_build: str):
        """Set the simulation build directory (for Verilator coverage files)."""
        self._sim_build_dir = sim_build

    def get_verilator_compile_args(self) -> List[str]:
        """Get Verilator compile arguments for coverage."""
        args = self.config.get_verilator_compile_args()

        # Add coverage output directory
        coverage_dat = os.path.join(self._per_test_dir, f"{self.test_name}_verilator.dat")
        args.extend([
            f'--coverage-underscore',  # Include _ signals
        ])

        return args

    def get_coverage_env(self) -> Dict[str, str]:
        """Get environment variables for coverage collection."""
        return {
            'COVERAGE_ENABLE': '1',
            'COVERAGE_TEST_NAME': self.test_name,
            'COVERAGE_OUTPUT_DIR': self._per_test_dir,
        }

    def collect_verilator_coverage(self):
        """Collect Verilator coverage data after simulation."""
        if not self._sim_build_dir:
            self.log.warning("No sim_build_dir set, cannot collect Verilator coverage")
            return

        # Find coverage.dat files
        coverage_files = glob.glob(os.path.join(self._sim_build_dir, '*.dat'))
        coverage_files.extend(glob.glob(os.path.join(self._sim_build_dir, 'coverage*.dat')))

        if not coverage_files:
            self.log.info("No Verilator coverage files found")
            return

        # Copy coverage files to per-test directory
        for src in coverage_files:
            filename = os.path.basename(src)
            dst = os.path.join(self._per_test_dir, f"{self.test_name}_{filename}")
            try:
                import shutil
                shutil.copy2(src, dst)
                self.log.info(f"Copied coverage file: {src} -> {dst}")
            except Exception as e:
                self.log.error(f"Failed to copy coverage file: {e}")

        # Parse coverage stats
        self._parse_verilator_coverage()

    def _parse_verilator_coverage(self):
        """Parse Verilator coverage data files.

        Verilator SystemC::Coverage-3 format:
        C 'f<filename>l<line>n<col>page<type>/<hierarchy>' <count>

        Example:
        C 'f/path/to/file.svl102n41pagev_toggle/schedulerosched_rd_validh.scheduler' 10

        Where:
        - 'f' prefix: filename
        - 'l' prefix: line number
        - 'n' prefix: column number
        - 'page' prefix: coverage type (v_line, v_toggle, v_branch)
        - Final number: hit count
        """
        coverage_files = glob.glob(os.path.join(self._per_test_dir, f"{self.test_name}_*.dat"))

        # Also check sim_build for coverage.dat directly
        if self._sim_build_dir:
            main_coverage = os.path.join(self._sim_build_dir, 'coverage.dat')
            if os.path.exists(main_coverage) and main_coverage not in coverage_files:
                coverage_files.append(main_coverage)

        for filepath in coverage_files:
            # Skip non-coverage files
            if 'verFiles.dat' in filepath:
                continue

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
                                self.code_coverage.toggle_total += 1
                                if count > 0:
                                    self.code_coverage.toggle_covered += 1
                            elif 'v_line' in metadata or 'pagev_line' in metadata:
                                self.code_coverage.line_total += 1
                                if count > 0:
                                    self.code_coverage.line_covered += 1
                            elif 'v_branch' in metadata or 'pagev_branch' in metadata:
                                self.code_coverage.branch_total += 1
                                if count > 0:
                                    self.code_coverage.branch_covered += 1

            except Exception as e:
                self.log.warning(f"Failed to parse coverage file {filepath}: {e}")

    def save(self):
        """Save all coverage data."""
        # Save protocol coverage
        protocol_path = os.path.join(self._per_test_dir, f"{self.test_name}_protocol.json")
        self.protocol.save_to_file(protocol_path)

        # Collect and save code coverage
        self.collect_verilator_coverage()

        # Save combined summary
        summary_path = os.path.join(self._per_test_dir, f"{self.test_name}_summary.json")
        self._save_summary(summary_path)

        self.log.info(f"Coverage saved for test: {self.test_name}")
        self.log.info(f"  Protocol: {self.protocol.overall_coverage_pct:.1f}%")
        self.log.info(f"  Line:     {self.code_coverage.line_pct:.1f}%")

    def _save_summary(self, filepath: str):
        """Save combined coverage summary."""
        summary = {
            'test_name': self.test_name,
            'protocol_coverage': self.protocol.get_coverage_summary(),
            'code_coverage': self.code_coverage.to_dict(),
            'overall': {
                'protocol_pct': self.protocol.overall_coverage_pct,
                'line_pct': self.code_coverage.line_pct,
                'toggle_pct': self.code_coverage.toggle_pct,
            }
        }

        with open(filepath, 'w') as f:
            json.dump(summary, f, indent=2)

    def report(self, detailed: bool = False) -> str:
        """Generate human-readable coverage report."""
        lines = []
        lines.append("=" * 80)
        lines.append(f"COVERAGE REPORT: {self.test_name}")
        lines.append("=" * 80)
        lines.append("")
        lines.append("CODE COVERAGE (Verilator):")
        lines.append(f"  Line:    {self.code_coverage.line_pct:.1f}% ({self.code_coverage.line_covered}/{self.code_coverage.line_total})")
        lines.append(f"  Toggle:  {self.code_coverage.toggle_pct:.1f}% ({self.code_coverage.toggle_covered}/{self.code_coverage.toggle_total})")
        lines.append("")
        lines.append(self.protocol.report(detailed=detailed))

        return "\n".join(lines)


def get_coverage_compile_args(test_name: str, config: Optional[CoverageConfig] = None) -> List[str]:
    """
    Convenience function to get Verilator compile args for coverage.

    Use in pytest wrapper:
        compile_args = get_coverage_compile_args("test_scheduler_basic")
        run(..., compile_args=compile_args, ...)
    """
    collector = CoverageCollector.get_instance(test_name, config)
    return collector.get_verilator_compile_args()


def get_coverage_env(test_name: str, config: Optional[CoverageConfig] = None) -> Dict[str, str]:
    """
    Convenience function to get environment variables for coverage.

    Use in pytest wrapper:
        extra_env = get_coverage_env("test_scheduler_basic")
        run(..., extra_env=extra_env, ...)
    """
    collector = CoverageCollector.get_instance(test_name, config)
    return collector.get_coverage_env()
