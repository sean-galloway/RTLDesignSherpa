# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: coverage_mixin
# Purpose: Mixin class to add coverage support to any testbench
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream/dv/coverage
#
# Author: sean galloway
# Created: 2025-01-10

"""
Coverage Mixin for STREAM Testbenches

Provides easy integration of coverage collection into any testbench class.
Use as a mixin or standalone helper.

Usage:
    class MyTB(TBBase, CoverageMixin):
        def __init__(self, dut):
            TBBase.__init__(self, dut)
            CoverageMixin.__init__(self)

        async def run_test(self):
            # Sample coverage during test
            self.coverage_sample_axi_read(1, 2, 7)  # INCR, 4-byte, 8 beats

        def cleanup(self):
            self.coverage_save()

Or use as helper:
    class MyTB(TBBase):
        def __init__(self, dut):
            super().__init__(dut)
            self.coverage = CoverageHelper("my_test")
"""

import os
import logging
from typing import Optional

from .coverage_collector import CoverageCollector
from .protocol_coverage import ProtocolCoverage
from .coverage_config import CoverageConfig, LegalCoverageConfig


class CoverageHelper:
    """
    Standalone coverage helper that can be used in any testbench.

    Example:
        self.coverage = CoverageHelper("test_scheduler_basic")

        # During test
        self.coverage.sample_axi_read(burst_type=1, size=2, length=7)
        self.coverage.sample_scenario("concurrent_rw")

        # At end of test
        self.coverage.save()

    Legal Coverage Mode:
        Set COVERAGE_LEGAL=1 to measure against STREAM-specific legal points only.
        This gives realistic coverage numbers instead of measuring against the
        full AXI4 protocol space that STREAM doesn't fully implement.

        COVERAGE=1 COVERAGE_LEGAL=1 pytest test_scheduler.py -v
    """

    def __init__(self, test_name: str, log: Optional[logging.Logger] = None,
                 legal_config: str = None):
        """
        Initialize coverage helper.

        Args:
            test_name: Unique name for this test
            log: Optional logger (will use coverage logger if not provided)
            legal_config: Name of legal config to load (e.g., 'stream')
                         Or set COVERAGE_LEGAL=1 env var to auto-load 'stream'
        """
        self.test_name = test_name
        self.enabled = os.environ.get('COVERAGE', '0') == '1'
        self.log = log or logging.getLogger(f"coverage.{test_name}")

        # Load legal coverage config if requested
        self.legal_config = None
        if legal_config:
            self.legal_config = LegalCoverageConfig.load(legal_config)
        elif os.environ.get('COVERAGE_LEGAL', '0') == '1':
            self.legal_config = LegalCoverageConfig.load('stream')

        if self.enabled:
            self.collector = CoverageCollector.get_instance(
                test_name, log=self.log, legal_config=self.legal_config
            )
            self.protocol = self.collector.protocol

            # Auto-set sim_build from environment if available
            sim_build = os.environ.get('COVERAGE_SIM_BUILD')
            if sim_build:
                self.collector.set_sim_build_dir(sim_build)
                self.log.info(f"Coverage enabled for test: {test_name} (sim_build: {sim_build})")
            else:
                self.log.info(f"Coverage enabled for test: {test_name} (no sim_build)")

            if self.legal_config:
                self.log.info(f"Legal coverage mode: {self.legal_config.count_legal_points()} legal points")
        else:
            self.collector = None
            self.protocol = None

    def set_sim_build(self, sim_build: str):
        """Set simulation build directory for Verilator coverage collection."""
        if self.collector:
            self.collector.set_sim_build_dir(sim_build)

    # =========================================================================
    # AXI sampling methods
    # =========================================================================

    def sample_axi_read(self, burst_type: int, burst_size: int, burst_len: int,
                        address: int = 0, response: int = 0, interface: str = None):
        """Sample an AXI read transaction for coverage.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (2^size bytes per beat)
            burst_len: AXI burst length (0=1 beat, 255=256 beats)
            address: Transaction address (for alignment coverage)
            response: AXI response (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            interface: Optional interface name ('desc', 'axi_mem', 'network')
        """
        if self.protocol:
            self.protocol.sample_axi_read(burst_type, burst_size, burst_len, address, response, interface)

    def sample_axi_write(self, burst_type: int, burst_size: int, burst_len: int,
                         address: int = 0, response: int = 0, interface: str = None):
        """Sample an AXI write transaction for coverage.

        Args:
            burst_type: AXI burst type (0=FIXED, 1=INCR, 2=WRAP)
            burst_size: AXI burst size (2^size bytes per beat)
            burst_len: AXI burst length (0=1 beat, 255=256 beats)
            address: Transaction address (for alignment coverage)
            response: AXI response (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
            interface: Optional interface name ('desc', 'axi_mem', 'network')
        """
        if self.protocol:
            self.protocol.sample_axi_write(burst_type, burst_size, burst_len, address, response, interface)

    def sample_handshake(self, handshake_name: str):
        """Sample a valid/ready handshake event.

        Args:
            handshake_name: Name of the handshake interface (e.g., 'desc_valid_ready')
        """
        if self.protocol:
            self.protocol.sample_handshake(handshake_name)

    # =========================================================================
    # APB sampling methods
    # =========================================================================

    def sample_apb_read(self, is_error: bool = False):
        """Sample an APB read transaction."""
        if self.protocol:
            self.protocol.sample_apb(is_write=False, is_error=is_error)

    def sample_apb_write(self, is_error: bool = False):
        """Sample an APB write transaction."""
        if self.protocol:
            self.protocol.sample_apb(is_write=True, is_error=is_error)

    # =========================================================================
    # Functional coverage methods
    # =========================================================================

    def sample_scenario(self, scenario_name: str):
        """Sample a functional scenario."""
        if self.protocol:
            self.protocol.sample_scenario(scenario_name)

    def sample_fsm_state(self, state_name: str):
        """Sample an FSM state transition."""
        if self.protocol:
            # Use scenarios group for FSM states
            self.protocol.scenarios.sample(f"fsm_{state_name}")

    # =========================================================================
    # Report and save methods
    # =========================================================================

    def save(self):
        """Save coverage data at end of test."""
        if self.collector:
            self.collector.save()
            self.log.info(f"Coverage saved: {self.test_name}")
            self.log.info(f"  Protocol coverage: {self.protocol.overall_coverage_pct:.1f}%")

    def report(self, detailed: bool = False) -> str:
        """Generate coverage report string."""
        if self.collector:
            return self.collector.report(detailed=detailed)
        return "Coverage not enabled"

    @property
    def protocol_coverage_pct(self) -> float:
        """Get overall protocol coverage percentage."""
        if self.protocol:
            return self.protocol.overall_coverage_pct
        return 0.0


class CoverageMixin:
    """
    Mixin class to add coverage support to testbench classes.

    Usage:
        class SchedulerTB(TBBase, CoverageMixin):
            def __init__(self, dut):
                TBBase.__init__(self, dut)
                CoverageMixin.__init__(self, "test_scheduler")
    """

    def __init__(self, test_name: Optional[str] = None, **kwargs):
        """
        Initialize coverage mixin.

        Args:
            test_name: Test name for coverage (defaults to class name)
        """
        # Get test name from environment or use default
        if test_name is None:
            test_name = os.environ.get('COVERAGE_TEST_NAME', self.__class__.__name__)

        # Get log from parent class if available
        log = getattr(self, 'log', None)

        # Create coverage helper
        self._coverage_helper = CoverageHelper(test_name, log=log)

    @property
    def coverage(self) -> CoverageHelper:
        """Access the coverage helper."""
        return self._coverage_helper

    def coverage_sample_axi_read(self, burst_type: int, burst_size: int, burst_len: int,
                                  address: int = 0, response: int = 0):
        """Sample an AXI read transaction for coverage."""
        self._coverage_helper.sample_axi_read(burst_type, burst_size, burst_len, address, response)

    def coverage_sample_axi_write(self, burst_type: int, burst_size: int, burst_len: int,
                                   address: int = 0, response: int = 0):
        """Sample an AXI write transaction for coverage."""
        self._coverage_helper.sample_axi_write(burst_type, burst_size, burst_len, address, response)

    def coverage_sample_apb_read(self, is_error: bool = False):
        """Sample an APB read transaction."""
        self._coverage_helper.sample_apb_read(is_error)

    def coverage_sample_apb_write(self, is_error: bool = False):
        """Sample an APB write transaction."""
        self._coverage_helper.sample_apb_write(is_error)

    def coverage_sample_scenario(self, scenario_name: str):
        """Sample a functional scenario."""
        self._coverage_helper.sample_scenario(scenario_name)

    def coverage_save(self):
        """Save coverage data."""
        self._coverage_helper.save()


def get_coverage_compile_args() -> list:
    """
    Get Verilator compile arguments for coverage collection.

    Use in pytest wrapper:
        extra_args = get_coverage_compile_args()
        run(..., compile_args=extra_args + [...], ...)
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return []

    return [
        '--coverage',
        '--coverage-line',
        '--coverage-toggle',
        '--coverage-underscore',
    ]


def get_coverage_env(test_name: str, sim_build: str = None) -> dict:
    """
    Get environment variables for coverage collection.

    Use in pytest wrapper:
        extra_env = get_coverage_env("test_scheduler_basic", sim_build=sim_build)
        run(..., extra_env={**extra_env, ...}, ...)

    Args:
        test_name: Unique test name for coverage file naming
        sim_build: Path to simulation build directory (for Verilator line coverage)
    """
    if os.environ.get('COVERAGE', '0') != '1':
        return {}

    # Determine test type (fub or top) from sim_build path if available
    test_type = 'fub'  # default
    if sim_build:
        sim_build_abs = os.path.abspath(sim_build)
        if '/tests/top/' in sim_build_abs or '/tests/top' in sim_build_abs:
            test_type = 'top'
        elif '/tests/macro/' in sim_build_abs or '/tests/macro' in sim_build_abs:
            test_type = 'macro'

    # Compute the absolute path to coverage output directory
    # This ensures the cocotb subprocess knows exactly where to save data
    # Walk up from current file to find stream component root
    current = os.path.dirname(os.path.abspath(__file__))
    coverage_output_dir = None
    while current != '/':
        if os.path.exists(os.path.join(current, 'dv', 'tests', test_type)):
            coverage_output_dir = os.path.join(current, 'dv', 'tests', test_type, 'coverage_data', 'per_test')
            break
        current = os.path.dirname(current)

    if not coverage_output_dir:
        # Fallback: use current working directory
        coverage_output_dir = os.path.join(os.getcwd(), 'coverage_data', 'per_test')

    # Ensure directory exists
    os.makedirs(coverage_output_dir, exist_ok=True)

    env = {
        'COVERAGE': '1',  # Pass through to cocotb subprocess
        'COVERAGE_ENABLE': '1',
        'COVERAGE_TEST_NAME': test_name,
        'COVERAGE_OUTPUT_DIR': coverage_output_dir,
    }

    # Pass sim_build path for Verilator line coverage collection
    if sim_build:
        env['COVERAGE_SIM_BUILD'] = os.path.abspath(sim_build)

    return env


def register_bfm_coverage(bfms: list, coverage_helper: 'CoverageHelper') -> None:
    """
    Register coverage hooks on GAXI BFMs for automatic transaction sampling.

    This connects the GAXI BFM coverage hook infrastructure to the stream
    coverage collector, enabling automatic protocol coverage when transactions
    complete on any registered BFM.

    Args:
        bfms: List of GAXI BFMs (GAXIMaster, GAXISlave, GAXIMonitor instances)
        coverage_helper: CoverageHelper instance to receive samples

    Example:
        coverage = CoverageHelper("test_scheduler_basic")

        # Register all BFMs for automatic coverage
        register_bfm_coverage(
            [axi_master, axi_slave, desc_master, network_slave],
            coverage
        )

        # Now run test - coverage is sampled automatically!
        await tb.run_test()

        coverage.save()
    """
    if not coverage_helper.enabled:
        return

    try:
        from CocoTBFramework.components.gaxi.coverage_hooks import register_coverage_hooks
        register_coverage_hooks(bfms, coverage_helper, log=coverage_helper.log)
        coverage_helper.log.info(f"Registered coverage hooks on {len(bfms)} BFMs")
    except ImportError as e:
        coverage_helper.log.warning(f"Could not import coverage hooks: {e}")
    except Exception as e:
        coverage_helper.log.warning(f"Failed to register BFM coverage hooks: {e}")
