# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterBinTB
# Purpose: Binary Counter Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary Counter Test with Parameterized Test Levels and Configuration

This test uses WIDTH and MAX as parameters for maximum flexibility:

TEST LEVELS (per-test depth):
    basic (30s-2min):  Quick verification during development
    medium (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 2 tests (~5 min) - smoke test (small + large counter)
    FUNC: 9 tests (~20 min) - functional coverage - DEFAULT
    FULL: 27 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 2 configs (small + large) × 1 level = 2 tests
    FUNC: 3 widths × 3 max_vals × 1 level = 9 tests (basic level only)
    FULL: 3 widths × 3 max_vals × 3 levels = 27 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: basic|medium|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility

COUNTER_BIN BEHAVIOR:
    Binary counter with special wrap behavior:
    - Counts 0→1→2→...→(MAX-1), then wraps to {~MSB, 0...0}
    - For WIDTH=5, MAX=10: counts 0→1→...→9, then wraps to 16 (10000b)
    - Next cycle: 17, 18, ..., 25, then wraps to 0 (00000b)
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class CounterBinTB(TBBase):
    """Testbench for Binary Counter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '5'))
        self.MAX = self.convert_to_int(os.environ.get('TEST_MAX', '10'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}{self.get_time_ns_str()}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Counter Bin TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX={self.MAX}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

        # Calculate expected sequence
        self._calculate_expected_sequence()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_bin = self.dut.counter_bin_curr  # Updated to match new RTL port name
        self.counter_bin_next = self.dut.counter_bin_next

    def _calculate_expected_sequence(self):
        """Calculate the expected counting sequence"""
        self.expected_sequence = []

        # First sequence: 0 to MAX-1
        for i in range(self.MAX):
            self.expected_sequence.append(i)

        # Second sequence: toggle MSB and count 0 to MAX-1 again
        msb_mask = 1 << (self.WIDTH - 1)
        for i in range(self.MAX):
            self.expected_sequence.append(i | msb_mask)

        self.log.info(f"Expected sequence length: {len(self.expected_sequence)}{self.get_time_ns_str()}")
        if self.DEBUG:
            self.log.debug(f"Expected sequence: {[hex(x) for x in self.expected_sequence[:20]]}{self.get_time_ns_str()}")

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')
        self.log.debug(f"Clock setup complete{self.get_time_ns_str()}")

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f"Starting reset sequence{self.get_time_ns_str()}")
        self.enable.value = 0
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)
        # Wait a bit more for reset to properly settle
        await Timer(100, units='ps')
        self.log.debug(f"Reset sequence complete{self.get_time_ns_str()}")

    async def check_counter_value(self, expected_value, cycle_num):
        """Check if counter has expected value"""
        actual_value = int(self.counter_bin.value)
        if actual_value != expected_value:
            self.log.error(f"Cycle {cycle_num}: Expected 0x{expected_value:X}, got 0x{actual_value:X}{self.get_time_ns_str()}")
            return False
        else:
            if self.DEBUG or cycle_num % 10 == 0:
                self.log.debug(f"Cycle {cycle_num}: Correct value 0x{actual_value:X}{self.get_time_ns_str()}")
            return True

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'basic':
            num_cycles = min(20, len(self.expected_sequence))  # Test first 20 cycles
        elif self.TEST_LEVEL == 'medium':
            num_cycles = min(len(self.expected_sequence), 100)  # Test up to full sequence
        else:  # full
            num_cycles = len(self.expected_sequence) * 2  # Test two complete sequences

        all_passed = True
        self.enable.value = 1

        for cycle in range(num_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % len(self.expected_sequence)]

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle,
                'expected_value': expected_value,
                'actual_value': int(self.counter_bin.value),
                'success': int(self.counter_bin.value) == expected_value
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

            # Progress reporting
            if cycle % 50 == 0:
                self.mark_progress(f"Basic counting cycle {cycle}")

        self.log.info(f"Basic counting test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_enable_disable(self):
        """Test enable/disable functionality"""
        self.log.info(f"Testing enable/disable functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Count a few cycles
        for i in range(5):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Disable and check counter stops
        self.enable.value = 0
        await self.wait_time(100)
        stored_value = int(self.counter_bin.value)
        self.log.debug(f"Disabled counter at value 0x{stored_value:X}{self.get_time_ns_str()}")

        for i in range(10):
            await RisingEdge(self.clk)
            await self.wait_time(100)
            current_value = int(self.counter_bin.value)
            if current_value != stored_value:
                self.log.error(f"Counter changed while disabled: 0x{stored_value:X} -> 0x{current_value:X}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Re-enable and check counting resumes
        self.enable.value = 1
        await RisingEdge(self.clk)
        self.log.debug(f"Re-enabled counter{self.get_time_ns_str()}")
        self.log.debug(f'{self.expected_sequence=}')
        self.log.debug(f'{stored_value=}')

        for i in range(5):
            await RisingEdge(self.clk)  
            expected_idx = (stored_value + 1 + i) % len(self.expected_sequence)
            expected_value = self.expected_sequence[expected_idx]
            if not await self.check_counter_value(expected_value, stored_value + 1 + i):
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'enable_disable',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Enable/disable test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Count partway through sequence
        partial_count = min(self.MAX // 2, 10)

        for i in range(partial_count):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Apply reset
        self.log.debug(f"Applying reset during counting{self.get_time_ns_str()}")
        await self.wait_time(100)
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await self.wait_time(100)
        self.rst_n.value = 1
        # await RisingEdge(self.clk)
        # await self.wait_time(400)

        # Check counter is reset to 0
        if int(self.counter_bin.value) != 0:
            self.log.error(f"Counter not reset to 0: got 0x{int(self.counter_bin.value):X}{self.get_time_ns_str()}")
            all_passed = False

        # Verify counting resumes from 0
        for i in range(min(10, len(self.expected_sequence))):
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break
            await RisingEdge(self.clk)
            await self.wait_time(100)

        await self.wait_clocks('clk', 5)

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Reset behavior test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_wrap_behavior(self):
        """Test wrap-around behavior"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping wrap behavior test for basic level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing wrap behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Test full sequence including wrap
        test_cycles = len(self.expected_sequence) + 5  # A bit beyond full cycle

        for cycle in range(test_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % len(self.expected_sequence)]

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                if cycle < self.MAX * 2:  # Only break early in first two sequences
                    break

            # Mark important transitions
            if cycle == self.MAX - 1:
                self.log.info(f"About to wrap from first sequence{self.get_time_ns_str()}")
            elif cycle == self.MAX:
                self.log.info(f"Wrapped to second sequence{self.get_time_ns_str()}")
            elif cycle == len(self.expected_sequence) - 1:
                self.log.info(f"About to wrap to beginning{self.get_time_ns_str()}")
            elif cycle == len(self.expected_sequence):
                self.log.info(f"Wrapped back to beginning{self.get_time_ns_str()}")

            # Progress reporting
            if cycle % 25 == 0:
                self.mark_progress(f"Wrap test cycle {cycle}")

        # Store result
        result = {
            'test_type': 'wrap_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Wrap behavior test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_edge_cases(self):
        """Test edge cases and boundary conditions"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping edge case tests for {self.TEST_LEVEL} level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()

        all_passed = True

        # Test multiple rapid resets
        for reset_test in range(3):
            self.log.debug(f"Rapid reset test {reset_test + 1}{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Count a few cycles
            for i in range(min(5, self.MAX)):
                await RisingEdge(self.clk)
                expected_value = self.expected_sequence[i]
                if not await self.check_counter_value(expected_value, i):
                    self.log.error(f"Rapid reset test {reset_test + 1} failed{self.get_time_ns_str()}")
                    all_passed = False
                    break

            if not all_passed:
                break

        # Test reset at wrap boundary
        if all_passed:
            self.log.debug(f"Testing reset at wrap boundary{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Count to just before wrap
            for i in range(self.MAX - 1):
                await RisingEdge(self.clk)

            # Reset during the cycle that should wrap
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Should be back at 0
            if int(self.counter_bin.value) != 0:
                self.log.error(f"Reset at wrap failed: expected 0, got 0x{int(self.counter_bin.value):X}{self.get_time_ns_str()}")
                all_passed = False

        # Store result
        result = {
            'test_type': 'edge_cases',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Edge cases test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running COUNTER_BIN tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_enable_disable, "Enable/disable"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_wrap_behavior, "Wrap behavior"),
            (self.test_edge_cases, "Edge cases")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}{self.get_time_ns_str()}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}{self.get_time_ns_str()}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info(f"TEST RESULTS SUMMARY{self.get_time_ns_str()}")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall COUNTER_BIN result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_bin_test(dut):
    """Test for Binary Counter module"""
    tb = CounterBinTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER_BIN test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter bin test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed

def generate_params():
    """
    Generate counter_bin parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke test - small + large)
    REG_LEVEL=FUNC: 9 tests (functional coverage) - default
    REG_LEVEL=FULL: 27 tests (comprehensive validation)

    Parameters: (width, max_val, test_level)

    Counter constraint: MAX must fit in WIDTH-1 bits (MSB is special)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove basic functionality
        # 2 tests: small counter + large counter, basic level only
        params = [
            (5, 10, 'basic'),   # Small counter (5 bits, max 10)
            (8, 128, 'basic'),  # Larger counter (8 bits, max 128)
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - test variety of widths/maxs with basic level
        # 3 widths × 3 maxs × 1 level = 9 tests
        widths = [4, 5, 8]
        maxs = [8, 10, 16]
        test_levels = ['basic']  # Keep tests fast for functional check

        params = []
        for width, max_val in product(widths, maxs):
            # Ensure MAX fits in WIDTH-1 bits (since MSB is special)
            if max_val < (1 << (width - 1)):
                for level in test_levels:
                    params.append((width, max_val, level))

    else:  # FULL
        # Comprehensive testing - multiple widths, maxs, and all test levels
        # 3 widths × 3 maxs × 3 levels = 27 tests
        widths = [4, 5, 8]
        maxs = [8, 10, 16]
        test_levels = ['basic', 'medium', 'full']

        params = []
        for width, max_val, level in product(widths, maxs, test_levels):
            # Ensure MAX fits in WIDTH-1 bits
            if max_val < (1 << (width - 1)):
                params.append((width, max_val, level))

    return params

params = generate_params()

@pytest.mark.parametrize("width, max_val, test_level", params)
def test_counter_bin(request, width, max_val, test_level):
    """
    Parameterized Binary Counter test with configurable width, max value and test level.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)

    Counter behavior: Binary counter with special wrap (toggle MSB, clear others)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_bin"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_bin.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_counter_bin_w{width}_max{max_val}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width),
        'MAX': str(max_val)
    }

    # Adjust timeout based on test level and max value
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    max_factor = max(1.0, max_val / 100.0)  # Larger max values take more time
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_WIDTH': str(width),
        'TEST_MAX': str(max_val),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}, max={max_val}")
    print(f"Expected sequence length: {max_val * 2}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: width={width}, max={max_val}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
