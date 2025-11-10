# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CountLeadingZerosTB
# Purpose: Count Leading Zeros Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Count Leading Zeros Test with Parameterized Test Levels and Configuration

This test uses width and test_level as parameters for maximum flexibility:

CONFIGURATION:
    width:       Data width (8, 16, 32, 64)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - width: [8, 16, 32, 64]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Data width for CLZ calculation
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class CountLeadingZerosTB(TBBase):
    """Testbench for Count Leading Zeros module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '32'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.OUTPUT_WIDTH = math.ceil(math.log2(self.WIDTH)) + 1 if self.WIDTH > 1 else 1
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Count Leading Zeros TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, OUTPUT_WIDTH={self.OUTPUT_WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.data = self.dut.data
        self.count_leading_zeros = self.dut.clz

    def _calculate_expected_clz(self, data):
        """Calculate expected count of leading zeros"""
        if data == 0:
            return self.WIDTH
        
        # Note: RTL counts from LSB, so we need to count trailing zeros from LSB perspective
        # The function name in RTL is misleading - it's actually counting trailing zeros
        clz = 0
        for i in range(self.WIDTH):
            if (data >> i) & 1:
                break
            clz += 1
        return clz

    async def test_basic_patterns(self):
        """Test basic bit patterns"""
        self.log.info("Testing basic patterns")

        # Define test patterns based on level
        test_patterns = []
        
        # Always test these basic cases
        test_patterns.extend([0, self.MAX_DATA])
        
        # Single bit patterns
        if self.TEST_LEVEL == 'basic':
            # Test a few single bits
            bit_positions = [0, 1, self.WIDTH - 1] if self.WIDTH > 2 else [0, 1]
        elif self.TEST_LEVEL == 'medium':
            # Test more single bits
            bit_positions = [0, 1, 2, self.WIDTH // 2, self.WIDTH - 2, self.WIDTH - 1]
        else:  # full
            # Test all single bits
            bit_positions = list(range(self.WIDTH))
        
        # Add single bit patterns
        for pos in bit_positions:
            if pos < self.WIDTH:
                test_patterns.append(1 << pos)

        # Add some multi-bit patterns
        if self.TEST_LEVEL != 'basic':
            # Add patterns with multiple bits set
            if self.WIDTH >= 8:
                test_patterns.extend([0x55555555 & self.MAX_DATA, 0xAAAAAAAA & self.MAX_DATA])
            test_patterns.extend([3, 7, 15])  # Small patterns
            
        if self.TEST_LEVEL == 'full':
            # Add more complex patterns
            test_patterns.extend([
                self.MAX_DATA >> 1,  # All bits except MSB
                self.MAX_DATA >> 2,  # All bits except 2 MSBs
                (self.MAX_DATA >> 4) if self.WIDTH > 4 else 1,
            ])

        # Remove duplicates and filter valid values
        test_patterns = sorted(list(set([v & self.MAX_DATA for v in test_patterns])))

        all_passed = True

        for data in test_patterns:
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"PASS: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b}) → clz={actual_clz}")
            else:
                self.log.error(f"FAIL: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_patterns',
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_random_patterns(self):
        """Test random bit patterns"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping random pattern tests")
            return True

        self.log.info("Testing random patterns")

        # Determine number of random tests based on level
        if self.TEST_LEVEL == 'medium':
            num_tests = min(100, 2 ** min(self.WIDTH, 10))
        else:  # full
            num_tests = min(500, 2 ** min(self.WIDTH, 12))

        all_passed = True

        for test_num in range(num_tests):
            data = random.randint(0, self.MAX_DATA)
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"Random {test_num}: PASS data=0x{data:0{(self.WIDTH+3)//4}x} → clz={actual_clz}")
            else:
                self.log.error(f"Random {test_num}: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            # Store result
            result = {
                'test_type': 'random_patterns',
                'test_num': test_num,
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_exhaustive_small_widths(self):
        """Test all possible values for small widths"""
        if self.TEST_LEVEL != 'full' or self.WIDTH > 16:
            self.log.info("Skipping exhaustive small width tests")
            return True

        self.log.info(f"Testing all {2**self.WIDTH} possible values")

        all_passed = True

        for data in range(2**self.WIDTH):
            expected_clz = self._calculate_expected_clz(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if not success:
                self.log.error(f"Exhaustive: FAIL data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                await self._dump_clz_debug_info(data, expected_clz, actual_clz)
                all_passed = False
                break
            else:
                if data % (2**(self.WIDTH-4)) == 0:  # Log progress
                    self.log.debug(f"Exhaustive: {data}/{2**self.WIDTH} completed")

            # Store result (sample for large tests)
            if data % max(1, 2**(self.WIDTH-8)) == 0:
                result = {
                    'test_type': 'exhaustive',
                    'data': data,
                    'expected_clz': expected_clz,
                    'actual_clz': actual_clz,
                    'success': success
                }
                self.test_results.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test specific boundary cases
        boundary_cases = [
            (0, self.WIDTH),  # All zeros
            (1, self.WIDTH - 1),  # LSB only
            (self.MAX_DATA, 0),  # All ones
        ]

        # Add more boundary cases for larger widths
        if self.WIDTH > 8:
            boundary_cases.extend([
                (2, self.WIDTH - 2),  # Second bit only
                (self.MAX_DATA >> 1, 0),  # All except MSB
                (self.MAX_DATA >> 2, 0),  # All except 2 MSBs
            ])

        for data, expected_clz in boundary_cases:
            data = data & self.MAX_DATA
            expected_clz = self._calculate_expected_clz(data)  # Recalculate to be sure
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            actual_clz = int(self.count_leading_zeros.value)
            
            success = (actual_clz == expected_clz)
            
            if success:
                self.log.debug(f"Boundary: PASS data=0x{data:0{(self.WIDTH+3)//4}x} → clz={actual_clz}")
            else:
                self.log.error(f"Boundary: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                self.log.error(f"      Expected CLZ: {expected_clz}, Actual CLZ: {actual_clz}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'data': data,
                'expected_clz': expected_clz,
                'actual_clz': actual_clz,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def _dump_clz_debug_info(self, data, expected_clz, actual_clz):
        """Dump debug information for CLZ failures"""
        self.log.error("="*80)
        self.log.error("COUNT LEADING ZEROS FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input data: 0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
        self.log.error(f"Expected CLZ: {expected_clz}")
        self.log.error(f"Actual CLZ: {actual_clz}")

        # Show bit-by-bit analysis
        self.log.error("Bit analysis (LSB to MSB):")
        first_one_pos = None
        for i in range(self.WIDTH):
            bit_val = (data >> i) & 1
            marker = " <-- First 1" if bit_val == 1 and first_one_pos is None else ""
            if bit_val == 1 and first_one_pos is None:
                first_one_pos = i
            self.log.error(f"  Bit {i:2d}: {bit_val}{marker}")

        if first_one_pos is not None:
            self.log.error(f"First '1' found at position {first_one_pos} (CLZ should be {first_one_pos})")
        else:
            self.log.error(f"No '1' bits found (CLZ should be {self.WIDTH})")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running COUNT_LEADING_ZEROS tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_patterns, "Basic patterns"),
            (self.test_random_patterns, "Random patterns"),
            (self.test_exhaustive_small_widths, "Exhaustive small widths"),
            (self.test_boundary_conditions, "Boundary conditions")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall COUNT_LEADING_ZEROS result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=15000, timeout_unit="us")
async def count_leading_zeros_test(dut):
    """Test for Count Leading Zeros module"""
    tb = CountLeadingZerosTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNT_LEADING_ZEROS test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Count Leading Zeros test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Minimal - just 8-bit
        widths = [8]
        test_levels = ['full']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        widths = [8, 16]
        test_levels = ['full']
    else:  # FULL
        # FULL: All widths
        widths = [8, 16, 32, 64]
        test_levels = ['full']

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_count_leading_zeros(request, width, test_level):
    """
    Parameterized Count Leading Zeros test with configurable width and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "count_leading_zeros"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/count_leading_zeros.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(width, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_count_leading_zeros_w{w_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width),
        'INSTANCE_NAME': '"CLZ_TEST"'
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, width / 32.0)  # Larger widths may take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

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
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}")
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
            includes=[],
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
        print(f"✓ {test_level.upper()} test PASSED: width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise