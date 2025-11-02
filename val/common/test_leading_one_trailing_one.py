# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: LeadingOneTrailingOneTB
# Purpose: Leading One Trailing One Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Leading One Trailing One Test with Parameterized Test Levels and Configuration

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
    TEST_WIDTH: Data width
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
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class LeadingOneTrailingOneTB(TBBase):
    """Testbench for Leading One Trailing One module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.INDEX_WIDTH = math.ceil(math.log2(self.WIDTH)) if self.WIDTH > 1 else 1
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Leading One Trailing One TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}, INDEX_WIDTH={self.INDEX_WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.data = self.dut.data
        self.leadingone = self.dut.leadingone
        self.leadingone_vector = self.dut.leadingone_vector
        self.trailingone = self.dut.trailingone
        self.trailingone_vector = self.dut.trailingone_vector
        self.all_zeroes = self.dut.all_zeroes
        self.all_ones = self.dut.all_ones
        self.valid = self.dut.valid

    def _find_leading_one(self, data):
        """Find the position of the leading (most significant) one bit"""
        if data == 0:
            return None
        
        for i in range(self.WIDTH - 1, -1, -1):
            if (data >> i) & 1:
                return i
        return None

    def _find_trailing_one(self, data):
        """Find the position of the trailing (least significant) one bit"""
        if data == 0:
            return None
        
        for i in range(self.WIDTH):
            if (data >> i) & 1:
                return i
        return None

    def _calculate_expected_outputs(self, data):
        """Calculate all expected outputs for given input data"""
        data = data & self.MAX_DATA
        
        leading_pos = self._find_leading_one(data)
        trailing_pos = self._find_trailing_one(data)
        
        # Create expected results
        expected = {
            'leadingone': leading_pos if leading_pos is not None else 0,
            'leadingone_vector': (1 << leading_pos) if leading_pos is not None else 0,
            'trailingone': trailing_pos if trailing_pos is not None else 0,
            'trailingone_vector': (1 << trailing_pos) if trailing_pos is not None else 0,
            'all_zeroes': 1 if data == 0 else 0,
            'all_ones': 1 if data == self.MAX_DATA else 0,
            'valid': 1 if data != 0 else 0
        }
        
        return expected

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
                0xF0F0F0F0 & self.MAX_DATA,  # Alternating nibbles
                0xFF00FF00 & self.MAX_DATA,  # Alternating bytes
            ])

        # Remove duplicates and filter valid values
        test_patterns = sorted(list(set([v & self.MAX_DATA for v in test_patterns])))

        all_passed = True

        for data in test_patterns:
            expected = self._calculate_expected_outputs(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            # Read outputs
            actual = {
                'leadingone': int(self.leadingone.value),
                'leadingone_vector': int(self.leadingone_vector.value),
                'trailingone': int(self.trailingone.value),
                'trailingone_vector': int(self.trailingone_vector.value),
                'all_zeroes': int(self.all_zeroes.value),
                'all_ones': int(self.all_ones.value),
                'valid': int(self.valid.value)
            }
            
            # Check all outputs
            success = True
            for signal_name in expected:
                if actual[signal_name] != expected[signal_name]:
                    success = False
                    break
            
            if success:
                self.log.debug(f"PASS: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
            else:
                self.log.error(f"FAIL: data=0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")
                await self._dump_debug_info(data, expected, actual)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_patterns',
                'data': data,
                'expected': expected,
                'actual': actual,
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
            expected = self._calculate_expected_outputs(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            # Read outputs
            actual = {
                'leadingone': int(self.leadingone.value),
                'leadingone_vector': int(self.leadingone_vector.value),
                'trailingone': int(self.trailingone.value),
                'trailingone_vector': int(self.trailingone_vector.value),
                'all_zeroes': int(self.all_zeroes.value),
                'all_ones': int(self.all_ones.value),
                'valid': int(self.valid.value)
            }
            
            # Check all outputs
            success = True
            for signal_name in expected:
                if actual[signal_name] != expected[signal_name]:
                    success = False
                    break
            
            if success:
                self.log.debug(f"Random {test_num}: PASS data=0x{data:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"Random {test_num}: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                await self._dump_debug_info(data, expected, actual)
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            # Store result (sample for large tests)
            if test_num % max(1, num_tests // 20) == 0:
                result = {
                    'test_type': 'random_patterns',
                    'test_num': test_num,
                    'data': data,
                    'expected': expected,
                    'actual': actual,
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
            expected = self._calculate_expected_outputs(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            # Read outputs
            actual = {
                'leadingone': int(self.leadingone.value),
                'leadingone_vector': int(self.leadingone_vector.value),
                'trailingone': int(self.trailingone.value),
                'trailingone_vector': int(self.trailingone_vector.value),
                'all_zeroes': int(self.all_zeroes.value),
                'all_ones': int(self.all_ones.value),
                'valid': int(self.valid.value)
            }
            
            # Check all outputs
            success = True
            for signal_name in expected:
                if actual[signal_name] != expected[signal_name]:
                    success = False
                    break
            
            if not success:
                self.log.error(f"Exhaustive: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                await self._dump_debug_info(data, expected, actual)
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
                    'expected': expected,
                    'actual': actual,
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
            (0, "All zeros"),
            (self.MAX_DATA, "All ones"),
            (1, "LSB only"),
            (1 << (self.WIDTH - 1), "MSB only"),
        ]

        # Add more boundary cases for larger widths
        if self.WIDTH > 8:
            boundary_cases.extend([
                (0x80000001 & self.MAX_DATA, "MSB and LSB"),
                (3, "Two LSBs"),
                (3 << (self.WIDTH - 2), "Two MSBs"),
                ((1 << (self.WIDTH // 2)) - 1, "Lower half ones"),
                (self.MAX_DATA ^ ((1 << (self.WIDTH // 2)) - 1), "Upper half ones"),
            ])

        for data, description in boundary_cases:
            data = data & self.MAX_DATA
            expected = self._calculate_expected_outputs(data)
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            # Read outputs
            actual = {
                'leadingone': int(self.leadingone.value),
                'leadingone_vector': int(self.leadingone_vector.value),
                'trailingone': int(self.trailingone.value),
                'trailingone_vector': int(self.trailingone_vector.value),
                'all_zeroes': int(self.all_zeroes.value),
                'all_ones': int(self.all_ones.value),
                'valid': int(self.valid.value)
            }
            
            # Check all outputs
            success = True
            for signal_name in expected:
                if actual[signal_name] != expected[signal_name]:
                    success = False
                    break
            
            if success:
                self.log.debug(f"Boundary {description}: PASS data=0x{data:0{(self.WIDTH+3)//4}x}")
            else:
                self.log.error(f"Boundary {description}: FAIL data=0x{data:0{(self.WIDTH+3)//4}x}")
                await self._dump_debug_info(data, expected, actual)
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'description': description,
                'data': data,
                'expected': expected,
                'actual': actual,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_consistency_checks(self):
        """Test internal consistency of outputs"""
        if self.TEST_LEVEL != 'full':
            self.log.info("Skipping consistency check tests")
            return True

        self.log.info("Testing output consistency")

        all_passed = True

        # Test various patterns for consistency
        test_values = [0, 1, self.MAX_DATA] + [random.randint(0, self.MAX_DATA) for _ in range(20)]

        for data in test_values:
            data = data & self.MAX_DATA
            
            # Drive input
            self.data.value = data
            await Timer(1, units='ns')  # Combinational delay
            
            # Read outputs
            leadingone_idx = int(self.leadingone.value)
            leadingone_vec = int(self.leadingone_vector.value)
            trailingone_idx = int(self.trailingone.value)
            trailingone_vec = int(self.trailingone_vector.value)
            all_zeroes = int(self.all_zeroes.value)
            all_ones = int(self.all_ones.value)
            valid = int(self.valid.value)

            # Consistency checks
            consistency_ok = True
            
            # Check 1: valid should be 1 iff data is non-zero
            if (valid == 1) != (data != 0):
                self.log.error(f"Consistency FAIL: valid={valid} but data=0x{data:x}")
                consistency_ok = False
            
            # Check 2: all_zeroes should be 1 iff data is zero
            if (all_zeroes == 1) != (data == 0):
                self.log.error(f"Consistency FAIL: all_zeroes={all_zeroes} but data=0x{data:x}")
                consistency_ok = False
            
            # Check 3: all_ones should be 1 iff data is all ones
            if (all_ones == 1) != (data == self.MAX_DATA):
                self.log.error(f"Consistency FAIL: all_ones={all_ones} but data=0x{data:x} (max=0x{self.MAX_DATA:x})")
                consistency_ok = False
            
            # Check 4: If valid, vector outputs should match index outputs
            if valid == 1:
                expected_leading_vec = 1 << leadingone_idx if leadingone_idx < self.WIDTH else 0
                expected_trailing_vec = 1 << trailingone_idx if trailingone_idx < self.WIDTH else 0
                
                if leadingone_vec != expected_leading_vec:
                    self.log.error(f"Consistency FAIL: leadingone_vec=0x{leadingone_vec:x}, expected=0x{expected_leading_vec:x} from idx={leadingone_idx}")
                    consistency_ok = False
                    
                if trailingone_vec != expected_trailing_vec:
                    self.log.error(f"Consistency FAIL: trailingone_vec=0x{trailingone_vec:x}, expected=0x{expected_trailing_vec:x} from idx={trailingone_idx}")
                    consistency_ok = False
            
            # Check 5: If valid, the indicated bit positions should actually be set in data
            if valid == 1:
                if leadingone_idx < self.WIDTH and not ((data >> leadingone_idx) & 1):
                    self.log.error(f"Consistency FAIL: leadingone_idx={leadingone_idx} but bit not set in data=0x{data:x}")
                    consistency_ok = False
                    
                if trailingone_idx < self.WIDTH and not ((data >> trailingone_idx) & 1):
                    self.log.error(f"Consistency FAIL: trailingone_idx={trailingone_idx} but bit not set in data=0x{data:x}")
                    consistency_ok = False

            if not consistency_ok:
                all_passed = False

            # Store result (sample)
            if data in [0, 1, self.MAX_DATA] or random.random() < 0.1:
                result = {
                    'test_type': 'consistency_checks',
                    'data': data,
                    'consistency_ok': consistency_ok,
                    'success': consistency_ok
                }
                self.test_results.append(result)
                if not consistency_ok:
                    self.test_failures.append(result)

        return all_passed

    async def _dump_debug_info(self, data, expected, actual):
        """Dump debug information for failures"""
        self.log.error("="*80)
        self.log.error("LEADING/TRAILING ONE FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input data: 0x{data:0{(self.WIDTH+3)//4}x} ({data:0{self.WIDTH}b})")

        # Show bit positions
        bit_positions = []
        for i in range(self.WIDTH):
            if (data >> i) & 1:
                bit_positions.append(i)
        
        if bit_positions:
            self.log.error(f"Set bit positions: {bit_positions}")
            self.log.error(f"Leading one should be at position: {max(bit_positions)}")
            self.log.error(f"Trailing one should be at position: {min(bit_positions)}")
        else:
            self.log.error("No bits set (all zeros)")

        # Compare outputs
        self.log.error("Output comparison:")
        for signal_name in expected:
            exp_val = expected[signal_name]
            act_val = actual[signal_name]
            match = "✓" if exp_val == act_val else "✗"
            self.log.error(f"  {signal_name:20s}: expected={exp_val:8x}, actual={act_val:8x} {match}")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running LEADING_ONE_TRAILING_ONE tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_patterns, "Basic patterns"),
            (self.test_random_patterns, "Random patterns"),
            (self.test_exhaustive_small_widths, "Exhaustive small widths"),
            (self.test_boundary_conditions, "Boundary conditions"),
            (self.test_consistency_checks, "Consistency checks")
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
        self.log.info(f"Overall LEADING_ONE_TRAILING_ONE result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=15000, timeout_unit="us")
async def leading_one_trailing_one_test(dut):
    """Test for Leading One Trailing One module"""
    tb = LeadingOneTrailingOneTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"LEADING_ONE_TRAILING_ONE test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Leading One Trailing One test FAILED - {len(tb.test_failures)} failures detected"

    return passed


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.
    """
    widths = [8, 16, 32, 64]  # Different data widths
    test_levels = ['full']  # Test levels

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    # For debugging, uncomment one of these:
    # return [(8, 'full')]  # Single test
    # return [(16, 'medium')]  # Just specific configurations

    return valid_params


params = generate_params()


@pytest.mark.parametrize("width, test_level", params)
def test_leading_one_trailing_one(request, width, test_level):
    """
    Parameterized Leading One Trailing One test with configurable width and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "leading_one_trailing_one"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/leading_one_trailing_one.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(width, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_leading_one_trailing_one_w{w_str}_{test_level}_{reg_level}"

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
        'INSTANCE_NAME': '"LOTO_TEST"'
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, width / 32.0)  # Larger widths may take more time
    base_timeout = 3000  # 3 seconds base
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