# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: EncoderTB
# Purpose: Generic Encoder Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Encoder Test with Parameterized Test Levels and Configuration

This test uses input_width and test_level as parameters for maximum flexibility:

CONFIGURATION:
    input_width: Number of input bits (4, 8, 16, 32)
    output_width: Number of output bits (log2(input_width))

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - input_width: [4, 8, 16, 32]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_INPUT_WIDTH: Input width for encoder

Note: The encoder has a bug in the original code - 'out' should be 'data'
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

class EncoderTB(TBBase):
    """Testbench for Generic Encoder module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.INPUT_WIDTH = self.convert_to_int(os.environ.get('TEST_INPUT_WIDTH', '8'))
        self.OUTPUT_WIDTH = int(math.log2(self.INPUT_WIDTH))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Maximum values
        self.MAX_INPUT = (1 << self.INPUT_WIDTH) - 1
        self.MAX_OUTPUT = (1 << self.OUTPUT_WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Validate input width (must be power of 2)
        if not (self.INPUT_WIDTH & (self.INPUT_WIDTH - 1)) == 0:
            self.log.warning(f"Input width {self.INPUT_WIDTH} is not a power of 2")

        # Log configuration
        self.log.info(f"Encoder TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"INPUT_WIDTH={self.INPUT_WIDTH}, OUTPUT_WIDTH={self.OUTPUT_WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.decoded = self.dut.decoded
        self.data = self.dut.data

    def _calculate_expected_output(self, input_val):
        """Calculate expected encoder output (highest priority bit position)"""
        input_val &= self.MAX_INPUT
        
        if input_val == 0:
            return 0  # No bits set
        
        # Find highest priority bit (highest bit position)
        for i in range(self.INPUT_WIDTH - 1, -1, -1):
            if (input_val >> i) & 1:
                return i
        
        return 0

    def _generate_one_hot_values(self):
        """Generate one-hot test values"""
        one_hot_values = []
        for i in range(self.INPUT_WIDTH):
            one_hot_values.append(1 << i)
        return one_hot_values

    def _generate_multi_bit_values(self):
        """Generate values with multiple bits set"""
        multi_bit_values = []
        
        # Two adjacent bits
        for i in range(self.INPUT_WIDTH - 1):
            multi_bit_values.append((1 << i) | (1 << (i + 1)))
        
        # Two non-adjacent bits
        for i in range(0, self.INPUT_WIDTH - 2, 2):
            multi_bit_values.append((1 << i) | (1 << (i + 2)))
        
        # All bits in lower half
        lower_half = (1 << (self.INPUT_WIDTH // 2)) - 1
        if lower_half > 0:
            multi_bit_values.append(lower_half)
        
        # All bits in upper half
        upper_half = ((1 << (self.INPUT_WIDTH // 2)) - 1) << (self.INPUT_WIDTH // 2)
        if upper_half > 0:
            multi_bit_values.append(upper_half)
        
        return multi_bit_values

    async def test_one_hot_encoding(self):
        """Test encoder with one-hot inputs"""
        self.log.info("Testing one-hot encoding")

        one_hot_values = self._generate_one_hot_values()
        
        all_passed = True

        for input_val in one_hot_values:
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.decoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: decoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} → " +
                             f"data=0x{actual_output:x} (bit {actual_output})")
            else:
                self.log.error(f"FAIL: decoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'one_hot_encoding',
                'input': input_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_priority_encoding(self):
        """Test encoder with multiple bits set (priority encoding)"""
        self.log.info("Testing priority encoding")

        # Define test data based on level
        if self.TEST_LEVEL == 'basic':
            test_values = self._generate_multi_bit_values()[:8]  # Limited set
        elif self.TEST_LEVEL == 'medium':
            test_values = self._generate_multi_bit_values()
            # Add some random multi-bit values
            for _ in range(16):
                val = random.randint(1, self.MAX_INPUT)
                # Ensure at least 2 bits are set
                if bin(val).count('1') >= 2:
                    test_values.append(val)
        else:  # full
            test_values = self._generate_multi_bit_values()
            # Add comprehensive random multi-bit values
            for _ in range(64):
                val = random.randint(1, self.MAX_INPUT)
                if bin(val).count('1') >= 2:
                    test_values.append(val)
            # Add systematic patterns
            test_values.append(self.MAX_INPUT)  # All bits set
            test_values.append(self.MAX_INPUT >> 1)  # All but MSB

        # Remove duplicates
        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values if val > 0])))

        all_passed = True

        for input_val in test_values:
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.decoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                bit_count = bin(input_val).count('1')
                self.log.debug(f"PASS: decoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                             f"({bit_count} bits) → data={actual_output} (highest bit)")
            else:
                self.log.error(f"FAIL: decoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'priority_encoding',
                'input': input_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_zero_input(self):
        """Test encoder with zero input"""
        self.log.info("Testing zero input")

        input_val = 0
        expected_output = 0  # Should output 0 when no bits are set

        # Drive input
        self.decoded.value = input_val
        await cocotb.triggers.Timer(1, units='ns')

        actual_output = int(self.data.value) & self.MAX_OUTPUT

        success = (actual_output == expected_output)

        if success:
            self.log.debug(f"PASS: decoded=0x{input_val:x} → data={actual_output}")
        else:
            self.log.error(f"FAIL: decoded=0x{input_val:x}, expected={expected_output}, actual={actual_output}")

        # Store result
        result = {
            'test_type': 'zero_input',
            'input': input_val,
            'expected_output': expected_output,
            'actual_output': actual_output,
            'success': success
        }
        self.test_results.append(result)
        if not success:
            self.test_failures.append(result)

        return success

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests for basic level")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test boundary values
        boundary_values = [
            1,  # Only LSB
            1 << (self.INPUT_WIDTH - 1),  # Only MSB
            self.MAX_INPUT,  # All bits set
            self.MAX_INPUT >> 1,  # All but MSB
            (1 << (self.INPUT_WIDTH - 1)) | 1,  # MSB and LSB
        ]

        for input_val in boundary_values:
            if input_val == 0:
                continue  # Already tested in zero_input
                
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.decoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Boundary test FAIL: decoded=0x{input_val:x}, " +
                             f"expected={expected_output}, actual={actual_output}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                break

        return all_passed

    async def test_walking_patterns(self):
        """Test walking bit patterns"""
        if self.TEST_LEVEL != 'full':
            self.log.info("Skipping walking patterns test")
            return True

        self.log.info("Testing walking bit patterns")

        all_passed = True

        # Walking ones pattern
        for i in range(self.INPUT_WIDTH):
            input_val = 1 << i
            expected_output = i

            # Drive input
            self.decoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Walking ones FAIL: bit {i}, decoded=0x{input_val:x}, " +
                             f"expected={expected_output}, actual={actual_output}")
                all_passed = False
                break

        # Walking zeros pattern (all bits set except one)
        if all_passed:
            for i in range(self.INPUT_WIDTH):
                input_val = self.MAX_INPUT ^ (1 << i)  # All bits except bit i
                expected_output = self.INPUT_WIDTH - 1  # Highest bit position
                
                # Find the actual highest bit
                for j in range(self.INPUT_WIDTH - 1, -1, -1):
                    if (input_val >> j) & 1:
                        expected_output = j
                        break

                # Drive input
                self.decoded.value = input_val
                await cocotb.triggers.Timer(1, units='ns')

                actual_output = int(self.data.value) & self.MAX_OUTPUT

                success = (actual_output == expected_output)

                if not success:
                    self.log.error(f"Walking zeros FAIL: cleared bit {i}, decoded=0x{input_val:x}, " +
                                 f"expected={expected_output}, actual={actual_output}")
                    all_passed = False
                    break

        return all_passed

    async def _dump_debug_info(self, input_val, expected_output, actual_output):
        """Dump debug information for failures"""
        self.log.error("="*80)
        self.log.error("ENCODER FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input (decoded): 0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                      f"({input_val:0{self.INPUT_WIDTH}b})")
        self.log.error(f"Expected output: {expected_output}")
        self.log.error(f"Actual output:   {actual_output}")

        # Show bit analysis
        bits_set = []
        for i in range(self.INPUT_WIDTH):
            if (input_val >> i) & 1:
                bits_set.append(i)

        self.log.error(f"Input bits set: {bits_set}")
        self.log.error(f"Highest bit: {max(bits_set) if bits_set else 'none'}")
        self.log.error(f"Input bit count: {len(bits_set)}")

        if bits_set:
            expected_highest = max(bits_set)
            self.log.error(f"Expected highest bit position: {expected_highest}")
            if actual_output != expected_highest:
                self.log.error(f"Priority error: got bit {actual_output}, should be bit {expected_highest}")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running ENCODER tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_zero_input, "Zero input"),
            (self.test_one_hot_encoding, "One-hot encoding"),
            (self.test_priority_encoding, "Priority encoding"),
            (self.test_boundary_conditions, "Boundary conditions"),
            (self.test_walking_patterns, "Walking patterns")
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
        self.log.info(f"Overall ENCODER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def encoder_test(dut):
    """Test for Generic Encoder module"""
    tb = EncoderTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"ENCODER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Encoder test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Minimal - just 4-bit
        input_widths = [4]
        test_levels = ['full']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        input_widths = [4, 8]
        test_levels = ['full']
    else:  # FULL
        # FULL: All widths
        input_widths = [4, 8, 16, 32]
        test_levels = ['full']

    return [(width, level) for width, level in product(input_widths, test_levels)]

params = generate_params()

@pytest.mark.parametrize("input_width, test_level", params)
def test_encoder(request, input_width, test_level):
    """
    Parameterized Generic Encoder test with configurable input width and test level.

    Input width controls the size of the encoder:
    - 4: 4-to-2 encoder
    - 8: 8-to-3 encoder
    - 16: 16-to-4 encoder
    - 32: 32-to-5 encoder

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "encoder"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/encoder.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    output_width = int(math.log2(input_width))
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_encoder_{input_width}to{output_width}_{test_level}_{reg_level}"

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
        'N': str(input_width)
    }

    # Adjust timeout based on test level and input width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, input_width / 16.0)  # Larger inputs take more time
    base_timeout = 1000  # 1 second base
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
        'TEST_INPUT_WIDTH': str(input_width),
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
    print(f"Running {test_level.upper()} test: {input_width}-to-{output_width} encoder")
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
        print(f"✓ {test_level.upper()} test PASSED: {input_width}-to-{output_width} encoder")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
