# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DecoderTB
# Purpose: Generic Decoder Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Decoder Test with Parameterized Test Levels and Configuration

This test uses input_width and test_level as parameters for maximum flexibility:

CONFIGURATION:
    input_width: Number of input bits (2, 3, 4, 5, 6)
    output_width: Number of output bits (2^input_width)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - input_width: [2, 3, 4, 5, 6]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_INPUT_WIDTH: Input width for decoder
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
from conftest import get_coverage_compile_args

class DecoderTB(TBBase):
    """Testbench for Generic Decoder module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.INPUT_WIDTH = self.convert_to_int(os.environ.get('TEST_INPUT_WIDTH', '4'))
        self.OUTPUT_WIDTH = 2 ** self.INPUT_WIDTH
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

        # Log configuration
        self.log.info(f"Decoder TB initialized")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"INPUT_WIDTH={self.INPUT_WIDTH}, OUTPUT_WIDTH={self.OUTPUT_WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

    def _setup_signals(self):
        """Setup signal mappings"""
        self.encoded = self.dut.encoded
        self.data = self.dut.data

    def _calculate_expected_output(self, input_val):
        """Calculate expected decoder output (one-hot encoding)"""
        input_val &= self.MAX_INPUT
        expected = 1 << input_val
        return expected & self.MAX_OUTPUT

    async def test_basic_decoding(self):
        """Test basic decoder functionality"""
        self.log.info("Testing basic decoder functionality")

        # Define test data based on level
        if self.TEST_LEVEL == 'basic':
            # Test all possible inputs for basic level (should be fast for small widths)
            test_values = list(range(min(self.OUTPUT_WIDTH, 16)))
        elif self.TEST_LEVEL == 'medium':
            # Test all inputs for medium widths, sample for large widths
            if self.INPUT_WIDTH <= 4:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                # Test corners and some random values
                test_values = [0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT]
                test_values.extend([random.randint(0, self.MAX_INPUT) for _ in range(16)])
        else:  # full
            # Test all inputs for reasonable widths, comprehensive sampling for large widths
            if self.INPUT_WIDTH <= 5:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                # Test systematic patterns
                test_values = [0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT]
                # Test walking bit patterns
                for bit_pos in range(self.INPUT_WIDTH):
                    test_values.append(1 << bit_pos)
                    test_values.append(self.MAX_INPUT ^ (1 << bit_pos))
                # Add random values
                test_values.extend([random.randint(0, self.MAX_INPUT) for _ in range(32)])

        # Remove duplicates and sort
        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values])))

        all_passed = True

        for input_val in test_values:
            input_val &= self.MAX_INPUT
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')  # Combinational delay

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if success:
                self.log.debug(f"PASS: encoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} → " +
                             f"data=0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x}")
            else:
                self.log.error(f"FAIL: encoded=0x{input_val:0{(self.INPUT_WIDTH+3)//4}x}, " +
                             f"expected=0x{expected_output:0{(self.OUTPUT_WIDTH+3)//4}x}, " +
                             f"actual=0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_decoding',
                'input': input_val,
                'expected_output': expected_output,
                'actual_output': actual_output,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_one_hot_property(self):
        """Test that output is always one-hot (exactly one bit set)"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping one-hot property test for basic level")
            return True

        self.log.info("Testing one-hot property")

        # Test data based on level
        if self.TEST_LEVEL == 'medium':
            test_values = [random.randint(0, self.MAX_INPUT) for _ in range(16)]
            test_values.extend([0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT])
        else:  # full
            if self.INPUT_WIDTH <= 5:
                test_values = list(range(self.OUTPUT_WIDTH))
            else:
                test_values = [random.randint(0, self.MAX_INPUT) for _ in range(64)]
                test_values.extend([0, 1, self.MAX_INPUT >> 1, self.MAX_INPUT])

        test_values = sorted(list(set([val & self.MAX_INPUT for val in test_values])))

        all_passed = True

        for input_val in test_values:
            input_val &= self.MAX_INPUT

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            # Count number of bits set
            bits_set = bin(actual_output).count('1')
            is_one_hot = (bits_set == 1)

            success = is_one_hot

            if success:
                self.log.debug(f"PASS: encoded=0x{input_val:x} → one-hot output (bits_set={bits_set})")
            else:
                self.log.error(f"FAIL: encoded=0x{input_val:x}, output=0x{actual_output:x}, " +
                             f"bits_set={bits_set} (should be 1)")
                all_passed = False
                if self.TEST_LEVEL == 'medium':
                    break

            # Store result
            result = {
                'test_type': 'one_hot_property',
                'input': input_val,
                'output': actual_output,
                'bits_set': bits_set,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions and edge cases"""
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping boundary condition tests for basic level")
            return True

        self.log.info("Testing boundary conditions")

        all_passed = True

        # Test minimum and maximum values
        boundary_values = [0, self.MAX_INPUT]

        # Test power-of-2 values
        for i in range(self.INPUT_WIDTH):
            boundary_values.append(1 << i)
            boundary_values.append(self.MAX_INPUT ^ (1 << i))  # All bits except one

        boundary_values = sorted(list(set([val & self.MAX_INPUT for val in boundary_values])))

        for input_val in boundary_values:
            expected_output = self._calculate_expected_output(input_val)

            # Drive input
            self.encoded.value = input_val
            await cocotb.triggers.Timer(1, units='ns')

            actual_output = int(self.data.value) & self.MAX_OUTPUT

            success = (actual_output == expected_output)

            if not success:
                self.log.error(f"Boundary test FAIL: encoded=0x{input_val:x}, " +
                             f"expected=0x{expected_output:x}, actual=0x{actual_output:x}")
                await self._dump_debug_info(input_val, expected_output, actual_output)
                all_passed = False
                break

            # Verify one-hot property
            bits_set = bin(actual_output).count('1')
            if bits_set != 1:
                self.log.error(f"Boundary one-hot FAIL: encoded=0x{input_val:x}, " +
                             f"output=0x{actual_output:x}, bits_set={bits_set}")
                all_passed = False
                break

        return all_passed

    async def _dump_debug_info(self, input_val, expected_output, actual_output):
        """Dump debug information for failures"""
        self.log.error("="*80)
        self.log.error("DECODER FAILURE ANALYSIS")
        self.log.error("="*80)

        self.log.error(f"Input (encoded): 0x{input_val:0{(self.INPUT_WIDTH+3)//4}x} " +
                      f"({input_val:0{self.INPUT_WIDTH}b}) = {input_val}")
        self.log.error(f"Expected output: 0x{expected_output:0{(self.OUTPUT_WIDTH+3)//4}x} " +
                      f"({expected_output:0{self.OUTPUT_WIDTH}b})")
        self.log.error(f"Actual output:   0x{actual_output:0{(self.OUTPUT_WIDTH+3)//4}x} " +
                      f"({actual_output:0{self.OUTPUT_WIDTH}b})")

        # Show which bit should be set
        expected_bit_pos = input_val
        actual_bit_positions = [i for i in range(self.OUTPUT_WIDTH) if (actual_output >> i) & 1]

        self.log.error(f"Expected bit position: {expected_bit_pos}")
        self.log.error(f"Actual bit positions: {actual_bit_positions}")

        # Check if it's a simple shift error
        if len(actual_bit_positions) == 1:
            actual_pos = actual_bit_positions[0]
            shift_error = actual_pos - expected_bit_pos
            self.log.error(f"Bit position error: {shift_error} (actual - expected)")

        self.log.error("="*80)

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running DECODER tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_basic_decoding, "Basic decoding"),
            (self.test_one_hot_property, "One-hot property"),
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
        self.log.info(f"Overall DECODER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def decoder_test(dut):
    """Test for Generic Decoder module"""
    tb = DecoderTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"DECODER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Decoder test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Minimal - just 2-bit
        input_widths = [2]
        test_levels = ['full']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        input_widths = [2, 3, 4]
        test_levels = ['full']
    else:  # FULL
        # FULL: All widths
        input_widths = [2, 3, 4, 5, 6]
        test_levels = ['full']

    return [(width, level) for width, level in product(input_widths, test_levels)]

params = generate_params()

@pytest.mark.parametrize("input_width, test_level", params)
def test_decoder(request, input_width, test_level):
    """
    Parameterized Generic Decoder test with configurable input width and test level.

    Input width controls the size of the decoder:
    - 2: 2-to-4 decoder
    - 3: 3-to-8 decoder
    - 4: 4-to-16 decoder
    - etc.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "decoder"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/decoder.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    output_width = 2 ** input_width
    w_str = TBBase.format_dec(input_width, 1)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_decoder_{input_width}to{output_width}_{test_level}_{reg_level}"

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
        'M': str(input_width),
        'N': str(output_width)
    }

    # Adjust timeout based on test level and input width
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    width_factor = max(1.0, output_width / 16.0)  # Larger outputs take more time
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
    print(f"Running {test_level.upper()} test: {input_width}-to-{output_width} decoder")
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
        print(f"✓ {test_level.upper()} test PASSED: {input_width}-to-{output_width} decoder")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
