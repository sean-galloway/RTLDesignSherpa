# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AddSubTB
# Purpose: Test for the N-bit adder/subtractor module.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test for the N-bit adder/subtractor module.
"""
import os
import sys
import random
import itertools
import subprocess
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


class AddSubTB(TBBase):
    """Testbench for adder/subtractor modules."""

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '1'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize the random generator
        random.seed(self.seed)

        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with N={self.N}")


    def clear_interface(self):
        """Clear the DUT interface by setting all inputs to 0."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_c.value = 0


    def print_settings(self):
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Add/Sub Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')


    async def main_loop(self, count=256):
        """Main test loop for adder/subtractor.

        Tests all combinations of inputs up to max_val or randomly samples
        if max_val is larger than count.

        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info(f"Starting main test loop with count={count}")

        # Determine if we need to test all possible values or random sampling
        if self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        # Test both addition and subtraction modes
        c_list = [0, 1]  # 0 for addition, 1 for subtraction

        total_tests = len(a_list) * len(b_list) * len(c_list)
        self.log.info(f"Will run {total_tests} total test cases")

        # Test the adder/subtractor
        for test_idx, (a, b, cin) in enumerate(itertools.product(a_list, b_list, c_list)):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            # Apply test inputs
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            self.dut.i_c.value = cin

            # Wait for a simulation time to ensure values propagate
            await self.wait_time(2, 'ns')

            # Check if the operation is addition or subtraction
            if cin == 0:  # Addition
                expected_sum = (a + b) & self.mask
                expected_c = 1 if (a + b) >= self.max_val else 0
            else:  # Subtraction
                expected_sum = (a - b) & self.mask
                expected_c = 0 if a < b else 1  # borrow vs. no borrow

            # Get actual outputs
            actual_sum = int(self.dut.ow_sum.value)
            actual_c = int(self.dut.ow_carry.value)

            msg = f'{a=} {b=} {cin=} {expected_sum=} {actual_sum=}'
            self.log.debug(msg)

            # Verify results
            if (actual_sum != expected_sum) or (actual_c != expected_c):
                self.log.error(f"Test failed for inputs: a={a}, b={b}, cin={cin} (mode={'subtraction' if cin else 'addition'})")
                self.log.error(f"  Expected: sum={expected_sum}, carry/borrow={expected_c}")
                self.log.error(f"  Actual: sum={actual_sum}, carry/borrow={actual_c}")

                # For debugging, also print binary
                self.log.error("  Binary comparison:")
                self.log.error(f"    a      = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    b      = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    mode   = {'subtraction' if cin else 'addition'}")
                self.log.error(f"    exp_sum= {bin(expected_sum)[2:].zfill(self.N)}")
                self.log.error(f"    act_sum= {bin(actual_sum)[2:].zfill(self.N)}")

                self.fail_count += 1
                assert False, f"Add/Sub test failed for inputs a={a}, b={b}, cin={cin}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def addsub_dut_test(dut):
    """Test the adder/subtractor module."""
    tb = AddSubTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Print testbench settings
    tb.print_settings()

    # Clear and initialize interface
    tb.clear_interface()
    await tb.wait_time(2, 'ns')

    # Run the add/sub test
    await tb.main_loop()


def get_width_params():
    """Generate width parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [4]  # GATE: Minimal - just 4-bit
    elif reg_level == 'FUNC':
        return [4, 8]  # FUNC: Small and medium widths
    else:  # FULL
        return [4, 8, 12]  # FULL: All widths


@pytest.mark.parametrize("n", get_width_params())
def test_math_addsub_full_nbit(request, n):
    """PyTest function to run the cocotb test."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "math_addsub_full_nbit"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/math_addsub_full_nbit.f'
    )

    # Define test parameters
    parameters = {'N': n}

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_N{parameters['N']}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Define simulation build and log paths
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Define log path
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Set up environment variables
    seed = random.randint(0, 100000)
    test_level = os.environ.get('TEST_LEVEL', 'basic')  # Can be basic, medium, or full

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': test_level,
        'PARAM_N': str(n)
    }

    # Create command file for viewing waveforms

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

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Launch the simulation

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
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
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure