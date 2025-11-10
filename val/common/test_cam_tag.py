# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CamTagConfig
# Purpose: Configuration class for CAM tag tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.common.cam_testing import CamTB

class CamTagConfig:
    """Configuration class for CAM tag tests"""
    def __init__(self, name, n, depth):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            n: Tag width
            depth: CAM depth
        """
        self.name = name
        self.n = n
        self.depth = depth

class CamTagTB(CamTB):
    """
    Enhanced testbench for the CAM tag module
    Inherits from CamTB but adds additional test sequences
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Log configuration
        self.log.info(f"CAM Tag TB initialized with N={self.N}, DEPTH={self.DEPTH}")
        self.log.info(f"SEED={self.SEED}")

        # Test completion flag
        self.done = False

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.dut.rst_n.value = 0

        # Hold reset for multiple cycles
        await self.wait_clocks('clk', 10)

        # Release reset
        self.dut.rst_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        self.log.debug('Ending reset_dut')

    async def run_basic_test(self):
        """Run basic functionality test of the CAM"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting basic CAM functionality test @ {time_ns}ns")

        # Initial state checks
        self.check_empty()
        self.check_not_full()

        # Test with alternating bit pattern
        tag = self.generate_alternating_ones(self.N)
        tag_invert = self.invert_bits(tag, self.N)

        # Mark one tag valid
        await self.mark_one_valid(tag)
        self.check_not_empty()
        self.check_not_full()

        # Check tag matches
        await self.check_tag(tag, 1)  # Should be true
        await self.check_tag(tag_invert, 0)  # Should be false

        # Try to invalidate a non-existent tag
        await self.mark_one_invalid(tag_invert)  # Should be ignored

        # Verify that valid tag still exists
        await self.check_tag(tag, 1)
        await self.check_tag(tag_invert, 0)

        # Clear the valid tag
        await self.mark_one_invalid(tag)

        # Verify CAM is empty
        self.check_empty()
        self.check_not_full()

        time_ns = get_sim_time('ns')
        self.log.info(f"Basic CAM functionality test completed @ {time_ns}ns")

    async def run_capacity_test(self):
        """Test CAM to full capacity"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting CAM capacity test @ {time_ns}ns")

        # Generate unique tags
        tag_list = self.generate_unique_tags(self.DEPTH)

        # Fill CAM to capacity
        self.log.info(f"Filling CAM with {self.DEPTH} unique tags")
        for i, tag in enumerate(tag_list):
            self.log.debug(f"Adding tag {i}: 0x{tag:x}")
            await self.mark_one_valid(tag)

            # Verify correct status
            if i == self.DEPTH - 1:
                self.check_full()
            else:
                self.check_not_full()
            self.check_not_empty()

            # Verify tag is found
            await self.check_tag(tag, 1)

        # Try to add one more (should fail)
        extra_tag = self.generate_unique_tag(tag_list)
        self.log.info(f"Attempting to add extra tag: 0x{extra_tag:x} to full CAM")
        await self.mark_one_valid(extra_tag)

        # Verify CAM is still full
        self.check_full()

        # Verify extra tag wasn't added
        await self.check_tag(extra_tag, 0)

        # Remove tags and verify
        self.log.info("Removing tags and verifying CAM status")
        for i, tag in enumerate(tag_list):
            self.log.debug(f"Removing tag {i}: 0x{tag:x}")
            await self.mark_one_invalid(tag)

            # Verify correct status
            if i == 0:
                self.check_not_full()
            if i == self.DEPTH - 1:
                self.check_empty()
            else:
                self.check_not_empty()

            # Verify tag is not found
            await self.check_tag(tag, 0)

        time_ns = get_sim_time('ns')
        self.log.info(f"CAM capacity test completed @ {time_ns}ns")

    async def run_concurrent_access_test(self, num_operations=50):
        """Test CAM with concurrent operations"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting CAM concurrent access test with {num_operations} operations @ {time_ns}ns")

        # Track which tags are valid
        valid_tags = set()

        # Run a sequence of random operations
        for i in range(num_operations):
            # Generate operation type (0: add, 1: remove, 2: check)
            op_type = random.randint(0, 2)

            if op_type == 0:  # Add tag
                if len(valid_tags) < self.DEPTH:
                    # Generate a new tag not in valid_tags
                    tag = random.randint(0, (1 << self.N) - 1)
                    while tag in valid_tags:
                        tag = random.randint(0, (1 << self.N) - 1)

                    self.log.debug(f"Op {i}: Adding tag 0x{tag:x}")
                    await self.mark_one_valid(tag)
                    valid_tags.add(tag)
                else:
                    self.log.debug(f"Op {i}: CAM full, skipping add")

            elif op_type == 1 and valid_tags:  # Remove tag
                # Remove a random tag from valid_tags
                tag = random.choice(list(valid_tags))
                self.log.debug(f"Op {i}: Removing tag 0x{tag:x}")
                await self.mark_one_invalid(tag)
                valid_tags.remove(tag)

            elif random.random() < 0.5 and valid_tags:
                # Check a valid tag
                tag = random.choice(list(valid_tags))
                self.log.debug(f"Op {i}: Checking valid tag 0x{tag:x}")
                await self.check_tag(tag, 1)
            else:
                # Generate an invalid tag
                tag = random.randint(0, (1 << self.N) - 1)
                while tag in valid_tags:
                    tag = random.randint(0, (1 << self.N) - 1)

                self.log.debug(f"Op {i}: Checking invalid tag 0x{tag:x}")
                await self.check_tag(tag, 0)

        # Verify final state
        if not valid_tags:
            self.check_empty()
        elif len(valid_tags) == self.DEPTH:
            self.check_full()
        else:
            self.check_not_empty()
            self.check_not_full()

        # Verify each valid tag
        for tag in valid_tags:
            await self.check_tag(tag, 1)

        time_ns = get_sim_time('ns')
        self.log.info(f"CAM concurrent access test completed @ {time_ns}ns")

    def generate_unique_tags(self, count):
        """Generate a list of unique tags"""
        tag_list = []

        for _ in range(count):
            tag = self.generate_unique_tag(tag_list)
            tag_list.append(tag)

        return tag_list

    def generate_unique_tag(self, existing_tags=None):
        """Generate a tag not in the existing_tags list"""
        if existing_tags is None:
            existing_tags = []

        max_tag = (1 << self.N) - 1
        tag = random.randint(0, max_tag)

        while tag in existing_tags:
            tag = random.randint(0, max_tag)

        return tag

@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cam_tag_test(dut):
    """Test the CAM tag functionality"""
    tb = CamTagTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Print settings
    tb.print_settings()

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run basic test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting basic CAM test @ {time_ns}ns ===")
        await tb.run_basic_test()
        await tb.cleanup_cam()  # Clean up after test

        # Run capacity test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting capacity test @ {time_ns}ns ===")
        await tb.run_capacity_test()
        await tb.cleanup_cam()  # Clean up after test

        # Run concurrent access test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting concurrent access test @ {time_ns}ns ===")
        await tb.run_concurrent_access_test()
        await tb.cleanup_cam()  # Clean up after test

        # Run main loop test from CamTB base class
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting main loop test @ {time_ns}ns ===")
        await tb.main_loop()

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Set done flag and wait for any pending tasks
        tb.done = True
        await tb.wait_clocks('clk', 10)

def get_cam_params():
    """Generate CAM test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [(4, 8)]  # GATE: Minimal - just 4-bit, depth 8
    elif reg_level == 'FUNC':
        return [(8, 16), (4, 8)]  # FUNC: Small and medium
    else:  # FULL
        return [(8, 16), (4, 8), (8, 32), (8, 64)]  # FULL: All configurations

@pytest.mark.parametrize("n, depth", get_cam_params())
def test_cam_tag(request, n, depth):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "cam_tag"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/cam_tag.f'
    )

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create a human readable test identifier
    n_str = TBBase.format_dec(n, 2)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{dut_name}_n{n_str}_d{d_str}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    parameters = {'N': n, 'DEPTH': depth}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add parameter values to environment variables
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # Tell Verilator to use vcd
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
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
