# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_drop_fifo_sync
# Purpose: Test runner for gaxi_drop_fifo_sync module.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for gaxi_drop_fifo_sync module.

This module provides pytest test functions that instantiate and run tests
for the synchronous FIFO with drop capability.

Test Scenarios:
- Basic FIFO operations (write/read)
- Drop by count (specific number of entries)
- Drop all (flush entire FIFO)
- Drop timing (3-cycle latency)
- I/O blocking during drop
- Pointer wraparound with drop
"""

import os
import sys
import pytest
import cocotb
import random

# Import testbench class (reusable infrastructure)
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../bin'))
from CocoTBFramework.tbclasses.gaxi.gaxi_drop_fifo_sync_tb import GaxiDropFifoSyncTB

# Import run function for pytest
from cocotb_test.simulator import run

# Import path utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


##############################################################################
# CocoTB Test Functions (imported by pytest test cases)
##############################################################################

@cocotb.test()
async def basic_fifo_operation_cocotb(dut):
    """CocoTB test: Basic FIFO write/read without drops."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_fifo_operation()
    tb.log.info("✅ Basic FIFO operation test PASSED")


@cocotb.test()
async def drop_by_count_cocotb(dut):
    """CocoTB test: Dropping specific number of entries."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_drop_by_count()
    tb.log.info("✅ Drop by count test PASSED")


@cocotb.test()
async def drop_all_cocotb(dut):
    """CocoTB test: Dropping all FIFO entries."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_drop_all()
    tb.log.info("✅ Drop all test PASSED")


@cocotb.test()
async def drop_during_io_blocked_cocotb(dut):
    """CocoTB test: Normal I/O is blocked during drop operation."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_drop_during_io_blocked()
    tb.log.info("✅ I/O blocking during drop test PASSED")


@cocotb.test()
async def wraparound_with_drop_cocotb(dut):
    """CocoTB test: Drop operation across FIFO wraparound boundary."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_wraparound_with_drop()
    tb.log.info("✅ Wraparound with drop test PASSED")


##############################################################################
# Pytest Test Cases (parameterized test generation)
##############################################################################

def generate_test_parameters():
    """
    Generate test parameter combinations for pytest parameterization.

    Returns:
        List of tuples: (data_width, depth, registered, test_id)
    """
    test_params = []

    # Basic configurations
    configs = [
        # (DATA_WIDTH, DEPTH, REGISTERED, Description)
        (8,  8,   0, "minimal-mux"),       # Minimal FIFO, mux mode
        (8,  8,   1, "minimal-flop"),      # Minimal FIFO, flop mode
        (32, 16,  0, "small-mux"),         # Small FIFO
        (32, 16,  1, "small-flop"),        # Small FIFO, registered
        (64, 64,  0, "medium-mux"),        # Medium FIFO
        (64, 256, 0, "large-mux"),         # Large FIFO
    ]

    for dw, depth, registered, test_id in configs:
        test_params.append((dw, depth, registered, test_id))

    return test_params


@pytest.mark.parametrize("data_width, depth, registered, test_id",
                         generate_test_parameters())
def test_gaxi_drop_fifo_sync(request, data_width, depth, registered, test_id):
    """
    Pytest test runner for gaxi_drop_fifo_sync with parameterization.

    Args:
        request: pytest request fixture
        data_width: Width of data bus
        depth: FIFO depth (must be power of 2)
        registered: 0 = mux mode, 1 = flop mode
        test_id: Test configuration identifier
    """

    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    # DUT information
    dut_name = "gaxi_drop_fifo_sync"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], 'gaxi/gaxi_drop_fifo_sync.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin_load.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'fifo_control.sv'),
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    test_name_plus_params = f"test_gaxi_drop_fifo_sync_dw{data_width}_d{depth}_r{registered}_{test_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': str(registered),
        'ALMOST_WR_MARGIN': '1',
        'ALMOST_RD_MARGIN': '1',
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--Wno-UNOPTFLAT",
    ]

    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    # Enable waveform dumping
    extra_env['WAVES'] = '1'

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running test: data_width={data_width}, depth={depth}, registered={registered}, id={test_id}")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

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
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ Test PASSED: data_width={data_width}, depth={depth}, registered={registered}, id={test_id}")
    except Exception as e:
        print(f"✗ Test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms run: {cmd_filename}")
        raise


##############################################################################
# Smoke Test (Quick Verification)
##############################################################################

def test_gaxi_drop_fifo_smoke():
    """
    Quick smoke test with minimal configuration.

    Useful for rapid iteration during development.
    """
    import types
    fake_request = types.SimpleNamespace()

    test_gaxi_drop_fifo_sync(
        request=fake_request,
        data_width=32,
        depth=16,
        registered=0,
        test_id="smoke"
    )


if __name__ == "__main__":
    """
    Allow running tests directly: python test_gaxi_drop_fifo_sync.py
    """
    pytest.main([__file__, "-v", "-s"])
