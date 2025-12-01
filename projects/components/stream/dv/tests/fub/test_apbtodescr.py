# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apbtodescr
# Purpose: APB-to-Descriptor Router Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19
# Updated: 2025-11-07 - Refactored to standard pattern

"""
APB-to-Descriptor Router Test Runner - v1.0

Test Types:
- 'basic_all_channels': Test basic write to all 8 channels
- 'backpressure_single': Test single channel with back-pressure (5 cycle stall)
- 'backpressure_multiple': Test multiple channels with varying back-pressure
- 'errors': Test error cases (out-of-range address, read request)
- 'rapid_fire': Test rapid sequential writes to different channels

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import random

# Setup Python path BEFORE any other imports
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Now import utilities to get proper repo root
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import pytest
import cocotb
from cocotb_test.simulator import run

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.stream.dv.tbclasses.apbtodescr_tb import APBToDescrTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_apbtodescr(dut):
    """Unified APB-to-Descriptor test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic_all_channels': Test basic write to all 8 channels
    - 'backpressure_single': Test single channel with back-pressure
    - 'backpressure_multiple': Test multiple channels with varying back-pressure
    - 'errors': Test error cases (out-of-range, read)
    - 'rapid_fire': Test rapid sequential writes to different channels
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_all_channels')
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'basic_all_channels':
        result = await tb.test_all_channels()
        assert result, "All channels test failed"
        tb.log.info("✓ All channels basic test PASSED")

    elif test_type == 'backpressure_single':
        # Test channel 0 with 5 cycle stall
        result = await tb.test_backpressure(channel=0, stall_cycles=5)
        assert result, "Back-pressure test failed"
        tb.log.info("✓ Back-pressure test PASSED")

    elif test_type == 'backpressure_multiple':
        # Test channels 0, 3, 7 with different stalls
        test_cases = [
            (0, 3),   # Channel 0, 3 cycle stall
            (3, 10),  # Channel 3, 10 cycle stall
            (7, 1),   # Channel 7, 1 cycle stall
        ]

        for channel, stall_cycles in test_cases:
            result = await tb.test_backpressure(channel, stall_cycles)
            assert result, f"Back-pressure test failed for channel {channel}"
            await tb.wait_clocks(tb.clk_name, 2)

        tb.log.info("✓ Multiple back-pressure test PASSED")

    elif test_type == 'errors':
        # Test out-of-range address
        result1 = await tb.test_out_of_range()
        assert result1, "Out-of-range test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test read request (not supported)
        result2 = await tb.test_read_error()
        assert result2, "Read error test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test HIGH write before LOW write (two-write sequence violation)
        result3 = await tb.test_high_write_first()
        assert result3, "HIGH-before-LOW test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test LOW write twice in a row (expecting HIGH, got LOW)
        result4 = await tb.test_low_write_twice()
        assert result4, "LOW-write-twice test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test write to different channel mid-sequence
        result5 = await tb.test_different_channel_mid_sequence()
        assert result5, "Different channel mid-sequence test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test read during write sequence
        result6 = await tb.test_read_during_sequence()
        assert result6, "Read during sequence test failed"

        tb.log.info("✓ All error tests PASSED (6 error cases verified)")

    elif test_type == 'rapid_fire':
        tb.log.info("Testing rapid-fire writes to multiple channels (TWO-WRITE SEQUENCE)")

        # Write to channels 0, 1, 2, 3 in quick succession
        for ch in range(4):
            # NEW: Two-write sequence for 64-bit descriptor address
            addr_low = ch * 8
            addr_high = ch * 8 + 4
            desc_addr_64 = 0x0003_0000 + (ch * 0x10_0000)
            data_low = desc_addr_64 & 0xFFFF_FFFF
            data_high = (desc_addr_64 >> 32) & 0xFFFF_FFFF

            # Write LOW register
            success, error, cycles, kickoff_hit = await tb.apb_write(addr_low, data_low)
            assert success, f"Rapid-fire LOW write to channel {ch} failed"
            assert not kickoff_hit, f"kickoff_hit asserted after LOW write (should wait for HIGH)"

            # Minimal delay between LOW and HIGH
            await tb.wait_clocks(tb.clk_name, 1)

            # Write HIGH register (completes 64-bit address, triggers routing)
            success, error, cycles, kickoff_hit = await tb.apb_write(addr_high, data_high)
            assert success, f"Rapid-fire HIGH write to channel {ch} failed"
            assert kickoff_hit, f"kickoff_hit not asserted for channel {ch} after HIGH write"

            # Minimal delay between channels
            await tb.wait_clocks(tb.clk_name, 1)

        tb.log.info("✓ Rapid-fire test PASSED (4 channels, 8 writes total)")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_apbtodescr_test_params():
    """Generate test parameters for APB-to-Descriptor tests.

    Returns:
        List of tuples: (test_type, addr_width, data_width, num_channels)
    """
    test_types = ['basic_all_channels', 'backpressure_single', 'backpressure_multiple', 'errors', 'rapid_fire']
    base_params = [
        # (addr_width, data_width, num_channels)
        (32, 32, 8),  # Standard STREAM configuration
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params

apbtodescr_params = generate_apbtodescr_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, addr_width, data_width, num_channels", apbtodescr_params)
def test_apbtodescr(request, test_type, addr_width, data_width, num_channels, test_level):
    """Pytest wrapper for APB-to-Descriptor tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../../../rtl/stream_macro'
    })

    dut_name = "apbtodescr"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/apbtodescr.f'
    )

    # Format parameters for unique test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    test_name_plus_params = f"test_{dut_name}_{test_type}_aw{aw_str}_dw{dw_str}_nc{nc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'NUM_CHANNELS': num_channels
    }

    extra_env = {
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = ["-Wno-TIMESCALEMOD"]
    if enable_waves:
        compile_args.extend(["--trace", "--trace-depth", "99"])

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_apbtodescr",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            simulator='verilator'
        )
        print(f"✓ APB to Descriptor {test_type} test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ APB to Descriptor {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
