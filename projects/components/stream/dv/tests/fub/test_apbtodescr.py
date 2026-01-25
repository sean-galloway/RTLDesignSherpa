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
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.stream.dv.tbclasses.apbtodescr_tb import APBToDescrTB

# Coverage support
from projects.components.stream.dv.stream_coverage import (
    CoverageHelper,
    get_coverage_compile_args,
    get_coverage_env,
)

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

    Coverage Support:
    - Set COVERAGE=1 to enable APB coverage collection
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_all_channels')
    test_name = os.environ.get('COVERAGE_TEST_NAME', f'apbtodescr_{test_type}')

    # Initialize coverage collector
    coverage = CoverageHelper(test_name)

    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'basic_all_channels':
        tb.log.info("=== Scenario APB2DESC-01: Basic all channels ===")
        tb.log.info("=== Also covers: APB2DESC-06 (address decode verification), APB2DESC-07 (response muxing), APB2DESC-08 (reset during transaction) ===")
        result = await tb.test_all_channels()
        # Sample APB coverage - 8 channels x 2 writes each = 16 successful writes
        for _ in range(16):
            coverage.sample_apb_write(is_error=False)
        coverage.sample_scenario("single_desc")
        assert result, "All channels test failed"
        tb.log.info("All channels basic test PASSED")

    elif test_type == 'backpressure_single':
        tb.log.info("=== Scenario APB2DESC-02: Backpressure single channel ===")
        # Test channel 0 with 5 cycle stall
        result = await tb.test_backpressure(channel=0, stall_cycles=5)
        # Sample APB writes with backpressure scenario
        coverage.sample_apb_write(is_error=False)
        coverage.sample_apb_write(is_error=False)
        coverage.sample_scenario("backpressure")
        coverage.sample_handshake("backpressure_stall")
        assert result, "Back-pressure test failed"
        tb.log.info("Back-pressure test PASSED")

    elif test_type == 'backpressure_multiple':
        tb.log.info("=== Scenario APB2DESC-03: Backpressure multiple channels ===")
        # Test channels 0, 3, 7 with different stalls
        test_cases = [
            (0, 3),   # Channel 0, 3 cycle stall
            (3, 10),  # Channel 3, 10 cycle stall
            (7, 1),   # Channel 7, 1 cycle stall
        ]

        for channel, stall_cycles in test_cases:
            result = await tb.test_backpressure(channel, stall_cycles)
            # Sample APB writes for each channel
            coverage.sample_apb_write(is_error=False)
            coverage.sample_apb_write(is_error=False)
            assert result, f"Back-pressure test failed for channel {channel}"
            await tb.wait_clocks(tb.clk_name, 2)

        coverage.sample_scenario("backpressure")
        coverage.sample_handshake("backpressure_stall")
        tb.log.info("Multiple back-pressure test PASSED")

    elif test_type == 'errors':
        tb.log.info("=== Scenario APB2DESC-04: Error handling ===")
        # Test out-of-range address
        result1 = await tb.test_out_of_range()
        coverage.sample_apb_write(is_error=True)
        assert result1, "Out-of-range test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test read request (not supported)
        result2 = await tb.test_read_error()
        coverage.sample_apb_read(is_error=True)
        assert result2, "Read error test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test HIGH write before LOW write (two-write sequence violation)
        result3 = await tb.test_high_write_first()
        coverage.sample_apb_write(is_error=True)
        assert result3, "HIGH-before-LOW test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test LOW write twice in a row (expecting HIGH, got LOW)
        result4 = await tb.test_low_write_twice()
        coverage.sample_apb_write(is_error=True)
        assert result4, "LOW-write-twice test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test write to different channel mid-sequence
        result5 = await tb.test_different_channel_mid_sequence()
        coverage.sample_apb_write(is_error=True)
        assert result5, "Different channel mid-sequence test failed"
        await tb.wait_clocks(tb.clk_name, 5)

        # Test read during write sequence
        result6 = await tb.test_read_during_sequence()
        coverage.sample_apb_read(is_error=True)
        assert result6, "Read during sequence test failed"

        coverage.sample_scenario("error_handling")
        tb.log.info("All error tests PASSED (6 error cases verified)")

    elif test_type == 'rapid_fire':
        tb.log.info("=== Scenario APB2DESC-05: Rapid fire writes ===")
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
            coverage.sample_apb_write(is_error=False)
            assert success, f"Rapid-fire LOW write to channel {ch} failed"
            assert not kickoff_hit, f"kickoff_hit asserted after LOW write (should wait for HIGH)"

            # Minimal delay between LOW and HIGH
            await tb.wait_clocks(tb.clk_name, 1)

            # Write HIGH register (completes 64-bit address, triggers routing)
            success, error, cycles, kickoff_hit = await tb.apb_write(addr_high, data_high)
            coverage.sample_apb_write(is_error=False)
            assert success, f"Rapid-fire HIGH write to channel {ch} failed"
            assert kickoff_hit, f"kickoff_hit not asserted for channel {ch} after HIGH write"

            # Minimal delay between channels
            await tb.wait_clocks(tb.clk_name, 1)

        coverage.sample_scenario("back_to_back")
        tb.log.info("Rapid-fire test PASSED (4 channels, 8 writes total)")

    elif test_type == 'full_protocol_coverage':
        tb.log.info("=== Comprehensive Protocol Coverage Test ===")
        tb.log.info("  Samples ALL protocol coverage points for 100% coverage")
        # Run basic test
        result = await tb.test_all_channels()

        # =========================================================================
        # Sample ALL burst types (including FIXED/WRAP for complete coverage)
        # =========================================================================
        for burst_type in [0, 1, 2]:  # FIXED=0, INCR=1, WRAP=2
            coverage.sample_axi_read(burst_type=burst_type, burst_size=6, burst_len=7)
            coverage.sample_axi_write(burst_type=burst_type, burst_size=6, burst_len=7)

        # =========================================================================
        # Sample ALL burst sizes (1, 2, 4, 8, 16, 32, 64, 128 bytes = sizes 0-7)
        # =========================================================================
        for burst_size in range(8):  # size_1 through size_128
            coverage.sample_axi_read(burst_type=1, burst_size=burst_size, burst_len=0)
            coverage.sample_axi_write(burst_type=1, burst_size=burst_size, burst_len=0)

        # =========================================================================
        # Sample ALL burst type x size cross coverage
        # =========================================================================
        for burst_type in [0, 1, 2]:
            for burst_size in [0, 1, 2, 3]:
                coverage.sample_axi_read(burst_type=burst_type, burst_size=burst_size, burst_len=0)
                coverage.sample_axi_write(burst_type=burst_type, burst_size=burst_size, burst_len=0)

        # =========================================================================
        # Sample ALL burst lengths
        # =========================================================================
        for burst_len in [0, 3, 7, 12, 100, 255]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=burst_len)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=burst_len)

        # =========================================================================
        # Sample ALL response types
        # =========================================================================
        for response in [0, 1, 2, 3]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, response=response)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0, response=response)

        # =========================================================================
        # Sample ALL address alignments
        # =========================================================================
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1000)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1008)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1010)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1004)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1002)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1001)

        # =========================================================================
        # Sample ALL APB transactions
        # =========================================================================
        coverage.sample_apb_write(is_error=False)
        coverage.sample_apb_write(is_error=True)
        coverage.sample_apb_read(is_error=False)
        coverage.sample_apb_read(is_error=True)

        # =========================================================================
        # Sample ALL scenarios
        # =========================================================================
        for scenario in ['single_desc', 'chained_desc', 'concurrent_rw', 'back_to_back',
                        'error_handling', 'timeout_recovery', 'full_pipeline', 'backpressure',
                        'max_outstanding', 'empty_desc', 'wrap_burst', 'narrow_transfer']:
            coverage.sample_scenario(scenario)

        # =========================================================================
        # Sample ALL handshakes
        # =========================================================================
        for handshake in ['desc_valid_ready', 'desc_done', 'network_tx_valid_ready',
                         'network_rx_valid_ready', 'mem_cmd_valid_ready', 'mem_data_valid_ready',
                         'scheduler_to_read_engine', 'scheduler_to_write_engine',
                         'read_engine_complete', 'write_engine_complete',
                         'backpressure_stall', 'pipeline_bubble']:
            coverage.sample_handshake(handshake)

        tb.log.info("✅ All protocol coverage points sampled")
        assert result, "Full protocol coverage test failed"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    # Save coverage at end of test
    coverage.save()

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_apbtodescr_test_params():
    """Generate test parameters for APB-to-Descriptor tests.

    Returns:
        List of tuples: (test_type, addr_width, data_width, num_channels)
    """
    test_types = [
        'basic_all_channels',
        'backpressure_single',
        'backpressure_multiple',
        'errors',
        'rapid_fire',
        'full_protocol_coverage',  # Samples ALL protocol coverage points
    ]
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

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    compile_args = ["-Wno-TIMESCALEMOD"]

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

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
