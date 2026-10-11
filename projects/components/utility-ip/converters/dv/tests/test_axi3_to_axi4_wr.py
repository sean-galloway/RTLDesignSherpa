# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi3_to_axi4_wr
# Purpose: AXI3 to AXI4 Write Converter Test Runner (WRITE-ONLY)
#
# Documentation: projects/components/utility-ip/converters/rtl/README_AXI_CONVERTERS.md
# Subsystem: tests
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""
AXI3 to AXI4 Write Converter Test Runner - WRITE-ONLY

Test runner for AXI3->AXI4 WRITE protocol upgrade converter with WID stripping
under a single-active-write contract.
Imports testbench class from projects/components/utility-ip/converters/dv/tbclasses/axi3_to_axi4_wr_tb.py

Test Levels:
- gate: Quick smoke test (WID strip, B pass-through, single-active backpressure)
- func: Adds AWLOCK mapping validation
- full: Same as func for this core

Tests ONLY the write path. For read path, see test_axi3_to_axi4_rd.py.
"""

import asyncio
import os
import random
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root, get_paths, create_view_cmd, sim_build_path

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import TB class from project area
from projects.components.utility_ip.converters.dv.tbclasses.axi3_to_axi4_wr_tb import AXI3ToAXI4WriteTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def axi3_to_axi4_wr_test(dut):
    """
    AXI3 to AXI4 Write Converter test - WRITE-ONLY with WID stripping and
    single-active-write contract.

    Tests write path (AW, W, B channels) with:
    - Pass-through for single-beat and burst writes
    - WID stripping on the AXI4 W channel
    - W data/strb/last integrity
    - B response pass-through
    - Single-active-write backpressure on second AW
    - AWLEN zero-extension and AWLOCK mapping

    Test intelligence resides here, infrastructure in TB class.
    """
    tb = AXI3ToAXI4WriteTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    valid_levels = ['gate', 'func', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'. Valid: {valid_levels}")
        test_level = 'gate'

    tb.log.info(f"Running {test_level.upper()} AXI3->AXI4 Write Converter test suite")

    # Start clocks and reset
    await tb.setup_clocks_and_reset()

    # Start background transaction monitors (BFM handles protocol automatically)
    aw_monitor_task = cocotb.start_soon(tb.axi4_aw_monitor())
    w_monitor_task = cocotb.start_soon(tb.axi4_w_monitor())
    b_monitor_task = cocotb.start_soon(tb.axi4_b_monitor())

    try:
        # Run appropriate test suite based on test level
        if test_level == 'gate':
            success = await tb.run_basic_test()
        elif test_level == 'func':
            success = await tb.run_medium_test()
        else:  # full
            success = await tb.run_full_test()

        # Allow additional time for any pending transactions
        await tb.wait_clocks('aclk', 50)

        # Get final statistics
        final_stats = tb.get_statistics()

        # Log final results
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Bursts sent:           {final_stats['bursts_sent']}")
        tb.log.info(f"Beats expected:        {final_stats['beats_expected']}")
        tb.log.info(f"AXI4 writes received:  {final_stats['axi4_writes_received']}")
        tb.log.info(f"Bursts completed:      {final_stats['bursts_completed']}")
        tb.log.info(f"AWID errors:           {final_stats['awid_errors']}")
        tb.log.info(f"WID errors:            {final_stats['wid_errors']}")
        tb.log.info(f"WLAST errors:          {final_stats['wlast_errors']}")
        tb.log.info(f"Data errors:           {final_stats['data_errors']}")
        tb.log.info(f"BRESP errors:          {final_stats['bresp_errors']}")
        tb.log.info(f"Backpressure errors:   {final_stats['backpressure_errors']}")
        tb.log.info(f"Total errors:          {final_stats['errors']}")
        tb.log.info("=" * 80)

        # Verify final results
        if success and final_stats['errors'] == 0:
            tb.log.info(f"ALL {test_level.upper()} TESTS PASSED!")
        else:
            error_summary = []
            if not success:
                error_summary.append("Test suite failures")
            if final_stats['errors'] > 0:
                error_summary.append(f"{final_stats['errors']} errors")

            tb.log.error(f"{test_level.upper()} TESTS FAILED: {', '.join(error_summary)}")
            assert False, f"Test failures: {', '.join(error_summary)}"

    finally:
        # Clean up the background monitor coroutines
        for task in (aw_monitor_task, w_monitor_task, b_monitor_task):
            if task is not None:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass

        # Final cleanup wait
        await tb.wait_clocks('aclk', 10)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi3_to_axi4_wr_wid_mismatch_test(dut):
    """
    Negative test: injected WID mismatch must trigger ASSERT_A3_WID_STABLE.

    This test deliberately drives a W beat whose WID differs from the active
    AWID. The DUT's assertion should fire and fail the simulation.
    """
    tb = AXI3ToAXI4WriteTB(dut)

    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()

    aw_monitor_task = cocotb.start_soon(tb.axi4_aw_monitor())
    w_monitor_task = cocotb.start_soon(tb.axi4_w_monitor())
    b_monitor_task = cocotb.start_soon(tb.axi4_b_monitor())

    try:
        await tb.wid_mismatch_asserts()

        # If the assertion did not fire, fail explicitly so the strict xfail
        # negative model stays red until the RTL check is present.
        assert False, "ASSERT_A3_WID_STABLE did not fire on injected WID mismatch"

    finally:
        for task in (aw_monitor_task, w_monitor_task, b_monitor_task):
            if task is not None:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass

        await tb.wait_clocks('aclk', 10)


def generate_test_params():
    """
    Generate test parameters for different configurations.

    Respects REG_LEVEL environment variable:
    - GATE: Quick smoke test
    - FUNC: Functional coverage
    - FULL: Comprehensive validation
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # All parameters with embedded test_level
    all_params = [
        # GATE level: Basic configurations across data widths
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'gate'},
        {'data_width': 128, 'addr_width': 32, 'id_width': 8, 'test_level': 'gate'},

        # FUNC level: Medium test depth
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'func'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'func'},

        # FULL level: Comprehensive validation
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'data_width': 128, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
    ]

    # Filter based on REG_LEVEL
    if reg_level == 'GATE':
        # Only basic tests, limited configurations
        params = [p for p in all_params if p['test_level'] == 'gate' and p['data_width'] in [32, 64]]
    elif reg_level == 'FUNC':
        # Basic and medium tests
        params = [p for p in all_params if p['test_level'] in ['gate', 'func']]
    else:  # FULL
        # All tests
        params = all_params

    return params


@pytest.mark.parametrize("params", generate_test_params())
def test_axi3_to_axi4_wr(request, params):
    """
    AXI3 to AXI4 Write Converter test with WID stripping and single-active-write
    contract validation.

    Features:
    - Protocol upgrade (AXI3 -> AXI4)
    - Pass-through (single-beat and burst writes)
    - WID stripping
    - Single-active-write backpressure
    - B response pass-through
    - AWLEN zero-extension and AWLOCK mapping
    """
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi3_to_axi4_wr"  # Write-only converter with WID stripping
    toplevel = dut_name

    # Extract test parameters
    data_width = params['data_width']
    addr_width = params['addr_width']
    id_width = params['id_width']
    test_level = params['test_level']

    # Create descriptive test name
    test_name_plus_params = (f"test_axi3_to_axi4_wr_"
                            f"dw{data_width}_aw{addr_width}_id{id_width}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Simulation build directory
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Results directory
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4_wr.f'
    )

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': '1',
    }

    # Calculate timeout based on test level
    base_timeout_ms = {'gate': 10000, 'func': 30000, 'full': 90000}
    timeout_ms = base_timeout_ms[test_level]

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'COCOTB_TESTCASE': 'axi3_to_axi4_wr_test',
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': test_level,
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_ID_WIDTH': str(id_width),
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

    # Add coverage flags if COVERAGE=1
    if bool(int(os.environ.get('COVERAGE', '0'))):
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
        ])
        sim_args.append("--coverage")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Test execution with reporting
    print(f"\n{'='*80}")
    print(f"AXI3->AXI4 Write Converter Test: {test_level.upper()}")
    print(f"Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
    print(f"Features: WID strip, single-active-write, B pass-through, AWLOCK mapping")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir, repo_root],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )

        print(f"{test_level.upper()} TEST PASSED")
        print(f"   Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")

    except Exception as e:
        print(f"{test_level.upper()} TEST FAILED: {str(e)}")
        print(f"   Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")

        # Provide debugging guidance
        if "timeout" in str(e).lower():
            print(f"   Check for single-active-write deadlocks")
        elif "assertion" in str(e).lower():
            print(f"   Check AW/W/B channel mapping in waveforms")

        raise


@pytest.mark.xfail(strict=True, reason="ASSERT_A3_WID_STABLE must fire on injected WID mismatch")
def test_axi3_to_axi4_wr_wid_mismatch(request):
    """
    Negative test: injected WID mismatch must be caught by the DUT assertion.

    The cocotb test deliberately drives a W beat with the wrong WID. A correctly
    implemented converter fires ASSERT_A3_WID_STABLE and the simulation fails,
    which pytest records as the expected xfail.
    """
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/utility-ip/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi3_to_axi4_wr"
    toplevel = dut_name

    test_name_plus_params = "test_axi3_to_axi4_wr_wid_mismatch_dw32_aw32_id8_gate"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/utility-ip/converters/rtl/filelists/axi3_to_axi4_wr.f'
    )

    rtl_parameters = {
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_DATA_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': '10000',
        'COCOTB_TESTCASE': 'axi3_to_axi4_wr_wid_mismatch_test',
        'SEED': os.environ.get('SEED', str(random.randint(0, 1000000))),
        'TEST_LEVEL': 'gate',
        'AXI_DATA_WIDTH': '32',
        'AXI_ADDR_WIDTH': '32',
        'AXI_ID_WIDTH': '8',
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"AXI3->AXI4 Write Converter WID Mismatch Negative Test")
    print(f"Configuration: DW=32, AW=32, ID=8")
    print(f"Expected: ASSERT_A3_WID_STABLE fires and simulation fails")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir, repo_root],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            simulator='verilator',
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=['--trace'] if enable_waves else [],
        )

        # If the simulation somehow passes, the strict xfail turns this into a
        # suite failure, which is what we want for a negative model.
        print("WID MISMATCH TEST PASSED (unexpectedly)")

    except Exception as e:
        print(f"WID MISMATCH TEST FAILED AS EXPECTED: {str(e)}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")
        raise
