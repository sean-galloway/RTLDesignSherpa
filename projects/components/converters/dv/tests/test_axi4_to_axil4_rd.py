# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi4_to_axil4_rd
# Purpose: AXI4 to AXIL4 Read Converter Test Runner (READ-ONLY)
#
# Documentation: projects/components/converters/rtl/README_AXI_CONVERTERS.md
# Subsystem: tests
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
AXI4 to AXIL4 Read Converter Test Runner - READ-ONLY

Test runner for AXI4→AXIL4 READ protocol downgrade converter with burst decomposition.
Imports testbench class from projects/components/converters/dv/tbclasses/axi4_to_axil4_rd_tb.py

Test Levels:
- basic: Quick smoke test (4 simple read bursts)
- medium: Multiple read bursts with varying lengths (10 bursts, len 1-16)
- full: Comprehensive read coverage (30 bursts, len 1-32, various burst types)

Tests ONLY the read path with burst decomposition. For write path, see test_axi4_to_axil4_wr.py.
"""

import os
import random
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root, get_paths, create_view_cmd

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import TB class from project area
from projects.components.converters.dv.tbclasses.axi4_to_axil4_rd_tb import AXI4ToAXIL4ReadTB
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def axi4_to_axil4_rd_test(dut):
    """
    AXI4 to AXIL4 Read Converter test - READ-ONLY with burst decomposition.

    Tests read path (AR, R channels) with:
    - Multi-beat burst decomposition
    - Address incrementing
    - Response aggregation

    Test intelligence resides here, infrastructure in TB class.
    """
    tb = AXI4ToAXIL4ReadTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    tb.log.info(f"Running {test_level.upper()} AXI4→AXIL4 Read Converter test suite")

    # Start clocks and reset
    await tb.setup_clocks_and_reset()

    # Start background transaction monitor (BFM handles protocol automatically)
    monitor_task = cocotb.start_soon(tb.axil4_transaction_monitor())

    try:
        # Run appropriate test suite based on test level
        if test_level == 'basic':
            success = await tb.run_basic_test()
        elif test_level == 'medium':
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
        tb.log.info(f"AXIL reads received:   {final_stats['axil_reads_received']}")
        tb.log.info(f"Bursts completed:      {final_stats['bursts_completed']}")
        tb.log.info(f"Address errors:        {final_stats['address_errors']}")
        tb.log.info(f"Decomposition errors:  {final_stats['decomposition_errors']}")
        tb.log.info(f"Total errors:          {final_stats['errors']}")
        tb.log.info("=" * 80)

        # Verify final results
        if success and final_stats['errors'] == 0:
            tb.log.info(f"✅ ALL {test_level.upper()} TESTS PASSED!")
        else:
            error_summary = []
            if not success:
                error_summary.append("Test suite failures")
            if final_stats['errors'] > 0:
                error_summary.append(f"{final_stats['errors']} errors")

            tb.log.error(f"❌ {test_level.upper()} TESTS FAILED: {', '.join(error_summary)}")
            assert False, f"Test failures: {', '.join(error_summary)}"

    finally:
        # Final cleanup wait
        await tb.wait_clocks('aclk', 10)


def generate_test_params():
    """
    Generate test parameters for different configurations.

    Respects REG_LEVEL environment variable:
    - GATE: Quick smoke test (basic level only, simple bursts)
    - FUNC: Functional coverage (basic + medium levels)
    - FULL: Comprehensive validation (all levels, complex bursts)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # All parameters with embedded test_level
    all_params = [
        # GATE level: Basic configurations
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'basic'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'basic'},
        {'data_width': 128, 'addr_width': 32, 'id_width': 8, 'test_level': 'basic'},

        # FUNC level: Additional widths
        {'data_width': 32, 'addr_width': 32, 'id_width': 4, 'test_level': 'basic'},
        {'data_width': 32, 'addr_width': 32, 'id_width': 16, 'test_level': 'basic'},

        # FUNC level: Medium test depth (more bursts, longer lengths)
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'medium'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'medium'},

        # FULL level: Comprehensive validation (maximum bursts, all burst types)
        {'data_width': 32, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'data_width': 64, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
        {'data_width': 128, 'addr_width': 32, 'id_width': 8, 'test_level': 'full'},
    ]

    # Filter based on REG_LEVEL
    if reg_level == 'GATE':
        # Only basic tests, limited configurations
        params = [p for p in all_params if p['test_level'] == 'basic' and p['data_width'] in [32, 64]]
    elif reg_level == 'FUNC':
        # Basic and medium tests
        params = [p for p in all_params if p['test_level'] in ['basic', 'medium']]
    else:  # FULL
        # All tests
        params = all_params

    return params


@pytest.mark.parametrize("params", generate_test_params())
def test_axi4_to_axil4_rd(request, params):
    """
    AXI4 to AXIL4 Read Converter test with burst decomposition validation.

    Features:
    - Protocol downgrade (AXI4 → AXI4-Lite)
    - Burst decomposition (multi-beat → multiple single-beat)
    - Address incrementing (INCR bursts)
    - FIXED burst support
    - Response aggregation
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi4_to_axil4_rd"  # Read-only burst decomposition converter
    toplevel = dut_name

    # Extract test parameters
    data_width = params['data_width']
    addr_width = params['addr_width']
    id_width = params['id_width']
    test_level = params['test_level']

    # Create descriptive test name
    test_name_plus_params = (f"test_axi4_to_axil4_rd_"
                            f"dw{data_width}_aw{addr_width}_id{id_width}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Simulation build directory
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Results directory
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/axi4_to_axil4_rd.f'
    )

    # RTL parameters
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': '1',
    }

    # Calculate timeout based on test level
    base_timeout_ms = {'basic': 10000, 'medium': 30000, 'full': 90000}
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
        'SEED': str(random.randint(0, 1000000)),
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

    plusargs = [
        "--trace",
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
    print(f"AXI4→AXIL4 Read Converter Test: {test_level.upper()}")
    print(f"Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
    print(f"Features: Burst decomposition, address incrementing")
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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✅ {test_level.upper()} TEST PASSED")
        print(f"   Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")

    except Exception as e:
        print(f"❌ {test_level.upper()} TEST FAILED: {str(e)}")
        print(f"   Configuration: DW={data_width}, AW={addr_width}, ID={id_width}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")

        # Provide debugging guidance
        if "timeout" in str(e).lower():
            print(f"   💡 Check for burst decomposition deadlocks")
        elif "assertion" in str(e).lower():
            print(f"   💡 Check address incrementing in waveforms")

        raise
