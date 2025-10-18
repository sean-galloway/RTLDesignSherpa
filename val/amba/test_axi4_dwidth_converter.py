# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_axi4_dwidth_converter
# Purpose: AXI4 Data Width Converter Test Runner
#
# Documentation: rtl/amba/axi4/AXI4_DATA_WIDTH_CONVERTER_SPEC.md
# Subsystem: tests
#
# Author: RTL Design Sherpa
# Created: 2025-10-18

"""
AXI4 Data Width Converter Test Runner

Test runner for AXI4 data width converter. Imports testbench class from
bin/CocoTBFramework/tbclasses/axi4/axi4_dwidth_converter_tb.py

Test Levels:
- basic: Quick smoke test (single write/read)
- medium: Multiple transactions with different patterns
- full: Comprehensive coverage (all burst types, strobes, errors)

Phase 1 Status: Basic infrastructure only - runs compilation check
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.axi4.axi4_dwidth_converter_tb import AXI4DWidthConverterTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4_dwidth_converter_test(dut):
    """
    AXI4 Data Width Converter test - imports TB class.

    Test intelligence resides here, infrastructure in TB class.
    """
    tb = AXI4DWidthConverterTB(dut)

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

    tb.log.info(f"Running {test_level.upper()} AXI4 Data Width Converter test suite")

    # Start clocks and reset
    await tb.setup_clocks_and_reset()

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
        tb.log.info(f"Transactions sent:     {final_stats['transactions_sent']}")
        tb.log.info(f"Transactions received: {final_stats['transactions_received']}")
        tb.log.info(f"Errors:                {final_stats['errors']}")
        tb.log.info(f"Width ratio:           {final_stats['width_ratio']}:1")
        tb.log.info(f"Conversion mode:       {final_stats['mode']}")
        tb.log.info("=" * 80)

        # Verify final results
        if success and final_stats['errors'] == 0:
            tb.log.info(f"🎉 ALL {test_level.upper()} TESTS PASSED!")
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
    Generate test parameters for different width conversion scenarios.

    For Phase 1, focus on basic upsize/downsize scenarios.
    For Phase 2+, expand to comprehensive coverage.
    """

    # Phase 1: Basic upsize scenarios
    params = [
        # Upsize: 32-bit → 128-bit (4:1 ratio)
        {'s_data_width': 32, 'm_data_width': 128, 'test_level': 'basic'},

        # Downsize: 128-bit → 32-bit (4:1 ratio)
        {'s_data_width': 128, 'm_data_width': 32, 'test_level': 'basic'},

        # Upsize: 64-bit → 256-bit (4:1 ratio)
        {'s_data_width': 64, 'm_data_width': 256, 'test_level': 'basic'},

        # Downsize: 256-bit → 64-bit (4:1 ratio)
        {'s_data_width': 256, 'm_data_width': 64, 'test_level': 'basic'},
    ]

    # Phase 2+: Uncomment for comprehensive coverage
    # test_levels = ['basic', 'medium', 'full']
    # width_pairs = [
    #     (32, 64), (32, 128), (32, 256),
    #     (64, 128), (64, 256),
    #     (128, 256)
    # ]
    # for (narrow, wide), level in product(width_pairs, test_levels):
    #     # Upsize
    #     params.append({'s_data_width': narrow, 'm_data_width': wide, 'test_level': level})
    #     # Downsize
    #     params.append({'s_data_width': wide, 'm_data_width': narrow, 'test_level': level})

    return params


@pytest.mark.parametrize("params", generate_test_params())
def test_axi4_dwidth_converter(request, params):
    """
    AXI4 Data Width Converter test with comprehensive validation.

    Phase 1 Features:
    - RTL skeleton with FIFO infrastructure
    - Basic pass-through data path
    - Parameter validation
    - CocoTB framework integration
    - GAXI BFM integration

    Phase 2+ Features (TODO):
    - Upsize write path (data accumulation)
    - Upsize read path (data splitting)
    - Downsize write path (data splitting)
    - Downsize read path (data accumulation)
    - Burst type support (INCR, FIXED, WRAP)
    - Error handling
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_axi4': 'rtl/amba/axi4',
        'rtl_amba_gaxi': 'rtl/amba/gaxi',
    })

    dut_name = "axi4_dwidth_converter"
    toplevel = dut_name

    # Extract test parameters
    s_data_width = params['s_data_width']
    m_data_width = params['m_data_width']
    test_level = params['test_level']

    # Calculate conversion characteristics
    width_ratio = max(s_data_width, m_data_width) // min(s_data_width, m_data_width)
    mode = "upsize" if s_data_width < m_data_width else "downsize"

    # Create descriptive test name
    test_name_plus_params = (f"test_axi4_dwidth_converter_"
                            f"{s_data_width}to{m_data_width}_"
                            f"{mode}_{width_ratio}x_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Simulation build directory
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Results directory
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_axi4'], f"{dut_name}.sv"),
        os.path.join(rtl_dict['rtl_amba_gaxi'], "gaxi_fifo_sync.sv"),
    ]

    includes = []

    # RTL parameters
    rtl_parameters = {
        'S_AXI_DATA_WIDTH': str(s_data_width),
        'M_AXI_DATA_WIDTH': str(m_data_width),
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
        'AW_FIFO_DEPTH': '4',
        'W_FIFO_DEPTH': '8',
        'B_FIFO_DEPTH': '4',
        'AR_FIFO_DEPTH': '4',
        'R_FIFO_DEPTH': '8',
    }

    # Calculate timeout based on test level
    base_timeout_ms = {'basic': 5000, 'medium': 15000, 'full': 45000}
    timeout_ms = base_timeout_ms[test_level]

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': str(random.randint(0, 1000000)),
        'TEST_LEVEL': test_level,
        'S_AXI_DATA_WIDTH': str(s_data_width),
        'M_AXI_DATA_WIDTH': str(m_data_width),
        'AXI_ID_WIDTH': '8',
        'AXI_ADDR_WIDTH': '32',
        'AXI_USER_WIDTH': '1',
        'TEST_CLK_PERIOD': '10',
    }

    compile_args = [
        "--trace",
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]

    sim_args = [
        "--trace",
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]

    plusargs = [
        "+trace",
        f"+s_width={s_data_width}",
        f"+m_width={m_data_width}",
        f"+mode={mode}",
        f"+test_level={test_level}",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Test execution with reporting
    print(f"\n{'='*80}")
    print(f"AXI4 Data Width Converter Test: {test_level.upper()}")
    print(f"Conversion: {s_data_width}-bit → {m_data_width}-bit ({mode} {width_ratio}:1)")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
    print(f"Phase 1: Infrastructure and compilation check")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✅ {test_level.upper()} TEST PASSED")
        print(f"   Configuration: {s_data_width}→{m_data_width} ({mode} {width_ratio}:1)")

    except Exception as e:
        print(f"❌ {test_level.upper()} TEST FAILED: {str(e)}")
        print(f"   Configuration: {s_data_width}→{m_data_width} ({mode} {width_ratio}:1)")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")

        # Provide debugging guidance
        if "timeout" in str(e).lower():
            print(f"   💡 Check for deadlocks or excessive latency in converter")
        elif "assertion" in str(e).lower():
            print(f"   💡 Check data integrity in waveforms")

        raise
