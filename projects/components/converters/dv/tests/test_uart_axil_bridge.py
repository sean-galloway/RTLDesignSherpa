# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: test_uart_axil_bridge
# Purpose: UART to AXI4-Lite Bridge Test Runner
#
# Documentation: projects/components/converters/rtl/uart_to_axil4/README.md
# Subsystem: tests
#
# Author: RTL Design Sherpa
# Created: 2025-11-09

"""
UART to AXI4-Lite Bridge Test Runner

Test runner for UART command parser to AXI4-Lite master bridge.
Imports testbench class from projects/components/converters/dv/tbclasses/uart_axil_bridge_tb.py

Test Levels:
- basic: Quick smoke test (4 write/read pairs)
- medium: Functional coverage (10 write/read operations)
- full: Comprehensive validation (30 operations, various patterns)

Tests UART command parsing (W/R commands) and AXI4-Lite transaction generation.
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
from projects.components.converters.dv.tbclasses.uart_axil_bridge_tb import UARTAXILBridgeTB
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def uart_axil_bridge_test(dut):
    """
    UART to AXI4-Lite Bridge test.

    Tests UART command parsing and AXI4-Lite transaction generation:
    - Write command parsing (W <addr> <data>)
    - Read command parsing (R <addr>)
    - AXI4-Lite master transaction generation
    - Response formatting (OK for writes, hex data for reads)

    Test intelligence resides here, infrastructure in TB class.

    Timeout: 500ms simulation time (UART is slow!)
    - basic: ~50ms sim time (4 operations)
    - medium: ~125ms sim time (10 operations)
    - full: ~375ms sim time (30 operations)
    """
    tb = UARTAXILBridgeTB(dut)

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

    tb.log.info(f"Running {test_level.upper()} UART→AXIL Bridge test suite")

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
        await tb.wait_clocks('aclk', 100)

        # Get final statistics
        final_stats = tb.get_statistics()

        # Log final results
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Commands sent:       {final_stats['commands_sent']}")
        tb.log.info(f"Writes completed:    {final_stats['writes_completed']}")
        tb.log.info(f"Reads completed:     {final_stats['reads_completed']}")
        tb.log.info(f"Total errors:        {final_stats['errors']}")
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
    - GATE: Quick smoke test (basic level only, single configuration)
    - FUNC: Functional coverage (basic + medium levels)
    - FULL: Comprehensive validation (all levels, all configurations)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # All parameters with embedded test_level
    all_params = [
        # GATE level: Basic configuration
        {'axil_data_width': 32, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'basic'},

        # FUNC level: Different data widths
        {'axil_data_width': 64, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'basic'},

        # FUNC level: Different baud rates
        {'axil_data_width': 32, 'axil_addr_width': 32, 'clks_per_bit': 434, 'test_level': 'basic'},  # 50MHz/115200

        # FUNC level: Medium test depth
        {'axil_data_width': 32, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'medium'},

        # FULL level: Comprehensive validation
        {'axil_data_width': 32, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'full'},
        {'axil_data_width': 64, 'axil_addr_width': 32, 'clks_per_bit': 868, 'test_level': 'full'},
    ]

    # Filter based on REG_LEVEL
    if reg_level == 'GATE':
        # Only basic test, single configuration
        params = [p for p in all_params if p['test_level'] == 'basic' and p['axil_data_width'] == 32 and p['clks_per_bit'] == 868]
    elif reg_level == 'FUNC':
        # Basic and medium tests
        params = [p for p in all_params if p['test_level'] in ['basic', 'medium']]
    else:  # FULL
        # All tests
        params = all_params

    return params


@pytest.mark.parametrize("params", generate_test_params())
def test_uart_axil_bridge(request, params):
    """
    UART to AXI4-Lite Bridge test with command parsing validation.

    Features:
    - UART command parsing (W/R commands)
    - AXI4-Lite master transaction generation
    - Response formatting (OK, hex data)
    - Write-then-read verification
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "uart_axil_bridge"
    toplevel = dut_name

    # Extract test parameters
    axil_data_width = params['axil_data_width']
    axil_addr_width = params['axil_addr_width']
    clks_per_bit = params['clks_per_bit']
    test_level = params['test_level']

    # Create descriptive test name (UNIQUE per configuration!)
    test_name_plus_params = (f"test_uart_axil_bridge_"
                            f"dw{axil_data_width}_aw{axil_addr_width}_"
                            f"baud{clks_per_bit}_{test_level}")

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
        filelist_path='projects/components/converters/rtl/filelists/uart_axil_bridge.f'
    )

    # RTL parameters
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': str(axil_addr_width),
        'AXIL_DATA_WIDTH': str(axil_data_width),
        'CLKS_PER_BIT': str(clks_per_bit),
    }

    # Calculate timeout based on test level (UART is slow!)
    base_timeout_ms = {'basic': 30000, 'medium': 60000, 'full': 180000}
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
        'AXIL_DATA_WIDTH': str(axil_data_width),
        'AXIL_ADDR_WIDTH': str(axil_addr_width),
        'CLKS_PER_BIT': str(clks_per_bit),
    }

    # VCD waveform generation support via WAVES environment variable
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

    plusargs = [
        "--trace",
    ]

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Test execution with reporting
    print(f"\n{'='*80}")
    print(f"UART→AXIL Bridge Test: {test_level.upper()}")
    print(f"Configuration: DW={axil_data_width}, AW={axil_addr_width}, Baud={clks_per_bit} clks/bit")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
    print(f"Features: UART command parsing, AXI4-Lite master")
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
        print(f"   Configuration: DW={axil_data_width}, AW={axil_addr_width}, Baud={clks_per_bit} clks/bit")

    except Exception as e:
        print(f"❌ {test_level.upper()} TEST FAILED: {str(e)}")
        print(f"   Configuration: DW={axil_data_width}, AW={axil_addr_width}, Baud={clks_per_bit} clks/bit")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")

        # Provide debugging guidance
        if "timeout" in str(e).lower():
            print(f"   💡 Check for UART timing or command parser deadlock")
        elif "assertion" in str(e).lower():
            print(f"   💡 Check UART command format in waveforms")

        raise
