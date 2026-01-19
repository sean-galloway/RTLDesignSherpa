# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cdc_handshake
# Purpose: CDC Handshake Main Test - test_cdc_handshake.py
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
CDC Handshake Main Test - test_cdc_handshake.py

Main test file that should be placed in the tests directory.
This integrates the CDC handshake testbench with sophisticated features.
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.amba.cdc_handshake import CDCHandshakeTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cdc_handshake_test(dut):
    """CDC handshake test with sophisticated patterns and analysis"""


    tb = CDCHandshakeTB(dut)

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

    tb.log.info(f"Running {test_level.upper()} CDC test suite")

    # Start the clocks with different periods for true CDC behavior
    await tb.start_clock('clk_src', tb.clk_src_PERIOD_NS, 'ns')
    await tb.start_clock('clk_dst', tb.clk_dst_PERIOD_NS, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run appropriate test suite based on test level
        if test_level == 'basic':
            success = await tb.run_basic_tests()
        elif test_level == 'medium':
            success = await tb.run_medium_tests()
        else:  # full
            success = await tb.run_full_tests()

        # Allow additional time for any pending transactions
        await tb.wait_clocks('clk_src', 50)
        await tb.wait_clocks('clk_dst', 50)

        # Get final comprehensive statistics
        final_stats = tb.get_comprehensive_statistics()

        # Log final results
        tb.log.info("=" * 80)
        tb.log.info(f"FINAL {test_level.upper()} TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Transactions sent: {final_stats['transactions_sent']}")
        tb.log.info(f"Transactions verified: {final_stats['transactions_verified']}")
        tb.log.info(f"Total errors: {final_stats['total_errors']}")
        tb.log.info(f"CDC violations: {final_stats['cdc_violations']}")
        tb.log.info(f"Test duration: {final_stats['test_duration_ns']/1e6:.2f}ms")

        if 'avg_cdc_latency_ns' in final_stats:
            tb.log.info(f"Average CDC latency: {final_stats['avg_cdc_latency_ns']:.2f}ns")
            tb.log.info(f"CDC latency range: {final_stats['min_cdc_latency_ns']:.2f}ns - {final_stats['max_cdc_latency_ns']:.2f}ns")

        if final_stats['throughput_tps'] > 0:
            tb.log.info(f"Throughput: {final_stats['throughput_tps']:.1f} transactions/second")

        tb.log.info("=" * 80)

        # Verify final results
        if success and final_stats['total_errors'] == 0:
            tb.log.info(f"🎉 ALL {test_level.upper()} CDC TESTS PASSED!")
        else:
            error_summary = []
            if not success:
                error_summary.append("Test suite failures")
            if final_stats['total_errors'] > 0:
                error_summary.append(f"{final_stats['total_errors']} transaction errors")
            if final_stats['cdc_violations'] > 0:
                error_summary.append(f"{final_stats['cdc_violations']} CDC violations")

            tb.log.error(f"❌ {test_level.upper()} CDC TESTS FAILED: {', '.join(error_summary)}")
            assert False, f"CDC test failures: {', '.join(error_summary)}"

    finally:
        # Set done flag to terminate any background handlers
        tb.done = True

        # Final cleanup wait
        await tb.wait_clocks('clk_src', 10)
        await tb.wait_clocks('clk_dst', 10)


def generate_cdc_test_params():
    """
    Generate CDC test parameters with focus on clock domain crossing scenarios.

    For quick debugging, modify this function:

    Examples:
        # Single test case:
        return [{'clk_src_period_ns': 15, 'clk_dst_period_ns': 10, 'test_level': 'basic'}]

        # Only basic tests:
        params = []
        for src_p in [10, 15, 20, 50]:
            for dst_p in [10, 15, 20]:
                if src_p != dst_p:  # Skip same frequency
                    params.append({'clk_src_period_ns': src_p, 'clk_dst_period_ns': dst_p, 'test_level': 'basic'})
        return params
    """

    # Comprehensive CDC frequency combinations
    src_periods = [10, 15, 20, 25, 50, 100]  # Source clock periods (ns)
    dst_periods = [10, 15, 20, 25, 50]       # Destination clock periods (ns)
    test_levels = ['basic', 'medium', 'full']

    params = []

    # Generate combinations focusing on interesting CDC scenarios
    for src_period, dst_period, test_level in product(src_periods, dst_periods, test_levels):
        # Skip same frequency for medium/full (not interesting for CDC)
        if src_period == dst_period and test_level != 'basic':
            continue

        # Limit very slow combinations to basic level only
        if (src_period >= 100 or dst_period >= 50) and test_level != 'basic':
            continue

        ratio = dst_period / src_period

        # Include all combinations for basic level
        if test_level == 'basic':
            params.append({
                'clk_src_period_ns': src_period,
                'clk_dst_period_ns': dst_period,
                'test_level': test_level
            })
        # For medium level, focus on common ratios
        elif test_level == 'medium' and (
            0.4 <= ratio <= 2.5 or  # Common ratios
            abs(ratio - 1.0) < 0.1 or  # Near same frequency
            abs(ratio - 2.0) < 0.1 or  # 2:1 ratio
            abs(ratio - 0.5) < 0.1     # 1:2 ratio
        ):
            params.append({
                'clk_src_period_ns': src_period,
                'clk_dst_period_ns': dst_period,
                'test_level': test_level
            })
        # For full level, focus on challenging ratios
        elif test_level == 'full' and (
            ratio > 2.0 or ratio < 0.5 or  # Extreme ratios
            abs(ratio - 1.5) < 0.1 or      # 3:2 ratio
            abs(ratio - 0.67) < 0.1        # 2:3 ratio
        ):
            params.append({
                'clk_src_period_ns': src_period,
                'clk_dst_period_ns': dst_period,
                'test_level': test_level
            })

    # For debugging: uncomment to limit scope
    return [{'clk_src_period_ns': 30, 'clk_dst_period_ns': 10, 'test_level': 'full'}, {'clk_src_period_ns': 10, 'clk_dst_period_ns': 30, 'test_level': 'full'}]
    # return params


@pytest.mark.parametrize("params", generate_cdc_test_params())
def test_cdc_handshake(request, params):
    """
    CDC handshake test with comprehensive validation.

    Features:
    - Test Levels: basic (2-3min), medium (5-8min), full (15-25min)
    - Clock Combinations: Comprehensive CDC frequency matrix
    - Randomization: FlexConfigGen with 20+ sophisticated patterns
    - Verification: Cross-domain integrity, timing analysis, memory consistency
    - Analysis: CDC latency, throughput, timing violations
    - Statistics: Comprehensive error tracking and performance metrics

    For debugging: Modify generate_cdc_test_params() to limit test scope
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared':'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "cdc_handshake"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv")
    ]

    # Extract test parameters
    src_period = params['clk_src_period_ns']
    dst_period = params['clk_dst_period_ns']
    test_level = params['test_level']

    # Calculate CDC characteristics for naming and analysis
    ratio = dst_period / src_period
    if ratio > 1.1:
        ratio_desc = f"slow{ratio:.1f}x"
    elif ratio < 0.9:
        ratio_desc = f"fast{1/ratio:.1f}x"
    else:
        ratio_desc = "same"

    # Create descriptive test name
    test_name_plus_params = (f"test_{worker_id}_cdc_handshake_"
                            f"src{src_period}ns_dst{dst_period}ns_"
                            f"{ratio_desc}_{test_level}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Simulation build directory
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Results directory
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]
    # RTL parameters
    total_width = 32 + 32 + 32//8 + 1 + 3  # addr + data + strb + write + prot
    rtl_parameters = {
        'DATA_WIDTH': str(total_width),
    }

    # Calculate timeouts based on test level and clock speeds
    base_timeout_ms = {'basic': 5000, 'medium': 15000, 'full': 45000}
    max_period = max(src_period, dst_period)
    slow_factor = max(1, max_period / 10)
    timeout_ms = int(base_timeout_ms[test_level] * slow_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'SEED': str(random.randint(0, 1000000)),
        'TEST_LEVEL': test_level,
        'SUPER_DEBUG': 'false',
        'TEST_ADDR_WIDTH': '32',
        'TEST_DATA_WIDTH': '32',
        'clk_src_PERIOD_NS': str(src_period),
        'clk_dst_PERIOD_NS': str(dst_period),
        'CDC_RATIO': f"{ratio:.3f}",
        'CDC_TYPE': 'fast_to_slow' if ratio > 1 else 'slow_to_fast' if ratio < 1 else 'same_freq',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend(get_coverage_compile_args())


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-underscore",
        "--trace-threads", "1",
    ]

    plusargs = [
        "--trace",
        f"+cdc_src_period={src_period}",
        f"+cdc_dst_period={dst_period}",
        f"+test_level={test_level}",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # test execution with reporting
    print(f"\n{'='*80}")
    print(f"CDC Handshake Test: {test_level.upper()}")
    print(f"Clock Configuration: src={src_period}ns ({1000/src_period:.1f}MHz), dst={dst_period}ns ({1000/dst_period:.1f}MHz)")
    print(f"CDC Ratio: {ratio:.3f} ({extra_env['CDC_TYPE']})")
    print(f"Expected Duration: {timeout_ms/1000:.1f}s")
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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✅ {test_level.upper()} CDC TEST PASSED")
        print(f"   Clock config: src={src_period}ns, dst={dst_period}ns, ratio={ratio:.3f}")

    except Exception as e:
        print(f"❌ {test_level.upper()} CDC TEST FAILED: {str(e)}")
        print(f"   Clock config: src={src_period}ns, dst={dst_period}ns, ratio={ratio:.3f}")
        print(f"   Logs: {log_path}")
        print(f"   Waveforms: {cmd_filename}")

        # Provide debugging guidance
        if "timeout" in str(e).lower():
            print(f"   💡 Check for CDC deadlocks or excessive latency")
        elif "assertion" in str(e).lower():
            print(f"   💡 Check CDC timing violations in waveforms")

        raise
