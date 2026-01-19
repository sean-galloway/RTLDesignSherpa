# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_regslice
# Purpose: GAXI Regslice (1-deep elastic buffer) Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-23

"""
GAXI Regslice Test - 1-Deep Elastic Buffer Verification

The regslice is a timing-friendly 1-deep elastic stage that always provides
1-cycle latency with 1 beat/clk throughput in steady state.

Intentionally aligned with gaxi_skid_buffer interface for compatibility,
so we can reuse GaxiBufferTB directly.

TEST LEVELS (per-test depth):
    basic (30s-1min):   Quick verification during development
    medium (2-3 min):   Integration testing for CI/branches
    full (5-8 min):     Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~1 min) - smoke test
    FUNC: 4 tests (~8 min) - functional coverage - DEFAULT
    FULL: 15 tests (~40 min) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width × 1 test_level = 1 test
    FUNC: 2 widths × 2 test_levels = 4 tests
    FULL: 5 widths × 3 test_levels = 15 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: basic|medium|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def gaxi_regslice_test(dut):
    '''Test the GAXI Regslice (1-deep elastic buffer) comprehensively'''
    tb = GaxiBufferTB(dut, dut.axi_aclk, dut.axi_aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Seed: {seed}')

    # Get test level from environment (default: basic)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    tb.log.info(f"Running test level: {test_level.upper()}")

    await tb.start_clock('axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    tb.log.info(f"Starting {test_level.upper()} GAXI Regslice test...")

    # Get available randomizer configurations
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available randomizer configs: {config_names}")

    # Define test configurations based on test level
    # Regslice is simpler than skid buffer (fixed 1-deep), so reduce counts
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast']
        packet_counts = {
            'simple_loops': 4 * tb.TEST_DEPTH,  # 4 for depth=1
            'back_to_back': 15,
            'stress_test': 20
        }
        run_comprehensive_sweep = False
        run_stress_test = False
    elif test_level == 'medium':
        # Moderate testing for CI
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'gaxi_stress', 'gaxi_realistic', 'moderate'
        ]
        packet_counts = {
            'simple_loops': 8 * tb.TEST_DEPTH,
            'back_to_back': 30,
            'stress_test': 50
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 6 * tb.TEST_DEPTH
        run_stress_test = True
    else:  # full
        # Comprehensive testing for regression
        essential_configs = [
            'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
            'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
            'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
            'gaxi_stress', 'gaxi_pipeline', 'gaxi_backpressure',
            'gaxi_realistic', 'gaxi_burst_heavy', 'gaxi_fine_grain'
        ]
        test_configs = [config for config in essential_configs if config in config_names]
        packet_counts = {
            'simple_loops': 12 * tb.TEST_DEPTH,
            'back_to_back': 50,
            'stress_test': 100
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 10 * tb.TEST_DEPTH
        run_stress_test = True

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Packet counts: {packet_counts}")

    # Run core tests with different randomizer configurations
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=15
        )
        tb.log.info(f"✅ Completed '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✅ Completed comprehensive sweep")

    # Always run back-to-back test (essential for GAXI validation)
    tb.log.info("Running back-to-back test...")
    await tb.back_to_back_test(count=packet_counts['back_to_back'])
    tb.log.info("✅ Completed back-to-back test")

    # Run stress test for medium and full levels
    if run_stress_test:
        tb.log.info("Running stress test...")
        stress_config = 'gaxi_stress' if 'gaxi_stress' in config_names else 'stress'
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'],
            delay_key=stress_config
        )
        tb.log.info("✅ Completed stress test")

    tb.log.info(f"✅ ALL {test_level.upper()} TESTS PASSED!")


def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (smoke test)
    REG_LEVEL=FUNC: 4 tests (functional coverage) - default
    REG_LEVEL=FULL: 15 tests (comprehensive validation)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Clock period (ns)
    clk_periods = [10]

    if reg_level == 'GATE':
        # Minimal - just prove it works
        # 1 test: 8-bit width, basic level
        return [
            (8, 10, 'basic'),
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - key combinations
        # 2 widths × 2 levels = 4 tests
        data_widths = [8, 32]
        test_levels = ['basic', 'medium']

        return list(product(data_widths, clk_periods, test_levels))

    else:  # FULL
        # Comprehensive testing
        # 5 widths × 3 levels = 15 tests
        data_widths = [8, 16, 32, 64, 128]
        test_levels = ['basic', 'medium', 'full']

        return list(product(data_widths, clk_periods, test_levels))


@pytest.mark.parametrize("data_width, clk_period, test_level", generate_test_params())
def test_gaxi_regslice(request, data_width, clk_period, test_level):
    """
    Pytest wrapper for GAXI regslice test

    Parameters:
        data_width: Data width (8, 16, 32, 64)
        clk_period: Clock period in ns
        test_level: Test comprehensiveness (basic, medium, full)
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Format test identifier
    test_id = f"{worker_id}_regslice_d{TBBase.format_dec(data_width, 2)}_{test_level}"

    # Get paths using dictionary format
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # Simulation build directory
    sim_build = os.path.join(tests_dir, f"local_sim_build/{module}_{test_id}")

    # Log file path
    log_path = os.path.join(log_dir, f'{test_id}.log')

    # RTL sources - single file for regslice
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_regslice.sv"),
    ]

    # Include directories
    includes = [
        rtl_dict['rtl_amba_includes'],
    ]

    # Test level message
    duration_msg = {
        'basic': '30s-1min',
        'medium': '2-3 min',
        'full': '5-8 min'
    }

    print("\n" + "="*80)
    print(f"Running {test_level.upper()} GAXI Regslice test: {test_id}")
    print(f"Data Width: {data_width}")
    print(f"Expected duration: {duration_msg[test_level]}")
    print("="*80)

    # Random seed
    seed = random.randint(0, 100000)

    # Compile-time parameters (no DEPTH parameter - regslice is fixed 1-deep)
    # Note: INSTANCE_NAME omitted due to Verilator FST tracing bug with string parameters
    parameters = {
        'DATA_WIDTH': data_width,
    }

    # Runtime environment variables
    extra_env = {
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': '1',  # Regslice is always 1-deep
        'TEST_MODE': 'skid',  # Regslice behaves like skid buffer
        'TEST_KIND': 'sync',
        'TEST_CLK_WR': str(clk_period),
        'TEST_CLK_RD': str(clk_period),
        'TEST_LEVEL': test_level,
        'SEED': str(seed),
    }

    # Compile arguments
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        '-Wall',
        '-Wno-SYNCASYNCNET',
        '-DUSE_ASYNC_RESET',
        '-Wno-UNUSED',
        '-Wno-DECLFILENAME',
        '-Wno-PINMISSING',
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    # Add include paths
    for inc in includes:
        compile_args.append(f'-I{inc}')

    # Add parameters
    for param, value in parameters.items():
        compile_args.append(f'-G{param}={value}')

    # Run the simulation
    # Note: waves=False due to Verilator FST bug with INSTANCE_NAME string parameter
    run(
        verilog_sources=verilog_sources,
        toplevel="gaxi_regslice",
        module=module,
        sim_build=sim_build,
        compile_args=compile_args,
        extra_env=extra_env,
        waves=False,  # VCD controlled by compile_args, not cocotb-test
    )

    # Generate waveform viewing command
    create_view_cmd(log_dir, log_path, sim_build, module, test_id)


if __name__ == "__main__":
    # Run basic test by default
    test_gaxi_regslice(None, 32, 10, 'basic')
