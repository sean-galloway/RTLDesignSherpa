# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_skid_buffer
# Purpose: GAXI Skid Buffer Test with Parameterized Test Levels
#
# Documentation: PRD.md, docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-23 (refactored from test_gaxi_buffer_sync.py)

"""
GAXI Skid Buffer Test with Parameterized Test Levels

Tests gaxi_skid_buffer.sv - zero-latency bypass buffer with 2-entry elastic storage.

TEST LEVELS (per-test depth):
    basic (2-3 min):   Quick verification during development
    medium (5-8 min):  Integration testing for CI/branches
    full (15-25 min):  Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~3 min) - smoke test
    FUNC: 4 tests (~15 min) - functional coverage - DEFAULT
    FULL: 36 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width × 1 depth × 1 test_level = 1 test
    FUNC: 2 widths × 1 depth × 2 test_levels = 4 tests
    FULL: 4 widths × 3 depths × 3 test_levels = 36 tests

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
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# WaveDrom support
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import (
    get_gaxi_field_config,
    create_gaxi_wavejson_generator,
)
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from CocoTBFramework.components.shared.field_config import FieldDefinition


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def gaxi_skid_buffer_test(dut):
    '''Test the GAXI Skid Buffer comprehensively with FlexConfigGen randomizers'''
    tb = GaxiBufferTB(dut, dut.axi_aclk, dut.axi_aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

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
    tb.log.info(f"Starting {test_level.upper()} GAXI Skid Buffer test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained']
        packet_counts = {
            'simple_loops': 4 * tb.TEST_DEPTH,
            'back_to_back': 15,
            'stress_test': 20
        }
        run_comprehensive_sweep = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
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

    else:  # test_level == 'full'
        # Comprehensive testing for validation
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
        tb.log.info(f"✓ Completed '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✓ Completed comprehensive sweep")

    # Always run back-to-back test (essential for GAXI validation)
    tb.log.info("Running back-to-back test...")
    await tb.back_to_back_test(count=packet_counts['back_to_back'])
    tb.log.info("✓ Completed back-to-back test")

    # Run stress test for medium and full levels
    if run_stress_test:
        tb.log.info("Running stress test...")
        stress_config = 'gaxi_stress' if 'gaxi_stress' in config_names else 'stress'
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'],
            delay_key=stress_config
        )
        tb.log.info("✓ Completed stress test")

    tb.log.info(f"✓ ALL {test_level.upper()} GAXI SKID BUFFER TESTS PASSED!")


@cocotb.test(timeout_time=5, timeout_unit="sec")
async def gaxi_skid_buffer_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for GAXI skid buffer.

    Generates 3 key scenarios:
    1. Write to empty (zero-latency bypass)
    2. Burst write until full (backpressure)
    3. Simultaneous read/write (pass-through)

    Environment Variables:
        ENABLE_WAVEDROM: Enable waveform generation (1/0, default: 0)
    """
    # Check if waveforms are enabled
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), skipping wavedrom test")
        return

    dut._log.info("=== GAXI Skid Buffer WaveDrom Test ===")

    # Setup clock and reset
    tb = GaxiBufferTB(dut, dut.axi_aclk, dut.axi_aresetn)
    await tb.start_clock('axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_aclk', 5)

    # Setup WaveDrom
    field_config = get_gaxi_field_config(data_width=8)
    wave_generator = create_gaxi_wavejson_generator(field_config, signal_prefix="")

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config,
        debug_level=1
    )

    wave_solver.add_clock_group('default', dut.axi_aclk)

    # Bind signals
    wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_', field_config=field_config)
    wave_solver.auto_bind_signals('gaxi', signal_prefix='rd_', field_config=field_config)
    wave_solver.add_signal_binding('clk', 'axi_aclk')
    wave_solver.add_signal_binding('rst_n', 'axi_aresetn')

    # Internal signals
    try:
        count_field = FieldDefinition('count', 4, format='dec', description='Buffer count')
        wave_solver.add_signal_binding('count', 'count', count_field)
    except:
        dut._log.info("Note: 'count' signal not available")

    # Define constraints for 3 key scenarios
    # Scenario 1: Write to empty (bypass)
    write_empty = TemporalConstraint(
        name="skid_write_empty",
        events=[TemporalEvent("wr_start", SignalTransition("wr_valid", 0, 1))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=12,
        context_cycles_before=3,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_data', 'rd_data', '->', 'bypass')]
    )
    wave_solver.add_constraint(write_empty)

    # Scenario 2: Backpressure
    backpressure = TemporalConstraint(
        name="skid_backpressure",
        events=[TemporalEvent("full", SignalTransition("wr_ready", 1, 0))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=20,
        context_cycles_before=4,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_ready', 'wr_valid', '->', 'blocked')]
    )
    wave_solver.add_constraint(backpressure)

    # Scenario 3: Simultaneous read/write
    simultaneous = TemporalConstraint(
        name="skid_simultaneous",
        events=[TemporalEvent("both", SignalTransition("wr_valid", 0, 1))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=18,
        context_cycles_before=3,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_data', 'rd_data', '->', 'flow')]
    )
    wave_solver.add_constraint(simultaneous)

    dut._log.info("✓ WaveDrom configured: 3 scenarios for skid buffer")

    # Scenario 1: Write to empty (tests bypass)
    dut._log.info("=== Scenario 1: Write to empty (bypass) ===")
    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    dut.wr_data.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)

    dut.wr_valid.value = 1
    dut.wr_data.value = 0xA0
    await RisingEdge(dut.axi_aclk)
    dut.wr_data.value = 0xA1
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 1 captured")

    # Drain
    dut.rd_ready.value = 1
    for _ in range(4):
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    # Scenario 2: Fill until backpressure
    dut._log.info("=== Scenario 2: Burst write until full ===")
    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)

    dut.wr_valid.value = 1
    for i in range(6):
        dut.wr_data.value = 0xB0 + i
        await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 2 captured")

    # Drain
    dut.rd_ready.value = 1
    for _ in range(6):
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    # Scenario 3: Simultaneous read/write
    dut._log.info("=== Scenario 3: Simultaneous read/write ===")
    # Pre-fill buffer
    dut.wr_valid.value = 1
    dut.wr_data.value = 0xC0
    await RisingEdge(dut.axi_aclk)
    dut.wr_data.value = 0xC1
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)

    # Simultaneous operations
    for i in range(3):
        dut.wr_valid.value = 1
        dut.rd_ready.value = 1
        dut.wr_data.value = 0xD0 + i
        await RisingEdge(dut.axi_aclk)
        dut.wr_valid.value = 0
        dut.rd_ready.value = 0
        await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 3 captured")

    dut._log.info("✓ GAXI Skid Buffer WaveDrom Complete: 3 scenarios generated")


def generate_test_params():
    """
    Generate test parameters for gaxi_skid_buffer based on REG_LEVEL.

    REG_LEVEL values:
        GATE: 1 test - minimal smoke test (~3 min)
        FUNC: 4 tests - functional coverage (~15 min) - DEFAULT
        FULL: 36 tests - comprehensive validation (~2 hours)

    For debugging, override REG_LEVEL:
        REG_LEVEL=GATE pytest test_gaxi_skid_buffer.py -v
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal smoke test - just prove it works
        return [
            (8, 4, 10, 'basic'),  # One basic configuration
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - key combinations
        widths = [8, 32]
        depths = [4]
        clk_periods = [10]
        test_levels = ['basic', 'medium']

        return list(product(widths, depths, clk_periods, test_levels))
        # Result: 2 widths × 1 depth × 2 levels = 4 tests

    else:  # FULL
        # Comprehensive testing - all meaningful combinations
        widths = [8, 16, 32, 64]
        depths = [2, 4, 8]
        clk_periods = [10]
        test_levels = ['basic', 'medium', 'full']

        return list(product(widths, depths, clk_periods, test_levels))
        # Result: 4 widths × 3 depths × 3 levels = 36 tests


params = generate_test_params()


@pytest.mark.parametrize("data_width, depth, clk_period, test_level", params)
def test_gaxi_skid_buffer(request, data_width, depth, clk_period, test_level):
    """
    Parameterized GAXI skid buffer test with configurable test levels.

    Tests gaxi_skid_buffer.sv - zero-latency bypass buffer.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min)
    - medium: Integration testing (5-8 min)
    - full: Comprehensive validation (15-25 min)
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """
    Parameterized GAXI skid buffer test with configurable test levels.

    Tests gaxi_skid_buffer.sv - zero-latency bypass buffer.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min)
    - medium: Integration testing (5-8 min)
    - full: Comprehensive validation (15-25 min)
    """
    # Get all directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "gaxi_skid_buffer"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], f"{dut_name}.sv"),
    ]

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cl_str = TBBase.format_dec(clk_period, 3)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_gaxi_skid_buffer_w{w_str}_d{d_str}_cl{cl_str}_{test_level}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = [rtl_dict['rtl_amba_includes']]

    # RTL parameters
    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'INSTANCE_NAME': f'"skid_{test_level}"'
    }

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 2000  # 2 seconds base
    timeout_ms = base_timeout * timeout_multipliers.get(test_level, 1)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(clk_period),
        'TEST_CLK_RD': str(clk_period),
        'TEST_MODE': 'skid',
        'TEST_KIND': 'sync'
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} test: gaxi_skid_buffer")
    print(f"Config: depth={depth}, width={data_width}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
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
            testcase="gaxi_skid_buffer_test",
        )
        print(f"✓ {test_level.upper()} test PASSED: gaxi_skid_buffer")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


# WaveDrom test
@pytest.mark.parametrize("data_width, depth, clk_period", [(8, 4, 10)])
def test_gaxi_skid_buffer_wavedrom(request, data_width, depth, clk_period):
    """
    GAXI skid buffer wavedrom test - generates timing diagrams.

    Run with: pytest test_gaxi_skid_buffer.py::test_gaxi_skid_buffer_wavedrom -v
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "gaxi_skid_buffer"
    verilog_sources = [os.path.join(rtl_dict['rtl_gaxi'], f"{dut_name}.sv")]

    test_name_plus_params = "test_gaxi_skid_buffer_wavedrom"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'INSTANCE_NAME': '"skid_wd"'
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'ENABLE_WAVEDROM': '1',
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'COCOTB_TEST_TIMEOUT': '10000'
    }

    print(f"\n{'='*80}")
    print(f"Running WaveDrom test: gaxi_skid_buffer")
    print(f"Will generate 3 scenarios")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            testcase="gaxi_skid_buffer_wavedrom_test",
        )
        print("✓ WaveDrom test PASSED: gaxi_skid_buffer - 3 scenarios generated")
    except Exception as e:
        print(f"✗ WaveDrom test FAILED: {str(e)}")
        raise


if __name__ == "__main__":
    # Run basic test by default
    test_gaxi_skid_buffer(None, 8, 4, 10, 'basic')
