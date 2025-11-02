# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_buffer_async
# Purpose: GAXI Async Buffer Test with Parameterized Test Levels
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXI Async Buffer Test - Clock Domain Crossing Validation

Tests async buffers with independent write/read clock domains, validating:
- Clock domain crossing (CDC) behavior
- Various clock ratios (1x to 2.5x)
- Backpressure handling across domains
- Multiple buffer modes (skid, fifo_mux, fifo_flop)

TEST LEVELS (per-test depth):
    basic (3-5 min):   Quick verification during development
    medium (8-12 min): Integration testing for CI/branches
    full (20-35 min):  Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~5 min) - smoke test (one mode, one clock ratio)
    FUNC: 9 tests (~60 min) - functional coverage - DEFAULT
    FULL: 48 tests (~6 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 mode × 1 ratio × 1 level = 1 test
    FUNC: 3 modes × 1 ratio × 3 levels = 9 tests
    FULL: 3 modes × 4 ratios × 4 depths = 48 tests

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


@cocotb.test(timeout_time=5, timeout_unit="ms")  # Increased timeout for async testing
async def gaxi_async_test(dut):
    '''Test the GAXI Async Buffer comprehensively with FlexConfigGen randomizers'''
    # For async, we need to pass both clock signals
    tb = GaxiBufferTB(
        dut,
        wr_clk=dut.axi_wr_aclk,
        wr_rstn=dut.axi_wr_aresetn,
        rd_clk=dut.axi_rd_aclk,
        rd_rstn=dut.axi_rd_aresetn
    )

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

    tb.log.info(f"Running ASYNC test level: {test_level.upper()}")

    # Start both clocks with different periods
    wr_clk_period = int(os.environ.get('TEST_CLK_WR', '10'))
    rd_clk_period = int(os.environ.get('TEST_CLK_RD', '10'))

    tb.log.info(f"Starting clocks: WR={wr_clk_period}ns, RD={rd_clk_period}ns")
    await tb.start_clock('axi_wr_aclk', wr_clk_period, 'ns')
    await tb.start_clock('axi_rd_aclk', rd_clk_period, 'ns')

    # Reset sequence for async
    await tb.assert_reset()
    await tb.wait_clocks('axi_wr_aclk', 5)
    await tb.wait_clocks('axi_rd_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_wr_aclk', 5)
    await tb.wait_clocks('axi_rd_aclk', 5)

    tb.log.info(f"Starting {test_level.upper()} GAXI ASYNC test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained']
        packet_counts = {
            'simple_loops': 6 * tb.TEST_DEPTH,  # Slightly more for async
            'back_to_back': 20,
            'stress_test': 30
        }
        run_comprehensive_sweep = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'gaxi_stress', 'gaxi_realistic', 'moderate', 'chaotic'
        ]
        packet_counts = {
            'simple_loops': 10 * tb.TEST_DEPTH,
            'back_to_back': 40,
            'stress_test': 75
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 8 * tb.TEST_DEPTH
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
            'simple_loops': 15 * tb.TEST_DEPTH,
            'back_to_back': 60,
            'stress_test': 120
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 12 * tb.TEST_DEPTH
        run_stress_test = True

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Packet counts: {packet_counts}")

    # Calculate additional wait time based on clock ratio for async operations
    clk_ratio = max(wr_clk_period, rd_clk_period) / min(wr_clk_period, rd_clk_period)
    async_wait_multiplier = max(2, int(clk_ratio * 1.5))

    tb.log.info(f"Clock ratio: {clk_ratio:.2f}, async wait multiplier: {async_wait_multiplier}")

    # Run core tests with different randomizer configurations
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=20 * async_wait_multiplier  # More time for async
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

    # Async-specific test: Clock domain crossing stress test
    if test_level in ['medium', 'full']:
        tb.log.info("Running async clock domain crossing test...")
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'] // 2,
            delay_key='chaotic'  # Use chaotic timing for CDC stress
        )
        tb.log.info("✓ Completed CDC stress test")

    tb.log.info(f"✓ ALL {test_level.upper()} ASYNC TESTS PASSED!")


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def gaxi_async_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for GAXI async buffers.

    Generates 3 key scenarios for each async mode:
    1. Write to empty (CDC latency visible)
    2. Burst write until full (backpressure with CDC)
    3. Clock domain crossing behavior

    Environment Variables:
        ENABLE_WAVEDROM: Enable waveform generation (1/0, default: 0)
        TEST_MODE: Buffer mode (skid/fifo_mux/fifo_flop)
        TEST_CLK_WR: Write clock period (ns)
        TEST_CLK_RD: Read clock period (ns)
    """
    # Check if waveforms are enabled
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), skipping wavedrom test")
        return

    # Get test parameters
    mode = os.environ.get('TEST_MODE', 'skid')
    wr_clk_period = int(os.environ.get('TEST_CLK_WR', '10'))
    rd_clk_period = int(os.environ.get('TEST_CLK_RD', '12'))
    dut._log.info(f"=== GAXI Async WaveDrom Test: {mode} mode (wr={wr_clk_period}ns, rd={rd_clk_period}ns) ===")

    # Setup clocks and reset
    tb = GaxiBufferTB(
        dut,
        wr_clk=dut.axi_wr_aclk,
        wr_rstn=dut.axi_wr_aresetn,
        rd_clk=dut.axi_rd_aclk,
        rd_rstn=dut.axi_rd_aresetn
    )

    await tb.start_clock('axi_wr_aclk', wr_clk_period, 'ns')
    await tb.start_clock('axi_rd_aclk', rd_clk_period, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('axi_wr_aclk', 5)
    await tb.wait_clocks('axi_rd_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_wr_aclk', 5)
    await tb.wait_clocks('axi_rd_aclk', 5)

    # Setup WaveDrom - use write clock as reference
    field_config = get_gaxi_field_config(data_width=8)
    wave_generator = create_gaxi_wavejson_generator(field_config, signal_prefix="")

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config,
        debug_level=1
    )

    # Use write clock as reference for sampling
    wave_solver.add_clock_group('default', dut.axi_wr_aclk)

    # Bind signals
    wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_', field_config=field_config)
    wave_solver.auto_bind_signals('gaxi', signal_prefix='rd_', field_config=field_config)
    wave_solver.add_signal_binding('wr_clk', 'axi_wr_aclk')
    wave_solver.add_signal_binding('rd_clk', 'axi_rd_aclk')
    wave_solver.add_signal_binding('wr_rst_n', 'axi_wr_aresetn')
    wave_solver.add_signal_binding('rd_rst_n', 'axi_rd_aresetn')

    # Define constraints for async CDC scenarios
    # Scenario 1: Write to empty (shows CDC latency)
    write_empty = TemporalConstraint(
        name=f"{mode}_async_write_empty",
        events=[TemporalEvent("wr_start", SignalTransition("wr_valid", 0, 1))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=20,
        context_cycles_before=3,
        context_cycles_after=4,
        signals_to_show=[
            'wr_clk', 'rd_clk', '|',
            'wr_rst_n', 'rd_rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_data', 'rd_data', '~>', 'CDC')]
    )
    wave_solver.add_constraint(write_empty)

    # Scenario 2: Backpressure with CDC
    backpressure = TemporalConstraint(
        name=f"{mode}_async_backpressure",
        events=[TemporalEvent("full", SignalTransition("wr_ready", 1, 0))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=30,
        context_cycles_before=4,
        context_cycles_after=3,
        signals_to_show=[
            'wr_clk', 'rd_clk', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_ready', 'wr_valid', '->', 'blocked')]
    )
    wave_solver.add_constraint(backpressure)

    # Scenario 3: Continuous flow across CDC
    continuous = TemporalConstraint(
        name=f"{mode}_async_continuous",
        events=[TemporalEvent("flow", SignalTransition("wr_valid", 0, 1))],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=25,
        context_cycles_before=3,
        context_cycles_after=3,
        signals_to_show=[
            'wr_clk', 'rd_clk', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data']
        ],
        edges=[('wr_data', 'rd_data', '~>', 'CDC_flow')]
    )
    wave_solver.add_constraint(continuous)

    dut._log.info(f"✓ WaveDrom configured: 3 async CDC scenarios")

    # Scenario 1: Write to empty
    dut._log.info("=== Scenario 1: Write to empty (CDC latency) ===")
    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    dut.wr_data.value = 0
    await RisingEdge(dut.axi_wr_aclk)
    await RisingEdge(dut.axi_wr_aclk)

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_wr_aclk)

    dut.wr_valid.value = 1
    dut.wr_data.value = 0xA0
    await RisingEdge(dut.axi_wr_aclk)
    dut.wr_data.value = 0xA1
    await RisingEdge(dut.axi_wr_aclk)
    dut.wr_valid.value = 0

    # Wait for CDC propagation
    for _ in range(10):
        await RisingEdge(dut.axi_wr_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 1 captured")

    # Drain
    dut.rd_ready.value = 1
    for _ in range(6):
        await RisingEdge(dut.axi_rd_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_rd_aclk)

    # Scenario 2: Fill until backpressure
    dut._log.info("=== Scenario 2: Burst write until full (async CDC) ===")
    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_wr_aclk)

    dut.wr_valid.value = 1
    for i in range(8):
        dut.wr_data.value = 0xB0 + i
        await RisingEdge(dut.axi_wr_aclk)
    dut.wr_valid.value = 0

    # Wait for CDC
    for _ in range(8):
        await RisingEdge(dut.axi_wr_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 2 captured")

    # Drain
    dut.rd_ready.value = 1
    for _ in range(10):
        await RisingEdge(dut.axi_rd_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_rd_aclk)

    # Scenario 3: Continuous flow
    dut._log.info("=== Scenario 3: Continuous flow across CDC ===")
    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_wr_aclk)

    # Continuous writes with reads
    dut.rd_ready.value = 1
    for i in range(4):
        dut.wr_valid.value = 1
        dut.wr_data.value = 0xC0 + i
        await RisingEdge(dut.axi_wr_aclk)
        dut.wr_valid.value = 0
        for _ in range(2):
            await RisingEdge(dut.axi_wr_aclk)

    # Wait for CDC
    for _ in range(6):
        await RisingEdge(dut.axi_wr_aclk)
    dut.rd_ready.value = 0

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 3 captured")

    dut._log.info(f"✓ GAXI Async {mode} WaveDrom Complete: 3 CDC scenarios generated")


# WaveDrom test parameters - separate from functional tests
def generate_async_wavedrom_params():
    """
    Generate parameters for async WaveDrom-enabled tests.

    Returns a small set of configurations optimized for waveform generation:
    - Single clock ratio (10ns:12ns = 1.2x) to show CDC behavior
    - All three modes (skid, fifo_mux, fifo_flop)
    - Fixed width/depth for consistency
    """
    return [
        # data_width, depth, wr_clk_period, rd_clk_period, mode
        (8, 4, 10, 12, 'skid'),      # wr=10ns, rd=12ns (1.2x ratio)
        (8, 4, 10, 12, 'fifo_mux'),
        (8, 4, 10, 12, 'fifo_flop'),
    ]

wavedrom_async_params = generate_async_wavedrom_params()

@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period, mode", wavedrom_async_params)
def test_gaxi_buffer_async_wavedrom(request, data_width, depth, wr_clk_period, rd_clk_period, mode):
    """
    GAXI async buffer wavedrom test - generates CDC timing diagrams.

    This test is separate from functional tests and focuses on generating
    clean, readable WaveJSON diagrams showing:
    - Clock domain crossing behavior
    - CDC latency characteristics
    - Backpressure handling across domains
    - Dual-clock timing relationships

    Test generates 3 scenarios per mode:
    1. Write to empty (shows CDC latency)
    2. Backpressure with CDC
    3. Continuous flow across CDC
    """
    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """
    GAXI async buffer wavedrom test - generates CDC timing diagrams.

    This test is separate from functional tests and focuses on generating
    clean, readable WaveJSON diagrams showing:
    - Clock domain crossing behavior
    - CDC latency characteristics
    - Backpressure handling across domains
    - Dual-clock timing relationships

    Test generates 3 scenarios per mode:
    1. Write to empty (shows CDC latency)
    2. Backpressure with CDC
    3. Continuous flow across CDC
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # set up all of the test names based on async modules
    if mode == 'skid':
        dut_name = "gaxi_skid_buffer_async"
    else:
        dut_name = "gaxi_fifo_async"
    toplevel = dut_name

    # Get verilog sources based on mode for async versions
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_cmn'],  "find_first_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "find_last_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "leading_one_trailing_one.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_johnson.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "grayj2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_async.sv"),
    ]

    if mode == 'skid':
        verilog_sources.append(os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"))
        verilog_sources.append(os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer_async.sv"))

    # create a human readable test identifier with clock information
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wr_str = TBBase.format_dec(wr_clk_period, 3)
    rd_str = TBBase.format_dec(rd_clk_period, 3)

    # Calculate clock ratio for test name
    clk_ratio = max(wr_clk_period, rd_clk_period) / min(wr_clk_period, rd_clk_period)
    ratio_str = f"r{clk_ratio:.1f}".replace('.', 'p')  # r1p2 for 1.2x ratio

    test_name_plus_params = f"test_{worker_id}_gaxi_async_{mode}_w{w_str}_d{d_str}_wr{wr_str}_rd{rd_str}_{ratio_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=[rtl_dict['rtl_amba_includes']]

    # RTL parameters - Handle string parameters specially for Verilator
    rtl_parameters = {}

    # Add numeric parameters normally
    rtl_parameters['DATA_WIDTH'] = str(data_width)
    rtl_parameters['DEPTH'] = str(depth)

    # Add async-specific parameters
    rtl_parameters['N_FLOP_CROSS'] = '3'  # Standard 3-flop synchronizer

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"{mode}_async_wavedrom"'
    if 'fifo' in mode:
        rtl_parameters['REGISTERED'] = str(1) if mode == 'fifo_flop' else str(0)

    # Shorter timeout for wavedrom tests (focused scenarios)
    timeout_ms = 5000  # 5 seconds

    # Environment variables - ENABLE WAVEDROM!
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': 'wavedrom',  # Special level for wavedrom
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
        'ENABLE_WAVEDROM': '1',  # Enable WaveDrom generation!
        'TEST_MODE': mode,
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(wr_clk_period),
        'TEST_CLK_RD': str(rd_clk_period),
        'TEST_KIND': 'async',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "-Wno-TIMESCALEMOD",
    ]

    sim_args = []

    plusargs = []

    # Run with WaveDrom-specific test function
    run(
        python_search=[os.path.join(repo_root, 'bin')],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        compile_args=compile_args,
        sim_args=sim_args,
        plusargs=plusargs,
        waves=False,  # Disable FST - using WaveDrom instead
        testcase="gaxi_async_wavedrom_test",  # Run wavedrom test specifically!
    )


def generate_params():
    """
    Generate test parameters based on REG_LEVEL for async CDC testing.

    REG_LEVEL=GATE: 1 test (smoke test)
    REG_LEVEL=FUNC: 9 tests (functional coverage) - default
    REG_LEVEL=FULL: 48 tests (comprehensive validation)

    Clock Ratios Tested:
        1.0x: Same clocks (10:10) - basic CDC validation
        1.2x: (10:12) - typical async scenario
        1.5x: (8:12) - moderate ratio
        2.0x: (10:20) - high ratio stress test
        2.5x: (8:20) - extreme ratio (FULL only)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove it works with one clock ratio
        # 1 test: skid mode, 1.2x ratio (10:12), basic level
        return [
            (8, 4, 10, 12, 'skid', 'basic'),
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - all modes with one clock ratio at all test levels
        # 3 modes × 3 levels = 9 tests
        modes = ['skid', 'fifo_mux', 'fifo_flop']
        test_levels = ['basic', 'medium', 'full']

        # Use 1.2x ratio (10:12) - typical async scenario
        return list(product([8], [4], [10], [12], modes, test_levels))

    else:  # FULL
        # Comprehensive testing - all modes, multiple clock ratios, multiple depths
        # 3 modes × 4 ratios × 4 depths × full level = 48 tests
        modes = ['skid', 'fifo_mux', 'fifo_flop']
        depths = [4, 6, 8, 10]

        # Test meaningful clock ratio combinations
        clock_configs = [
            (10, 10),  # 1.0x - same clocks
            (10, 12),  # 1.2x - typical async
            (8, 12),   # 1.5x - moderate ratio
            (10, 20),  # 2.0x - high ratio
        ]

        params = []
        for mode, depth, (wr_clk, rd_clk) in product(modes, depths, clock_configs):
            params.append((8, depth, wr_clk, rd_clk, mode, 'full'))

        return params


params = generate_params()

@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period, mode, test_level", params)
def test_gaxi_buffer_async(request, data_width, depth, wr_clk_period, rd_clk_period, mode, test_level):
    """
    Parameterized GAXI async buffer test with configurable test levels and independent clock domains.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (3-5 min)
    - medium: Integration testing (8-12 min)
    - full: Comprehensive validation (20-35 min)

    Clock configurations test various CDC scenarios:
    - Same clocks: wr_clk = rd_clk (basic CDC validation)
    - Slow write/fast read: wr_clk > rd_clk (backpressure scenarios)
    - Fast write/slow read: wr_clk < rd_clk (buffering scenarios)
    - Extreme ratios: up to 2.5x difference (stress testing)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':  'rtl/common',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    # set up all of the test names based on async modules
    if mode == 'skid':
        dut_name = "gaxi_skid_buffer_async"
    else:
        dut_name = "gaxi_fifo_async"
    toplevel = dut_name

    # Get verilog sources based on mode for async versions
    #
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_cmn'],  "find_first_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "find_last_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "leading_one_trailing_one.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "counter_johnson.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "grayj2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_async.sv"),
    ]

    if mode == 'skid':
        verilog_sources.append(os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"))
        verilog_sources.append(os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer_async.sv"))

    # create a human readable test identifier with clock information
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wr_str = TBBase.format_dec(wr_clk_period, 3)
    rd_str = TBBase.format_dec(rd_clk_period, 3)

    # Calculate clock ratio for test name
    clk_ratio = max(wr_clk_period, rd_clk_period) / min(wr_clk_period, rd_clk_period)
    ratio_str = f"r{clk_ratio:.1f}".replace('.', 'p')  # r2p0 for 2.0x ratio

    test_name_plus_params = f"test_{worker_id}_gaxi_async_{mode}_w{w_str}_d{d_str}_wr{wr_str}_rd{rd_str}_{ratio_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=[rtl_dict['rtl_amba_includes']]

    # RTL parameters - Handle string parameters specially for Verilator
    rtl_parameters = {}

    # Add numeric parameters normally
    for param_name in ['data_width', 'depth']:
        if param_name in locals():
            rtl_parameters[param_name.upper()] = str(locals()[param_name])

    # Add async-specific parameters
    rtl_parameters['N_FLOP_CROSS'] = '3'  # Standard 3-flop synchronizer

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"{mode}_async_{test_level}"'
    if 'fifo' in mode:
        rtl_parameters['REGISTERED'] = str(1) if mode == 'fifo_flop' else str(0)

    # Adjust timeout based on test level and clock ratio
    timeout_multipliers = {'basic': 1.5, 'medium': 3, 'full': 6}  # Higher for async
    base_timeout = 3000  # 3 seconds base for async
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * clk_ratio)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)  # Dynamic timeout
    }

    # Add test parameters for async testing
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)  # Write clock period
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)  # Read clock period
    extra_env['TEST_MODE'] = mode
    extra_env['TEST_KIND'] = 'async'  # Important: tells TB this is async

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
    print(f"Running {test_level.upper()} ASYNC test: {mode} mode")
    print(f"Config: depth={depth}, width={data_width}")
    print(f"Clocks: WR={wr_clk_period}ns, RD={rd_clk_period}ns (ratio: {clk_ratio:.1f}x)")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
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
        print(f"✓ {test_level.upper()} ASYNC test PASSED: {mode} mode (WR:{wr_clk_period}ns/RD:{rd_clk_period}ns)")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} ASYNC test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
