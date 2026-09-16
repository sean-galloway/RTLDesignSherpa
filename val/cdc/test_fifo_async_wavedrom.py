# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_async_wavedrom
# Purpose: WaveDrom waveform generation for fifo_async showcasing Gray code CDC
#
# Documentation: docs/markdown/rtl-common/fifo_async.md
# Subsystem: tests
#
# Author: Claude Code (sean galloway)
# Created: 2025-10-20

"""
WaveDrom Waveform Generation for Async FIFO (Standard Gray Code)

This test generates high-quality waveforms showcasing the fifo_async
implementation using standard Gray code for clock domain crossing.

KEY FEATURES TO SHOWCASE:
1. Standard Gray code pointer synchronization
2. Power-of-2 depth requirement
3. Efficient resource usage (logarithmic pointer width)
4. Cross-domain pointer transitions
5. Comparison point for the USE_JOHNSON=1 (Johnson counter) configuration

WAVEDROM SCENARIOS (v1.2 Requirements):
- Quality over quantity: 3-4 focused scenarios
- Clock signals ALWAYS first
- 2-3 initial setup cycles
- Meaningful signal grouping
- Arrows show causal relationships only

SCENARIOS:
1. Basic write-fill-read-empty cycle (standard operation)
2. Cross-domain Gray code synchronization
3. Power-of-2 depth utilization
4. Almost-full/almost-empty flag operation
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.tbbase import TBBase
from TBClasses.fifo.fifo_buffer import FifoBufferTB
from TBClasses.shared.utilities import get_wavejson_dir, get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig
from TBClasses.cdc.fifo_async_wavedrom_tb import FifoAsyncWaveDromTB

@cocotb.test(timeout_time=500, timeout_unit="us")
async def fifo_async_wavedrom_test(dut):
    """Generate WaveDrom waveforms for fifo_async showcasing Gray code CDC - per scenario."""
    import shutil
    import subprocess

    tb = FifoAsyncWaveDromTB(
        dut,
        wr_clk=dut.wr_clk,
        wr_rstn=dut.wr_rst_n,
        rd_clk=dut.rd_clk,
        rd_rstn=dut.rd_rst_n
    )

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.start_clock('wr_clk', tb.TEST_CLK_WR, 'ns')
    await tb.start_clock('rd_clk', tb.TEST_CLK_RD, 'ns')

    await tb.assert_reset()
    await tb.wait_clocks('wr_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('wr_clk', 5)

    tb.setup_wavedrom()

    # Output directory for waveforms
    output_dir = get_wavejson_dir("fifo_async", os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_write_fill_read_empty, "fifo_async_write_fill_read_empty.json"),
        (tb.scenario_gray_code_sync, "fifo_async_gray_code_sync.json"),
        (tb.scenario_power_of_2_depth, "fifo_async_power_of_2_depth.json"),
    ]
    # TEST_LEVEL gates HOW MANY scenarios are emitted, never the content of
    # any one of them. gate emits the first two as a smoke check.
    _lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    if _lvl not in ('gate', 'func', 'full'):
        _lvl = 'gate'
    if _lvl == 'gate':
        scenarios = scenarios[:2]

    try:
        for scenario_method, output_filename in scenarios:
            # Reset and prepare for this scenario
            await tb.assert_reset()
            await tb.wait_clocks('wr_clk', 3)
            await tb.deassert_reset()
            await tb.wait_clocks('wr_clk', 2)

            # Clear previous constraint windows
            if tb.wave_solver:
                tb.wave_solver.clear_windows()

            # Start sampling for this scenario
            if tb.wave_solver:
                await tb.wave_solver.start_sampling()

            # Run the scenario
            await scenario_method()
            await tb.wait_clocks('wr_clk', 2)

            # Stop and generate waveform
            if tb.wave_solver:
                await tb.wave_solver.stop_sampling()
                await tb.wave_solver.solve_and_generate()

                results = tb.wave_solver.get_results()
                solutions = results.get('solutions', [])

                if solutions:
                    # Find the most recently generated JSON file
                    import glob
                    json_files = glob.glob("fifo_async_capture_*.json")
                    if json_files:
                        # Sort by modification time, get most recent
                        src_file = max(json_files, key=os.path.getmtime)
                        dest_file = os.path.join(output_dir, output_filename)

                        if os.path.exists(src_file):
                            shutil.move(src_file, dest_file)
                            tb.log.info(f"✓ Generated waveform: {dest_file}")

                            # Trim dead time from waveform
                            trim_script = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
                                                       'bin', 'trim_wavedrom.py')
                            if os.path.exists(trim_script):
                                result = subprocess.run([
                                    'python3', trim_script, dest_file, '-b', '2', '-a', '2'
                                ], capture_output=True, text=True,
                                )
                                if result.returncode == 0:
                                    tb.log.info(f"✓ Trimmed waveform: {output_filename}")
                                else:
                                    tb.log.warning(f"Trimming failed: {result.stderr}")
                        else:
                            tb.log.warning(f"Source file not found: {src_file}")
                    else:
                        tb.log.warning(f"No JSON files found for scenario: {output_filename}")
                else:
                    tb.log.warning(f"No solution generated for scenario: {output_filename}")

        tb.log.info("🎉 FIFO ASYNC WAVEDROM GENERATION COMPLETE! 🎉")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('wr_clk', 10)

def _wavedrom_grid(gate, func, full):
    """REG_LEVEL grid for a wavedrom generator. Content of a given diagram is
    identical at every level; only how many scenarios run varies, so the
    committed JSON never depends on how the suite was invoked."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    return {'GATE': gate, 'FULL': full}.get(reg_level, func)


@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period",
                         _wavedrom_grid([(8, 8, 10, 12)],
                                        [(8, 8, 10, 12), (16, 16, 10, 12)],
                                        [(8, 8, 10, 12), (16, 16, 10, 12),
                                         (32, 8, 10, 20)]))
def test_fifo_async_wavedrom(request, data_width, depth, wr_clk_period, rd_clk_period):
    """Pytest wrapper for fifo_async WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cdc': 'rtl/cdc',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "fifo_async"
    toplevel = dut_name

    # Take the filelist; never hand-list. This test hand-listed rtl/common paths
    # and broke silently when the CDC modules moved to rtl/cdc.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/cdc/filelists/fifo_async.f")

    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_w{w_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': '0',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        # PINNED, not random: a wavedrom run must hit every scenario its
        # constraints require, and the randomizers' valid/ready delays decide
        # whether a complete sequence fits the capture window. A random seed
        # makes that a coin flip (AMBA-WAVEDROM-FLAKY). Override with SEED=<n>.
        'SEED': os.environ.get('SEED', '12345'),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(wr_clk_period),
        'TEST_CLK_RD': str(rd_clk_period),
        'TEST_MODE': 'fifo_mux',
        'TEST_KIND': 'async',
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running FIFO Async WaveDrom Generation")
    print(f"Showcasing Gray Code CDC Mechanism")
    print(f"Width: {data_width}, Depth: {depth}")
    print(f"Write CLK: {wr_clk_period}ns, Read CLK: {rd_clk_period}ns")
    print(f"{'='*60}")

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
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ FIFO Async WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ FIFO Async WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
