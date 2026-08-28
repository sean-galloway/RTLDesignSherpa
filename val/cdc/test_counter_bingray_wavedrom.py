# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterBinGrayWaveDromTB
# Purpose: Binary-Gray Counter WaveDrom Test - Showcases dual-output Gray code counter
#
# Documentation: docs/markdown/rtl-common/counter_bingray.md
# Subsystem: tests
#
# Author: RTL Design Sherpa AI
# Created: 2025-10-20

"""
Binary-Gray Counter WaveDrom Test

This test generates high-quality waveforms showcasing the dual-output counter:
- Binary counter output (normal 0→1→2→3→...)
- Gray code output (single-bit transitions)
- Counter_bin_next lookahead signal
- CDC-safe Gray code properties
- Relationship between binary and Gray encoding

KEY FEATURE: This counter is the foundation of fifo_async (standard async FIFO)!
             Shows why Gray code prevents metastability in clock domain crossing.

WaveDrom Output:
    val/common/local_sim_build/test_counter_bingray_wavedrom_*/bingray_counter_*.json

Generate Waveforms:
    pytest val/common/test_counter_bingray_wavedrom.py -v
"""

import os
import sys
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb_test.simulator import run
import pytest

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.cdc.counter_bingray_wavedrom_tb import CounterBinGrayWaveDromTB
from TBClasses.shared.utilities import get_wavejson_dir, get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def counter_bingray_wavedrom_test(dut):
    """WaveDrom test for Binary-Gray Counter - generates separate waveforms per scenario"""
    import os
    import shutil
    import subprocess

    tb = CounterBinGrayWaveDromTB(dut)

    # Setup
    await tb.setup_clock()
    await tb.reset_dut()

    # Setup WaveDrom
    tb.setup_wavedrom()

    # Create output directory
    output_dir = get_wavejson_dir("counter_bingray", os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_binary_vs_gray, "bingray_counter_binary_vs_gray.json"),
        (tb.scenario_single_bit_transitions, "bingray_counter_single_bit_transitions.json"),
        (tb.scenario_lookahead_signal, "bingray_counter_lookahead.json"),
        (tb.scenario_enable_and_reset, "bingray_counter_enable_reset.json"),
    ]
    # TEST_LEVEL gates HOW MANY scenarios are emitted, never the content of
    # any one of them. gate emits the first two as a smoke check; func and
    # full emit the complete set, so the normal regeneration path always
    # writes every diagram.
    _lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    if _lvl not in ('gate', 'func', 'full'):
        _lvl = 'gate'
    if _lvl == 'gate':
        scenarios = scenarios[:2]

    try:
        for scenario_method, output_filename in scenarios:
            tb.log.info(f"\n{'='*60}")
            tb.log.info(f"Generating waveform: {output_filename}")
            tb.log.info(f"{'='*60}")

            # Reset and prepare for this scenario
            await tb.reset_dut()
            await tb.wait_cycles(2)

            # Clear previous constraint windows
            if tb.wave_solver:
                tb.wave_solver.clear_windows()

            # Start sampling for this scenario
            if tb.wave_solver:
                await tb.wave_solver.start_sampling()

            # Run the scenario
            await scenario_method()
            await tb.wait_cycles(2)  # Small buffer at end

            # Stop and generate waveform
            if tb.wave_solver:
                await tb.wave_solver.stop_sampling()
                await tb.wave_solver.solve_and_generate()

                results = tb.wave_solver.get_results()
                solutions = results.get('solutions', [])

                if solutions and solutions[0].filename:
                    # Move and rename to match documentation
                    src_file = solutions[0].filename
                    dest_file = os.path.join(output_dir, output_filename)

                    # Check if source file exists, otherwise look in sim_build
                    if not os.path.exists(src_file):
                        # Try to find in sim build directory
                        basename = os.path.basename(src_file)
                        sim_build_file = basename
                        if os.path.exists(sim_build_file):
                            src_file = sim_build_file

                    if os.path.exists(src_file):
                        shutil.move(src_file, dest_file)
                        tb.log.info(f"  Generated: {dest_file}")

                        # Trim dead time from waveform
                        trim_script = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
                                                   'bin', 'trim_wavedrom.py')
                        if os.path.exists(trim_script):
                            result = subprocess.run([
                                'python3', trim_script, dest_file, '-b', '2', '-a', '2'
                            ], capture_output=True, text=True,
                            )
                            if result.returncode == 0:
                                tb.log.info(f"  Trimmed: {output_filename}")
                            else:
                                tb.log.warning(f"  Trim failed: {result.stderr}")
                    else:
                        tb.log.warning(f"  Source file not found: {src_file}")
                else:
                    tb.log.warning(f"  No solution generated for {output_filename}")

        tb.log.info("\n🎉 BINARY-GRAY COUNTER WAVEDROM GENERATION COMPLETE! 🎉")
        tb.log.info(f"Generated {len(scenarios)} waveform files in: {output_dir}")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_cycles(10)

    tb.log.info(f"✓ Binary-Gray Counter WaveDrom test PASSED{tb.get_time_ns_str()}")
    return True

def _wavedrom_grid(gate, func, full):
    """REG_LEVEL grid for a wavedrom generator. Content of a given diagram is
    identical at every level; only how many scenarios run varies, so the
    committed JSON never depends on how the suite was invoked."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    return {'GATE': gate, 'FULL': full}.get(reg_level, func)


@pytest.mark.parametrize("wave_cfg", _wavedrom_grid([0], [0, 1], [0, 1, 2]))
def test_counter_bingray_wavedrom(request, wave_cfg):
    """
    Pytest entry point for Binary-Gray Counter WaveDrom test

    Generates high-quality waveforms showcasing:
    - Binary vs Gray code comparison
    - Single-bit transitions (CDC safety)
    - Lookahead signal (counter_bin_next)
    - Enable and reset control

    Output: bingray_counter_*.json files in sim_build directory
    """
    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT configuration
    dut_name = "counter_bingray"
    # Take the filelist; never hand-list. This test hand-listed rtl/common and
    # broke silently when counter_bingray moved to rtl/cdc.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/cdc/filelists/counter_bingray.f")
    toplevel = dut_name

    # Test parameters
    width = 4  # WIDTH=4 gives 16 states (good for visualization)
    test_name = f"test_counter_bingray_wavedrom_w{width}"

    # Directories
    sim_build = sim_build_path(tests_dir, test_name + f'_w{wave_cfg}')
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width)
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '1'
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    print(f"\n{'='*60}")
    print(f"Binary-Gray Counter WaveDrom Test")
    print(f"WIDTH={width}, Max Value={2**width-1}")
    print(f"Output: {sim_build}/bingray_counter_*.json")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ WaveDrom test PASSED")
        print(f"WaveJSON files generated in: {sim_build}/")
    except Exception as e:
        print(f"✗ WaveDrom test FAILED: {str(e)}")
        print(f"Logs: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise
