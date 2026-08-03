# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterFreqInvariantWaveDromTB
# Purpose: Counter Freq Invariant WaveDrom Test - Showcases frequency-agnostic microsecond timing
#
# Documentation: docs/markdown/rtl-common/counter_freq_invariant.md
# Subsystem: tests
#
# Author: RTL Design Sherpa AI
# Created: 2025-10-20

"""
Counter Freq Invariant WaveDrom Test

This test generates high-quality waveforms showcasing the counter_freq_invariant properties:
- Frequency-invariant 1MHz tick generation
- Clock frequency selection via lookup table (100MHz-2GHz)
- Runtime frequency reconfiguration
- Microsecond counter with configurable width
- Synchronous reset control

KEY FEATURES:
- Prescaler: Divides arbitrary clock to 1MHz tick rate
- Tick Pulse: Single-cycle pulse every microsecond
- Freq Select: 68-entry lookup table for 100MHz-2GHz
- Counter: Increments on each tick (microsecond count)

WaveDrom Output:
    docs/markdown/assets/WAVES/staged/counter_freq_invariant/counter_freq_invariant_*.json

Generate Waveforms:
    pytest val/common/test_counter_freq_invariant_wavedrom.py -v
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
from TBClasses.common.counter_freq_invariant_wavedrom_tb import CounterFreqInvariantWaveDromTB
from TBClasses.shared.utilities import get_wavejson_dir, get_paths, create_view_cmd

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig


@cocotb.test(timeout_time=1000, timeout_unit="us")
async def counter_freq_invariant_wavedrom_test(dut):
    """Generate WaveDrom waveforms for counter_freq_invariant showcasing frequency-agnostic timing - per scenario."""
    import shutil
    import subprocess

    tb = CounterFreqInvariantWaveDromTB(dut)

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()
    tb.setup_wavedrom()

    # Output directory for waveforms
    output_dir = get_wavejson_dir("counter_freq_invariant", os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_basic_tick_generation, "counter_freq_invariant_basic_ticks.json"),
        (tb.scenario_freq_change, "counter_freq_invariant_freq_change.json"),
        (tb.scenario_sync_reset, "counter_freq_invariant_sync_reset.json"),
        (tb.scenario_counter_increment, "counter_freq_invariant_counter_increment.json"),
    ]
    # TEST_LEVEL for a wavedrom generator gates HOW MANY scenarios are
    # produced, never the content of any one of them: the committed JSON for a
    # given scenario must be byte-identical at every level, or the diagrams in
    # the docs would depend on how the suite was invoked. gate emits the first
    # two as a smoke check; func and full emit the complete set, so the normal
    # regeneration path (default REG_LEVEL=FUNC) always writes every diagram.
    _lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    if _lvl not in ('gate', 'func', 'full'):
        _lvl = 'gate'
    if _lvl == 'gate':
        scenarios = scenarios[:2]

    try:
        for scenario_method, output_filename in scenarios:
            # Reset and prepare for this scenario
            await tb.assert_reset()
            await tb.wait_clocks('clk', 3)
            await tb.deassert_reset()
            await tb.wait_clocks('clk', 2)

            # Clear previous constraint windows
            if tb.wave_solver:
                tb.wave_solver.clear_windows()

            # Start sampling for this scenario
            if tb.wave_solver:
                await tb.wave_solver.start_sampling()

            # Run the scenario
            await scenario_method()
            await tb.wait_clocks('clk', 2)

            # Stop and generate waveform
            if tb.wave_solver:
                await tb.wave_solver.stop_sampling()
                await tb.wave_solver.solve_and_generate()

                results = tb.wave_solver.get_results()
                solutions = results.get('solutions', [])

                if solutions:
                    # Find the most recently generated JSON file
                    import glob
                    json_files = glob.glob("counter_freq_invariant_capture_*.json")
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

        tb.log.info("🎉 COUNTER FREQ INVARIANT WAVEDROM GENERATION COMPLETE! 🎉")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('clk', 10)

def _wavedrom_grid(gate, func, full):
    """REG_LEVEL grid for a wavedrom generator.

    These produce the wave JSON the docs embed rather than a pass/fail check,
    so the depth rule sits differently for them -- but a diagram set still has
    a cheap and a comprehensive form, so the grid is not optional
    (test-runner.md: both mechanisms are a hard requirement).
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    return {'GATE': gate, 'FULL': full}.get(reg_level, func)

@pytest.mark.parametrize("counter_width",
                         _wavedrom_grid([16], [16, 20], [8, 16, 20, 24]))
def test_counter_freq_invariant_wavedrom(request, counter_width):
    """Pytest wrapper for counter_freq_invariant WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "counter_freq_invariant"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    cw_str = TBBase.format_dec(counter_width, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_cw{cw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'COUNTER_WIDTH': str(counter_width),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        # Wavedrom generators produce the wave JSON the docs embed, so their
        # stimulus must be REPRODUCIBLE: a random seed per run means the
        # committed diagram changes for no reason. Fixed default, still
        # overridable with SEED=... for a one-off experiment.
        'SEED': os.environ.get('SEED', '12345'),
        'TEST_COUNTER_WIDTH': str(counter_width),
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
    print(f"Running Counter Freq Invariant WaveDrom Generation")
    print(f"Showcasing Frequency-Agnostic Microsecond Timing")
    print(f"Counter Width: {counter_width}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ Counter Freq Invariant WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Counter Freq Invariant WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
