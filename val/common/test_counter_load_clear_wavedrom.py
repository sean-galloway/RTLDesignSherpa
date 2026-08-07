# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterLoadClearWaveDromTB
# Purpose: Counter Load Clear WaveDrom Test - Showcases load, clear, and done functionality
#
# Documentation: docs/markdown/rtl-common/counter_load_clear.md
# Subsystem: tests
#
# Author: RTL Design Sherpa AI
# Created: 2025-10-20

"""
Counter Load Clear WaveDrom Test

This test generates high-quality waveforms showcasing the counter_load_clear properties:
- Runtime-loadable match value for flexible counting
- Immediate clear to 0 (highest priority)
- Done flag when count reaches match value
- Automatic wraparound after reaching match
- Independent load and count operations

KEY FEATURES:
- Load: Runtime configuration of match value
- Clear: Immediate reset to 0 (overrides increment)
- Done: Combinational flag for loop termination
- Wraparound: Automatic return to 0 after match

WaveDrom Output:
    docs/markdown/assets/WAVES/staged/counter_load_clear/counter_load_clear_*.json

Generate Waveforms:
    pytest val/common/test_counter_load_clear_wavedrom.py -v
"""

import os
import sys
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb_test.simulator import run
import pytest
import math

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.counter_load_clear_wavedrom_tb import CounterLoadClearWaveDromTB
from TBClasses.shared.utilities import get_wavejson_dir, get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig


@cocotb.test(timeout_time=500, timeout_unit="us")
async def counter_load_clear_wavedrom_test(dut):
    """Generate WaveDrom waveforms for counter_load_clear showcasing load/clear/done - per scenario."""
    import shutil
    import subprocess

    tb = CounterLoadClearWaveDromTB(dut)

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()
    tb.setup_wavedrom()

    # Output directory for waveforms
    output_dir = get_wavejson_dir("counter_load_clear", os.path.dirname(os.path.abspath(__file__)))
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_load_and_count, "counter_load_clear_load_and_count.json"),
        (tb.scenario_clear_operation, "counter_load_clear_clear_operation.json"),
        (tb.scenario_dynamic_match, "counter_load_clear_dynamic_match.json"),
        (tb.scenario_wraparound, "counter_load_clear_wraparound.json"),
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
                    json_files = glob.glob("counter_load_clear_capture_*.json")
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

        tb.log.info("🎉 COUNTER LOAD CLEAR WAVEDROM GENERATION COMPLETE! 🎉")

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

# MAX=8 is NOT a legal member of this grid. loadval is [$clog2(MAX)-1:0], so
# MAX=8 gives a 3-bit port, and scenario_clear_operation loads a match value of
# 8 -- which needs 4 bits, i.e. MAX >= 16. It also has no meaning there: a
# counter that wraps at 8 can never reach a match of 8. Adding it produced
# "OverflowError: Int value (8) out of range for assignment of 3-bit signal",
# and only at FULL, where nothing else in the area runs that width.
@pytest.mark.parametrize("max_value",
                         _wavedrom_grid([16], [16, 32], [16, 32, 64]))
def test_counter_load_clear_wavedrom(request, max_value):
    """Pytest wrapper for counter_load_clear WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "counter_load_clear"
    toplevel = dut_name

    # Sources come from the filelist, never a hand-listed array: the array
    # here omitted the include dirs and reset_defs.svh the filelist carries,
    # and a dependency added to the module is invisible to it ([[filelists]]).
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_load_clear.f')

    m_str = TBBase.format_dec(max_value, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_m{m_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'MAX': str(max_value)
    }

    extra_env = {
        # Depth knob. Without this the TB reads TEST_LEVEL's default on every
        # run, so its gate/func/full branches are unreachable no matter what
        # REG_LEVEL selects ([[test-runner]]: both mechanisms are required,
        # and a mechanism nothing exports is not one).
        'TEST_LEVEL': os.environ.get('REG_LEVEL', 'FUNC').lower(),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        # Wavedrom generators produce the wave JSON the docs embed, so their
        # stimulus must be REPRODUCIBLE: a random seed per run means the
        # committed diagram changes for no reason. Fixed default, still
        # overridable with SEED=... for a one-off experiment.
        'SEED': os.environ.get('SEED', '12345'),
        'TEST_MAX_VALUE': str(max_value),
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]


    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this

    # the run produces no coverage.dat at all and `make coverage-report`

    # silently reports 0.0% from 0 merged files.

    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running Counter Load Clear WaveDrom Generation")
    print(f"Showcasing Load, Clear, Done, and Wraparound")
    print(f"MAX: {max_value}")
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
        print(f"✓ Counter Load Clear WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Counter Load Clear WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
