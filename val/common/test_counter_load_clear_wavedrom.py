# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterLoadClearWaveDromTB
# Purpose: Counter Load Clear WaveDrom Test - Showcases load, clear, and done functionality
#
# Documentation: docs/markdown/RTLCommon/counter_load_clear.md
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
    docs/markdown/assets/WAVES/counter_load_clear/counter_load_clear_*.json

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
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig


class CounterLoadClearWaveDromTB(TBBase):
    """Extended testbench for Counter Load Clear with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Load operation for runtime match value configuration
    - Clear operation for immediate reset
    - Done flag for match detection
    - Wraparound behavior
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.MAX_VALUE = self.convert_to_int(os.environ.get('TEST_MAX_VALUE', '16'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        random.seed(self.SEED)

        # Calculate count width
        self.COUNT_WIDTH = math.ceil(math.log2(self.MAX_VALUE)) if self.MAX_VALUE > 1 else 1

        self.log.info(f"Counter Load Clear WaveDrom TB initialized{self.get_time_ns_str()}")
        self.log.info(f"MAX_VALUE={self.MAX_VALUE}, COUNT_WIDTH={self.COUNT_WIDTH}{self.get_time_ns_str()}")

        # Signal mappings
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.clear = self.dut.clear
        self.increment = self.dut.increment
        self.load = self.dut.load
        self.loadval = self.dut.loadval
        self.count = self.dut.count
        self.done = self.dut.done

        # Clock configuration
        self.clock_period = 10  # 10ns = 100MHz

        # WaveDrom infrastructure
        self.wave_generator = None
        self.wave_solver = None

    async def setup_clocks_and_reset(self):
        """Start clock and perform reset"""
        # Start clock
        await self.start_clock('clk', self.clock_period, 'ns')

        # Assert reset
        await self.assert_reset()
        await self.wait_clocks('clk', 5)

        # Deassert reset
        await self.deassert_reset()
        await self.wait_clocks('clk', 2)

    async def assert_reset(self):
        """Assert reset signal"""
        self.rst_n.value = 0
        self.clear.value = 0
        self.increment.value = 0
        self.load.value = 0
        self.loadval.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1
        self.clear.value = 0
        self.increment.value = 0
        self.load.value = 0
        self.loadval.value = 0

    def setup_wavedrom(self):
        """Set up WaveDrom system for counter_load_clear waveform capture"""
        try:
            self.log.info("Setting up WaveDrom for Counter Load Clear...")

            # Create field configuration
            self.field_config_wave = FieldConfig.from_dict(
                field_dict={
                    'loadval': {'bits': self.COUNT_WIDTH, 'default': 0},
                    'count': {'bits': self.COUNT_WIDTH, 'default': 0},
                },
                lsb_first=True
            )

            # Create WaveJSON generator
            self.wave_generator = WaveJSONGenerator(debug_level=2)

            # WAVEDROM REQUIREMENT v1.2: Signal grouping MANDATORY
            # Group 1: Clocks and Resets (ALWAYS FIRST)
            clock_signals = ['clk', 'rst_n']
            self.wave_generator.add_interface_group("Clocks & Reset", clock_signals)

            # Group 2: Control
            control_signals = ['clear', 'increment', 'load', 'loadval']
            self.wave_generator.add_interface_group("Control", control_signals)

            # Group 3: Counter Outputs
            counter_signals = ['count', 'done']
            self.wave_generator.add_interface_group("Counter Outputs", counter_signals)

            # Create temporal constraint solver
            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.field_config_wave
            )

            # Add clock group
            self.wave_solver.add_clock_group(
                name="clk",
                clock_signal=self.clk,
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.field_config_wave
            )

            # Define signal mappings
            counter_signals = {
                'clk': 'clk',
                'rst_n': 'rst_n',
                'clear': 'clear',
                'increment': 'increment',
                'load': 'load',
                'loadval': 'loadval',
                'count': 'count',
                'done': 'done',
            }

            self.wave_solver.add_interface("counter", counter_signals, field_config=self.field_config_wave)

            # Add dummy constraint to trigger waveform generation
            load_constraint = TemporalConstraint(
                name="counter_load_clear_capture",
                events=[
                    TemporalEvent("load_high", SignalTransition("counter_load", 0, 1))
                ],
                temporal_relation=TemporalRelation.SEQUENCE,
                max_window_size=100,
                required=False,
                max_matches=10,
                clock_group="clk",
                signals_to_show=['counter_clk', 'counter_rst_n', 'counter_clear', 'counter_increment',
                                'counter_load', 'counter_loadval', 'counter_count', 'counter_done']
            )
            load_constraint.skip_boundary_detection = True
            self.wave_solver.add_constraint(load_constraint)

            self.log.info("✓ WaveDrom setup complete for Counter Load Clear")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            import traceback
            traceback.print_exc()
            self.wave_solver = None
            self.wave_generator = None

    async def scenario_load_and_count(self):
        """
        SCENARIO 1: Load match value and count to done

        Demonstrates loading a match value and counting up to it.
        """
        self.log.info("=== Scenario 1: Load and Count to Done ===")

        await self.wait_clocks('clk', 3)

        # Load match value of 5
        self.loadval.value = 5
        self.load.value = 1
        await RisingEdge(self.clk)
        self.load.value = 0
        await self.wait_clocks('clk', 2)

        # Count up to match value
        self.increment.value = 1
        for i in range(7):  # Count past match to show wraparound
            await RisingEdge(self.clk)
            count_val = int(self.count.value)
            done_val = int(self.done.value)
            self.log.info(f"Count: {count_val}, Done: {done_val}{self.get_time_ns_str()}")

        self.increment.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 1 complete")

    async def scenario_clear_operation(self):
        """
        SCENARIO 2: Clear operation

        Demonstrates immediate clear to 0 (overrides increment).
        """
        self.log.info("=== Scenario 2: Clear Operation ===")

        await self.wait_clocks('clk', 3)

        # Load match value of 8
        self.loadval.value = 8
        self.load.value = 1
        await RisingEdge(self.clk)
        self.load.value = 0
        await self.wait_clocks('clk', 2)

        # Count up partway
        self.increment.value = 1
        for i in range(4):
            await RisingEdge(self.clk)
            count_val = int(self.count.value)
            self.log.info(f"Count: {count_val}{self.get_time_ns_str()}")

        # Assert clear (should go to 0 immediately)
        self.clear.value = 1
        await RisingEdge(self.clk)
        count_val = int(self.count.value)
        self.log.info(f"After clear: Count={count_val}{self.get_time_ns_str()}")

        self.clear.value = 0
        self.increment.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 2 complete")

    async def scenario_dynamic_match(self):
        """
        SCENARIO 3: Dynamic match value change

        Demonstrates changing the match value mid-count.
        """
        self.log.info("=== Scenario 3: Dynamic Match Value Change ===")

        await self.wait_clocks('clk', 3)

        # Load initial match value of 4
        self.loadval.value = 4
        self.load.value = 1
        await RisingEdge(self.clk)
        self.load.value = 0
        await self.wait_clocks('clk', 2)

        # Count to 2
        self.increment.value = 1
        for i in range(2):
            await RisingEdge(self.clk)
            count_val = int(self.count.value)
            self.log.info(f"Count: {count_val}{self.get_time_ns_str()}")

        # Change match value to 6 mid-count
        self.loadval.value = 6
        self.load.value = 1
        await RisingEdge(self.clk)
        self.load.value = 0
        self.log.info(f"Changed match value to 6{self.get_time_ns_str()}")

        # Continue counting to new match
        for i in range(6):
            await RisingEdge(self.clk)
            count_val = int(self.count.value)
            done_val = int(self.done.value)
            self.log.info(f"Count: {count_val}, Done: {done_val}{self.get_time_ns_str()}")

        self.increment.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 3 complete")

    async def scenario_wraparound(self):
        """
        SCENARIO 4: Wraparound demonstration

        Shows automatic wraparound to 0 after reaching match value.
        """
        self.log.info("=== Scenario 4: Wraparound Behavior ===")

        await self.wait_clocks('clk', 3)

        # Load match value of 3
        self.loadval.value = 3
        self.load.value = 1
        await RisingEdge(self.clk)
        self.load.value = 0
        await self.wait_clocks('clk', 2)

        # Count through multiple wraparounds
        self.increment.value = 1
        for cycle in range(12):  # Multiple full cycles
            await RisingEdge(self.clk)
            count_val = int(self.count.value)
            done_val = int(self.done.value)
            self.log.info(f"Cycle {cycle}: Count={count_val}, Done={done_val}{self.get_time_ns_str()}")

        self.increment.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 4 complete")


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
    output_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
        'docs', 'markdown', 'assets', 'WAVES', 'counter_load_clear'
    )
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_load_and_count, "counter_load_clear_load_and_count.json"),
        (tb.scenario_clear_operation, "counter_load_clear_clear_operation.json"),
        (tb.scenario_dynamic_match, "counter_load_clear_dynamic_match.json"),
        (tb.scenario_wraparound, "counter_load_clear_wraparound.json"),
    ]

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


@pytest.mark.parametrize("max_value", [
    16,   # 4-bit counter, multiple wraparounds
])
def test_counter_load_clear_wavedrom(request, max_value):
    """Pytest wrapper for counter_load_clear WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "counter_load_clear"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    m_str = TBBase.format_dec(max_value, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_m{m_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'MAX': str(max_value)
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_MAX_VALUE': str(max_value),
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    compile_args = []
    sim_args = []
    plusargs = []

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
            includes=[rtl_dict['rtl_amba_includes']],
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
        print(f"✓ Counter Load Clear WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Counter Load Clear WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
