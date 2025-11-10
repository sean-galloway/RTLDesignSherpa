# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterFreqInvariantWaveDromTB
# Purpose: Counter Freq Invariant WaveDrom Test - Showcases frequency-agnostic microsecond timing
#
# Documentation: docs/markdown/RTLCommon/counter_freq_invariant.md
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
    docs/markdown/assets/WAVES/counter_freq_invariant/counter_freq_invariant_*.json

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
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig

class CounterFreqInvariantWaveDromTB(TBBase):
    """Extended testbench for Counter Freq Invariant with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Frequency-invariant microsecond tick generation
    - Clock frequency selection and reconfiguration
    - Prescaler operation and division factors
    - Tick pulse and counter increment
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.COUNTER_WIDTH = self.convert_to_int(os.environ.get('TEST_COUNTER_WIDTH', '16'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        random.seed(self.SEED)

        self.log.info(f"Counter Freq Invariant WaveDrom TB initialized{self.get_time_ns_str()}")
        self.log.info(f"COUNTER_WIDTH={self.COUNTER_WIDTH}{self.get_time_ns_str()}")

        # Signal mappings
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.sync_reset_n = self.dut.sync_reset_n
        self.freq_sel = self.dut.freq_sel
        self.counter = self.dut.o_counter
        self.tick = self.dut.tick

        # Clock configuration - use 10ns for simulation (100MHz nominal)
        # But freq_sel will configure the division factor
        self.clock_period = 10  # 10ns = 100MHz

        # WaveDrom infrastructure
        self.wave_generator = None
        self.wave_solver = None

        # Frequency selection lookup for common values
        self.freq_sel_map = {
            100: 0,    # 100MHz → div=100 (10ns × 100 = 1μs)
            150: 10,   # 150MHz → div=150
            200: 15,   # 200MHz → div=200
            250: 18,   # 250MHz → div=250
            500: 31,   # 500MHz → div=500
            1000: 47,  # 1GHz → div=1000
        }

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
        self.sync_reset_n.value = 0
        self.freq_sel.value = 0  # 100MHz

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1
        self.sync_reset_n.value = 1
        self.freq_sel.value = 0  # 100MHz

    def setup_wavedrom(self):
        """Set up WaveDrom system for counter_freq_invariant waveform capture"""
        try:
            self.log.info("Setting up WaveDrom for Counter Freq Invariant...")

            # Create field configuration
            self.field_config_wave = FieldConfig.from_dict(
                field_dict={
                    'freq_sel': {'bits': 7, 'default': 0},
                    'counter': {'bits': self.COUNTER_WIDTH, 'default': 0},
                },
                lsb_first=True
            )

            # Create WaveJSON generator
            self.wave_generator = WaveJSONGenerator(debug_level=2)

            # WAVEDROM REQUIREMENT v1.2: Signal grouping MANDATORY
            # Group 1: Clocks and Resets (ALWAYS FIRST)
            clock_signals = ['clk', 'rst_n', 'sync_reset_n']
            self.wave_generator.add_interface_group("Clocks & Reset", clock_signals)

            # Group 2: Configuration
            config_signals = ['freq_sel']
            self.wave_generator.add_interface_group("Configuration", config_signals)

            # Group 3: Outputs
            output_signals = ['tick', 'counter']
            self.wave_generator.add_interface_group("Outputs", output_signals)

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
                'sync_reset_n': 'sync_reset_n',
                'freq_sel': 'freq_sel',
                'tick': 'tick',
                'counter': 'counter',
            }

            self.wave_solver.add_interface("counter", counter_signals, field_config=self.field_config_wave)

            # Add dummy constraint to trigger waveform generation
            tick_constraint = TemporalConstraint(
                name="counter_freq_invariant_capture",
                events=[
                    TemporalEvent("tick_high", SignalTransition("counter_tick", 0, 1))
                ],
                temporal_relation=TemporalRelation.SEQUENCE,
                max_window_size=200,
                required=False,
                max_matches=10,
                clock_group="clk",
                signals_to_show=['counter_clk', 'counter_rst_n', 'counter_sync_reset_n',
                                'counter_freq_sel', 'counter_tick', 'counter_counter']
            )
            tick_constraint.skip_boundary_detection = True
            self.wave_solver.add_constraint(tick_constraint)

            self.log.info("✓ WaveDrom setup complete for Counter Freq Invariant")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            import traceback
            traceback.print_exc()
            self.wave_solver = None
            self.wave_generator = None

    async def scenario_basic_tick_generation(self):
        """
        SCENARIO 1: Basic tick generation

        Demonstrates 1MHz tick generation at nominal frequency (100MHz / 100 = 1MHz).
        Note: In simulation at 100MHz with div=100, we see a tick every 100 clock cycles.
        """
        self.log.info("=== Scenario 1: Basic Tick Generation (100MHz) ===")

        await self.wait_clocks('clk', 3)

        # Set to 100MHz (freq_sel=0, div=100)
        self.freq_sel.value = 0
        await self.wait_clocks('clk', 2)

        # Wait for ticks to occur (100 cycles per tick at 100MHz)
        # In real hardware: 10ns × 100 = 1μs
        # In simulation: count 100 clocks per tick
        for cycle in range(250):  # ~2.5 ticks
            await RisingEdge(self.clk)
            tick_val = int(self.tick.value)
            counter_val = int(self.counter.value)
            if tick_val == 1 or (cycle % 25 == 0):
                self.log.info(f"Cycle {cycle}: tick={tick_val}, counter={counter_val}{self.get_time_ns_str()}")

        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 1 complete")

    async def scenario_freq_change(self):
        """
        SCENARIO 2: Frequency change

        Demonstrates runtime frequency reconfiguration.
        """
        self.log.info("=== Scenario 2: Frequency Change ===")

        await self.wait_clocks('clk', 3)

        # Start at 100MHz (freq_sel=0, div=100)
        self.freq_sel.value = 0
        await self.wait_clocks('clk', 2)

        # Wait for a tick
        for cycle in range(120):
            await RisingEdge(self.clk)
            if int(self.tick.value) == 1:
                self.log.info(f"First tick at cycle {cycle}{self.get_time_ns_str()}")
                break

        await self.wait_clocks('clk', 10)

        # Change to 200MHz (freq_sel=15, div=200) - will take twice as many clocks per tick
        self.log.info("Changing frequency to 200MHz...")
        self.freq_sel.value = 15
        await self.wait_clocks('clk', 5)

        # Wait for next tick at new frequency
        for cycle in range(220):
            await RisingEdge(self.clk)
            tick_val = int(self.tick.value)
            if tick_val == 1:
                self.log.info(f"Tick after freq change at cycle {cycle}{self.get_time_ns_str()}")

        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 2 complete")

    async def scenario_sync_reset(self):
        """
        SCENARIO 3: Synchronous reset

        Demonstrates sync_reset_n control.
        """
        self.log.info("=== Scenario 3: Synchronous Reset ===")

        await self.wait_clocks('clk', 3)

        # Set frequency and wait for counter to increment
        self.freq_sel.value = 0  # 100MHz
        await self.wait_clocks('clk', 2)

        # Wait for a couple ticks
        tick_count = 0
        for cycle in range(250):
            await RisingEdge(self.clk)
            if int(self.tick.value) == 1:
                tick_count += 1
                counter_val = int(self.counter.value)
                self.log.info(f"Tick {tick_count}: counter={counter_val}{self.get_time_ns_str()}")
                if tick_count >= 2:
                    break

        await self.wait_clocks('clk', 5)

        # Assert sync reset
        self.log.info("Asserting sync_reset_n...")
        self.sync_reset_n.value = 0
        await self.wait_clocks('clk', 5)

        counter_val = int(self.counter.value)
        self.log.info(f"After sync reset: counter={counter_val}{self.get_time_ns_str()}")

        # Deassert and continue
        self.sync_reset_n.value = 1
        await self.wait_clocks('clk', 10)

        # Wait for next tick
        for cycle in range(120):
            await RisingEdge(self.clk)
            if int(self.tick.value) == 1:
                counter_val = int(self.counter.value)
                self.log.info(f"First tick after reset: counter={counter_val}{self.get_time_ns_str()}")
                break

        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 3 complete")

    async def scenario_counter_increment(self):
        """
        SCENARIO 4: Counter increment demonstration

        Shows counter incrementing on each tick.
        """
        self.log.info("=== Scenario 4: Counter Increment ===")

        await self.wait_clocks('clk', 3)

        # Set frequency
        self.freq_sel.value = 0  # 100MHz
        await self.wait_clocks('clk', 2)

        # Wait for multiple ticks and observe counter
        tick_count = 0
        for cycle in range(500):
            await RisingEdge(self.clk)
            tick_val = int(self.tick.value)
            counter_val = int(self.counter.value)
            if tick_val == 1:
                tick_count += 1
                self.log.info(f"Tick {tick_count}: counter incremented to {counter_val}{self.get_time_ns_str()}")
                if tick_count >= 4:
                    break

        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 4 complete")

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
    output_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
        'docs', 'markdown', 'assets', 'WAVES', 'counter_freq_invariant'
    )
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_basic_tick_generation, "counter_freq_invariant_basic_ticks.json"),
        (tb.scenario_freq_change, "counter_freq_invariant_freq_change.json"),
        (tb.scenario_sync_reset, "counter_freq_invariant_sync_reset.json"),
        (tb.scenario_counter_increment, "counter_freq_invariant_counter_increment.json"),
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

@pytest.mark.parametrize("counter_width", [
    16,   # 16-bit counter (65.5ms rollover)
])
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
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'COUNTER_WIDTH': str(counter_width),
        'PRESCALER_MAX': '2048'
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_COUNTER_WIDTH': str(counter_width),
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    compile_args = []
    sim_args = []
    plusargs = []

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
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ Counter Freq Invariant WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Counter Freq Invariant WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
