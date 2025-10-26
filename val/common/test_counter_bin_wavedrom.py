# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterBinWaveDromTB
# Purpose: Binary Counter WaveDrom Test - Showcases FIFO-optimized MSB inversion behavior
#
# Documentation: docs/markdown/RTLCommon/counter_bin.md
# Subsystem: tests
#
# Author: RTL Design Sherpa AI
# Created: 2025-10-20

"""
Binary Counter WaveDrom Test

This test generates high-quality waveforms showcasing the unique counter_bin properties:
- Basic binary counting (0→1→2→...→MAX-1)
- FIFO-optimized wraparound (MSB inversion + lower bit clear)
- Enable control for gating count operation
- Relationship to FIFO pointer management
- Both current (registered) and next (combinational) outputs

KEY FEATURE: counter_bin is designed for FIFO read/write pointers!
             The MSB toggles on wraparound to enable simple full/empty detection.

WaveDrom Output:
    docs/markdown/assets/WAVES/counter_bin/counter_bin_*.json

Generate Waveforms:
    pytest val/common/test_counter_bin_wavedrom.py -v
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


class CounterBinWaveDromTB(TBBase):
    """Extended testbench for Binary Counter with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Binary counting sequence
    - FIFO-optimized MSB inversion on wraparound
    - Enable control for hold operation
    - Current vs next counter outputs
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.MAX = self.convert_to_int(os.environ.get('TEST_MAX', '8'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        random.seed(self.SEED)

        self.log.info(f"Counter Bin WaveDrom TB initialized{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX={self.MAX}{self.get_time_ns_str()}")

        # Signal mappings
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_bin_curr = self.dut.counter_bin_curr
        self.counter_bin_next = self.dut.counter_bin_next

        # Clock configuration
        self.clock_period = 10  # 10ns = 100MHz

        # WaveDrom infrastructure
        self.wave_generator = None
        self.wave_solver = None

        # Calculate expected sequence
        self._calculate_expected_sequence()

    def _calculate_expected_sequence(self):
        """Calculate the expected counter_bin sequence with MSB inversion"""
        self.expected_sequence = []

        # First half: MSB=0, count 0 to MAX-1
        for i in range(self.MAX):
            self.expected_sequence.append(i)

        # Wraparound: MSB inverts, lower bits clear to 0
        msb_inverted = 1 << (self.WIDTH - 1)

        # Second half: MSB=1, count 0 to MAX-1
        for i in range(self.MAX):
            self.expected_sequence.append(msb_inverted | i)

        # Full cycle length
        self.full_cycle_length = len(self.expected_sequence)

        self.log.info(f"Expected sequence length: {self.full_cycle_length}{self.get_time_ns_str()}")
        if self.DEBUG:
            self.log.info(f"Expected sequence: {[hex(x) for x in self.expected_sequence]}{self.get_time_ns_str()}")

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
        self.enable.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1
        self.enable.value = 0

    def setup_wavedrom(self):
        """Set up WaveDrom system for counter_bin waveform capture"""
        try:
            self.log.info("Setting up WaveDrom for Counter Bin...")

            # Create field configuration
            self.field_config_wave = FieldConfig.from_dict(
                field_dict={
                    'counter_bin_curr': {'bits': self.WIDTH, 'default': 0},
                    'counter_bin_next': {'bits': self.WIDTH, 'default': 0},
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
            control_signals = ['enable']
            self.wave_generator.add_interface_group("Control", control_signals)

            # Group 3: Counter Outputs
            counter_signals = ['counter_bin_curr', 'counter_bin_next']
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
                'enable': 'enable',
                'counter_bin_curr': 'counter_bin_curr',
                'counter_bin_next': 'counter_bin_next',
            }

            self.wave_solver.add_interface("counter", counter_signals, field_config=self.field_config_wave)

            # Add dummy constraint to trigger waveform generation
            enable_constraint = TemporalConstraint(
                name="counter_bin_capture",
                events=[
                    TemporalEvent("enable_high", SignalTransition("counter_enable", 0, 1))
                ],
                temporal_relation=TemporalRelation.SEQUENCE,
                max_window_size=100,
                required=False,
                max_matches=10,
                clock_group="clk",
                signals_to_show=['counter_clk', 'counter_rst_n', 'counter_enable',
                                'counter_counter_bin_curr', 'counter_counter_bin_next']
            )
            enable_constraint.skip_boundary_detection = True
            self.wave_solver.add_constraint(enable_constraint)

            self.log.info("✓ WaveDrom setup complete for Counter Bin")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            import traceback
            traceback.print_exc()
            self.wave_solver = None
            self.wave_generator = None

    async def scenario_basic_counting(self):
        """
        SCENARIO 1: Basic counting sequence

        Demonstrates standard binary counter operation from 0 to MAX-1.
        """
        self.log.info("=== Scenario 1: Basic Counting (0 to MAX-1) ===")

        await self.wait_clocks('clk', 3)

        # Enable counter and count to MAX-1
        self.enable.value = 1
        for i in range(self.MAX):
            await RisingEdge(self.clk)
            curr_val = int(self.counter_bin_curr.value)
            self.log.info(f"Count: {curr_val}{self.get_time_ns_str()}")

        self.enable.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 1 complete")

    async def scenario_msb_wraparound(self):
        """
        SCENARIO 2: MSB inversion wraparound

        Demonstrates the FIFO-optimized behavior where MSB inverts and lower bits clear.
        """
        self.log.info("=== Scenario 2: MSB Inversion Wraparound ===")

        await self.wait_clocks('clk', 3)

        # Count through wraparound to show MSB inversion
        self.enable.value = 1
        for i in range(self.MAX + 3):  # Go past wraparound
            await RisingEdge(self.clk)
            curr_val = int(self.counter_bin_curr.value)
            next_val = int(self.counter_bin_next.value)
            msb_curr = (curr_val >> (self.WIDTH - 1)) & 1
            lower_curr = curr_val & ((1 << (self.WIDTH - 1)) - 1)
            self.log.info(f"Count: {curr_val:#x} (MSB={msb_curr}, Lower={lower_curr:#x}), Next={next_val:#x}{self.get_time_ns_str()}")

        self.enable.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 2 complete")

    async def scenario_enable_control(self):
        """
        SCENARIO 3: Enable control demonstration

        Shows how enable signal gates the counting operation.
        """
        self.log.info("=== Scenario 3: Enable Control ===")

        await self.wait_clocks('clk', 3)

        # Count with enable toggling
        for cycle in range(8):
            # Enable for 2 cycles
            self.enable.value = 1
            await RisingEdge(self.clk)
            await RisingEdge(self.clk)

            # Disable for 2 cycles (counter should hold)
            self.enable.value = 0
            await RisingEdge(self.clk)
            await RisingEdge(self.clk)

        self.enable.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 3 complete")

    async def scenario_full_cycle(self):
        """
        SCENARIO 4: Full cycle demonstration

        Shows complete cycle through both MSB states (0→MAX-1→wraparound→MAX-1→wraparound).
        """
        self.log.info("=== Scenario 4: Full Cycle (Both MSB States) ===")

        await self.wait_clocks('clk', 3)

        # Count through full cycle
        self.enable.value = 1
        for i in range(self.full_cycle_length + 2):
            await RisingEdge(self.clk)
            curr_val = int(self.counter_bin_curr.value)
            msb = (curr_val >> (self.WIDTH - 1)) & 1
            lower = curr_val & ((1 << (self.WIDTH - 1)) - 1)
            self.log.info(f"Cycle {i}: {curr_val:#x} (MSB={msb}, Lower={lower}){self.get_time_ns_str()}")

        self.enable.value = 0
        await self.wait_clocks('clk', 3)

        self.log.info("✓ Scenario 4 complete")


@cocotb.test(timeout_time=500, timeout_unit="us")
async def counter_bin_wavedrom_test(dut):
    """Generate WaveDrom waveforms for counter_bin showcasing FIFO-optimized behavior - per scenario."""
    import shutil
    import subprocess

    tb = CounterBinWaveDromTB(dut)

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.setup_clocks_and_reset()
    tb.setup_wavedrom()

    # Output directory for waveforms
    output_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
        'docs', 'markdown', 'assets', 'WAVES', 'counter_bin'
    )
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_basic_counting, "counter_bin_basic_counting.json"),
        (tb.scenario_msb_wraparound, "counter_bin_msb_wraparound.json"),
        (tb.scenario_enable_control, "counter_bin_enable_control.json"),
        (tb.scenario_full_cycle, "counter_bin_full_cycle.json"),
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
                    json_files = glob.glob("counter_bin_capture_*.json")
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
                                ], capture_output=True, text=True)
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

        tb.log.info("🎉 COUNTER BIN WAVEDROM GENERATION COMPLETE! 🎉")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('clk', 10)


@pytest.mark.parametrize("width, max_val", [
    (4, 8),   # 4-bit counter, wrap at 8
])
def test_counter_bin_wavedrom(request, width, max_val):
    """Pytest wrapper for counter_bin WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "counter_bin"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    w_str = TBBase.format_dec(width, 3)
    m_str = TBBase.format_dec(max_val, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_w{w_str}_m{m_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        'WIDTH': str(width),
        'MAX': str(max_val)
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_WIDTH': str(width),
        'TEST_MAX': str(max_val),
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    compile_args = []
    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running Counter Bin WaveDrom Generation")
    print(f"Showcasing FIFO-Optimized MSB Inversion")
    print(f"Width: {width}, MAX: {max_val}")
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
        print(f"✓ Counter Bin WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Counter Bin WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
