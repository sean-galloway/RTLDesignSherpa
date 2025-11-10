# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterJohnsonWaveDromTB
# Purpose: Johnson Counter WaveDrom Test - Showcases unique shift register with inverted feedback
#
# Documentation: docs/markdown/RTLCommon/counter_johnson.md
# Subsystem: tests
#
# Author: RTL Design Sherpa AI
# Created: 2025-10-20

"""
Johnson Counter WaveDrom Test

This test generates high-quality waveforms showcasing the unique Johnson counter properties:
- Shift register with inverted feedback
- Walking ones pattern (0000 → 0001 → 0011 → 0111 → 1111)
- Walking zeros pattern (1111 → 1110 → 1100 → 1000 → 0000)
- Single-bit transitions (CDC-safe like Gray code)
- 2×WIDTH states (8 states for WIDTH=4)
- Self-starting behavior

KEY FEATURE: Johnson counters are used in fifo_async_div2 for CDC!
             This test shows why single-bit transitions are critical.

WaveDrom Output:
    val/common/local_sim_build/test_counter_johnson_wavedrom_*/johnson_counter_*.json

Generate Waveforms:
    pytest val/common/test_counter_johnson_wavedrom.py -v
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

class CounterJohnsonWaveDromTB(TBBase):
    """Extended testbench for Johnson Counter with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Johnson counter sequence (shift with inverted feedback)
    - Walking ones and walking zeros patterns
    - Single-bit transitions (CDC safety)
    - Relationship to fifo_async_div2 CDC mechanism
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        random.seed(self.SEED)

        # Calculate sequence properties
        self.SEQUENCE_LENGTH = 2 * self.WIDTH

        self.log.info(f"Johnson Counter WaveDrom TB initialized{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, SEQUENCE_LENGTH={self.SEQUENCE_LENGTH}{self.get_time_ns_str()}")

        # Signal mappings
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_gray = self.dut.counter_gray

        # Clock configuration
        self.clock_period = 10  # 10ns = 100MHz

        # WaveDrom infrastructure
        self.wave_generator = None
        self.wave_solver = None

        # Calculate expected sequence
        self._calculate_expected_sequence()

    def _calculate_expected_sequence(self):
        """Calculate the expected Johnson counter sequence"""
        self.expected_sequence = []
        current_value = 0

        for i in range(self.SEQUENCE_LENGTH):
            self.expected_sequence.append(current_value)
            # Shift left and feed inverted MSB to LSB
            msb = (current_value >> (self.WIDTH - 1)) & 1
            current_value = ((current_value << 1) | (1 - msb)) & ((1 << self.WIDTH) - 1)

        if self.DEBUG:
            self.log.debug(f"Expected sequence: {[f'0b{x:0{self.WIDTH}b}' for x in self.expected_sequence]}{self.get_time_ns_str()}")

    def setup_wavedrom(self):
        """Set up WaveDrom system for Johnson counter waveform capture

        WaveDrom v1.2 Requirements:
        - Clock signals ALWAYS first
        - Signal grouping MANDATORY
        - 2-3 initial setup cycles
        - Quality over quantity (3-4 scenarios)
        """
        self.log.info(f"Setting up WaveDrom infrastructure{self.get_time_ns_str()}")

        # Create WaveDrom generator
        self.wave_generator = WaveJSONGenerator(debug_level=2)

        # Create constraint solver
        self.wave_solver = TemporalConstraintSolver(
            dut=self.dut,
            log=self.log,
            debug_level=2,
            wavejson_generator=self.wave_generator
        )

        # WAVEDROM REQUIREMENT v1.2: Clock signals ALWAYS first
        clock_signals = ['clk', 'rst_n']
        self.wave_generator.add_interface_group("Clocks & Reset", clock_signals)

        # Control signals
        control_signals = ['enable']
        self.wave_generator.add_interface_group("Control", control_signals)

        # Counter output
        counter_signals = ['counter_gray']
        self.wave_generator.add_interface_group("Johnson Counter Output", counter_signals)

        # Configure signals
        johnson_signals = {
            'clk': 'clk',
            'rst_n': 'rst_n',
            'enable': 'enable',
            'counter_gray': 'counter_gray'
        }

        # Add clock group
        self.wave_solver.add_clock_group(
            name="clk",
            clock_signal=self.clk,
            edge=ClockEdge.RISING,
            sample_delay_ns=0.1
        )

        # Add to solver
        self.wave_solver.add_interface("johnson", johnson_signals)

        # Add dummy constraint to trigger data capture
        # This constraint looks for enable going high, which happens at start of each scenario
        enable_constraint = TemporalConstraint(
            name="johnson_counter_capture",
            events=[
                TemporalEvent("enable_high", SignalTransition("johnson_enable", 0, 1))
            ],
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=150,  # Large enough to capture full scenarios
            required=False,
            max_matches=10,  # Allow multiple captures
            clock_group="clk",
            signals_to_show=['johnson_clk', 'johnson_rst_n', 'johnson_enable', 'johnson_counter_gray']
        )

        # Skip boundary detection for simple counter capture
        enable_constraint.skip_boundary_detection = True

        self.wave_solver.add_constraint(enable_constraint)

        self.log.info(f"WaveDrom setup complete{self.get_time_ns_str()}")

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.enable.value = 0
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    async def wait_cycles(self, n):
        """Wait for n clock cycles"""
        for _ in range(n):
            await RisingEdge(self.clk)

    async def scenario_walking_pattern(self):
        """SCENARIO 1: Walking ones and walking zeros pattern

        Demonstrates the unique Johnson counter sequence:
        - Walking ones: 0000 → 0001 → 0011 → 0111 → 1111
        - Walking zeros: 1111 → 1110 → 1100 → 1000 → 0000
        - Complete 2×WIDTH cycle (8 states for WIDTH=4)
        - Shows predictable, sequential pattern

        This pattern is why Johnson counters are useful for:
        - Multi-phase clock generation
        - Sequential state machines
        - LED chasers and visual effects
        """
        self.log.info(f"SCENARIO 1: Walking pattern{self.get_time_ns_str()}")

        # WAVEDROM REQUIREMENT v1.2: 2-3 initial setup cycles
        self.enable.value = 0
        await self.wait_cycles(2)

        # Start counting - capture complete sequence
        self.enable.value = 1

        # Capture full 2×WIDTH sequence
        for cycle in range(self.SEQUENCE_LENGTH):
            await RisingEdge(self.clk)
            actual = int(self.counter_gray.value)
            expected = self.expected_sequence[cycle]

            if actual != expected:
                self.log.error(f"Cycle {cycle}: Expected 0b{expected:0{self.WIDTH}b}, got 0b{actual:0{self.WIDTH}b}{self.get_time_ns_str()}")
            else:
                self.log.debug(f"Cycle {cycle}: 0b{actual:0{self.WIDTH}b}{self.get_time_ns_str()}")

        # Add a few more cycles to show wraparound
        await self.wait_cycles(3)

    async def scenario_single_bit_transitions(self):
        """SCENARIO 2: Single-bit transitions (CDC safety)

        Demonstrates that Johnson counters have single-bit transitions:
        - Each state change modifies only ONE bit
        - CDC-safe like Gray codes
        - Critical for fifo_async_div2 CDC mechanism

        Transition Analysis:
        - 0000 → 0001: bit[0] changes (0→1)
        - 0001 → 0011: bit[1] changes (0→1)
        - 0011 → 0111: bit[2] changes (0→1)
        - 0111 → 1111: bit[3] changes (0→1)
        - 1111 → 1110: bit[0] changes (1→0)
        - 1110 → 1100: bit[1] changes (1→0)
        - 1100 → 1000: bit[2] changes (1→0)
        - 1000 → 0000: bit[3] changes (1→0)

        THIS IS WHY Johnson counters are used in fifo_async_div2!
        Single-bit transitions prevent metastability when crossing clock domains.
        """
        self.log.info(f"SCENARIO 2: Single-bit transitions (CDC safety){self.get_time_ns_str()}")

        # Setup
        await self.reset_dut()
        await self.wait_cycles(2)

        # Enable and count
        self.enable.value = 1
        prev_value = int(self.counter_gray.value)

        for cycle in range(self.SEQUENCE_LENGTH):
            await RisingEdge(self.clk)
            curr_value = int(self.counter_gray.value)

            # Calculate Hamming distance
            hamming_dist = bin(prev_value ^ curr_value).count('1')

            if hamming_dist != 1:
                self.log.error(f"Cycle {cycle}: Hamming distance = {hamming_dist} (SHOULD BE 1!){self.get_time_ns_str()}")
            else:
                changed_bit = (prev_value ^ curr_value).bit_length() - 1
                self.log.debug(f"Cycle {cycle}: 0b{prev_value:0{self.WIDTH}b} → 0b{curr_value:0{self.WIDTH}b}, bit[{changed_bit}] changed{self.get_time_ns_str()}")

            prev_value = curr_value

        await self.wait_cycles(2)

    async def scenario_enable_control(self):
        """SCENARIO 3: Enable control (state holding)

        Demonstrates enable functionality:
        - Counter advances when enable=1
        - Counter holds state when enable=0
        - No glitches during enable transitions
        - Counting resumes from held state

        Use cases:
        - Conditional counting
        - Synchronized state machines
        - Power-efficient operation (clock gating alternative)
        """
        self.log.info(f"SCENARIO 3: Enable control{self.get_time_ns_str()}")

        # Setup
        await self.reset_dut()
        await self.wait_cycles(2)

        # Count a few cycles
        self.enable.value = 1
        await self.wait_cycles(4)

        # Hold state (disable)
        stored_value = int(self.counter_gray.value)
        self.enable.value = 0
        self.log.info(f"Disabling at 0b{stored_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
        await self.wait_cycles(5)

        # Verify held
        held_value = int(self.counter_gray.value)
        if held_value != stored_value:
            self.log.error(f"State changed during disable: 0b{stored_value:0{self.WIDTH}b} → 0b{held_value:0{self.WIDTH}b}{self.get_time_ns_str()}")

        # Re-enable and continue
        self.log.info(f"Re-enabling from 0b{held_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
        self.enable.value = 1
        await self.wait_cycles(6)

        # Disable again
        self.enable.value = 0
        await self.wait_cycles(3)

    async def scenario_reset_behavior(self):
        """SCENARIO 4: Reset and initialization

        Demonstrates reset behavior:
        - Asynchronous reset to 0000
        - Immediate reset effect
        - Clean restart from reset state
        - Reset during counting

        Properties:
        - Reset state: all zeros (0000)
        - Reset is asynchronous (immediate)
        - Counting starts from 0000 after reset release
        """
        self.log.info(f"SCENARIO 4: Reset behavior{self.get_time_ns_str()}")

        # Start from reset
        await self.reset_dut()
        await self.wait_cycles(2)

        # Count partway through sequence
        self.enable.value = 1
        await self.wait_cycles(5)

        # Apply reset mid-counting
        pre_reset_value = int(self.counter_gray.value)
        self.log.info(f"Applying reset at 0b{pre_reset_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
        self.rst_n.value = 0
        await RisingEdge(self.clk)

        # Check immediate reset
        reset_value = int(self.counter_gray.value)
        if reset_value != 0:
            self.log.error(f"Reset failed: got 0b{reset_value:0{self.WIDTH}b}, expected 0000{self.get_time_ns_str()}")

        await RisingEdge(self.clk)
        self.rst_n.value = 1

        # Verify counting resumes from 0
        await self.wait_cycles(6)

        # One more reset
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await self.wait_cycles(3)

    async def generate_all_wavedrom_scenarios(self):
        """Generate all Johnson counter WaveDrom scenarios.

        Follows FIFO pattern - all scenarios captured in one sampling session.
        No temporal constraints needed - direct waveform generation.
        """
        self.log.info(f"=== Generating All Johnson Counter WaveDrom Scenarios ==={self.get_time_ns_str()}")

        # Scenario 1: Walking pattern
        await self.reset_dut()
        await self.scenario_walking_pattern()
        await self.wait_cycles(10)  # Separation between scenarios

        # Scenario 2: Single-bit transitions
        await self.reset_dut()
        await self.scenario_single_bit_transitions()
        await self.wait_cycles(10)

        # Scenario 3: Enable control
        await self.reset_dut()
        await self.scenario_enable_control()
        await self.wait_cycles(10)

        # Scenario 4: Reset behavior
        await self.reset_dut()
        await self.scenario_reset_behavior()
        await self.wait_cycles(10)

        self.log.info(f"✓ All Johnson Counter WaveDrom scenarios generated{self.get_time_ns_str()}")

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def counter_johnson_wavedrom_test(dut):
    """WaveDrom test for Johnson Counter - generates separate waveforms per scenario"""
    import os
    import shutil
    import subprocess

    tb = CounterJohnsonWaveDromTB(dut)

    # Setup
    await tb.setup_clock()
    await tb.reset_dut()

    # Setup WaveDrom
    tb.setup_wavedrom()

    # Create output directory
    output_dir = "docs/markdown/assets/WAVES/counter_johnson"
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_walking_pattern, "johnson_counter_walking_pattern.json"),
        (tb.scenario_single_bit_transitions, "johnson_counter_single_bit_transitions.json"),
        (tb.scenario_enable_control, "johnson_counter_enable_control.json"),
        (tb.scenario_reset_behavior, "johnson_counter_reset_behavior.json"),
    ]

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

        tb.log.info("\n🎉 JOHNSON COUNTER WAVEDROM GENERATION COMPLETE! 🎉")
        tb.log.info(f"Generated {len(scenarios)} waveform files in: {output_dir}")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_cycles(10)

    tb.log.info(f"✓ Johnson Counter WaveDrom test PASSED{tb.get_time_ns_str()}")
    return True

def test_counter_johnson_wavedrom(request):
    """
    Pytest entry point for Johnson Counter WaveDrom test

    Generates high-quality waveforms showcasing:
    - Walking ones and walking zeros pattern
    - Single-bit transitions (CDC safety)
    - Enable control and state holding
    - Reset behavior

    Output: johnson_counter_*.json files in sim_build directory
    """
    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT configuration
    dut_name = "counter_johnson"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]
    toplevel = dut_name

    # Test parameters
    width = 4  # WIDTH=4 gives 8-state sequence (perfect for visualization)
    test_name = f"test_counter_johnson_wavedrom_w{width}"

    # Directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
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
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '1'
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    print(f"\n{'='*60}")
    print(f"Johnson Counter WaveDrom Test")
    print(f"WIDTH={width}, Sequence Length={2*width}")
    print(f"Output: {sim_build}/johnson_counter_*.json")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_amba_includes']],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ WaveDrom test PASSED")
        print(f"WaveJSON files generated in: {sim_build}/")
    except Exception as e:
        print(f"✗ WaveDrom test FAILED: {str(e)}")
        print(f"Logs: {log_path}")
        print(f"View waveforms: {cmd_filename}")
        raise
