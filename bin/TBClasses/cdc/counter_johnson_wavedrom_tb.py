# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterJohnsonWaveDromTB
# Purpose: Testbench for counter_johnson_wavedrom
# Subsystem: framework
#
# Extracted from val/cdc/test_counter_johnson_wavedrom.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles, ReadOnly
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator


class CounterJohnsonWaveDromTB(TBBase):
    """Extended testbench for Johnson Counter with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Johnson counter sequence (shift with inverted feedback)
    - Walking ones and walking zeros patterns
    - Single-bit transitions (CDC safety)
    - Relationship to the fifo_async USE_JOHNSON=1 CDC mechanism
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

    scenario_errors = 0

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
                self.scenario_errors += 1
            else:
                self.log.debug(f"Cycle {cycle}: 0b{actual:0{self.WIDTH}b}{self.get_time_ns_str()}")

        # Add a few more cycles to show wraparound
        await self.wait_cycles(3)

    async def scenario_single_bit_transitions(self):
        """SCENARIO 2: Single-bit transitions (CDC safety)

        Demonstrates that Johnson counters have single-bit transitions:
        - Each state change modifies only ONE bit
        - CDC-safe like Gray codes
        - Critical for the fifo_async USE_JOHNSON=1 CDC mechanism

        Transition Analysis:
        - 0000 → 0001: bit[0] changes (0→1)
        - 0001 → 0011: bit[1] changes (0→1)
        - 0011 → 0111: bit[2] changes (0→1)
        - 0111 → 1111: bit[3] changes (0→1)
        - 1111 → 1110: bit[0] changes (1→0)
        - 1110 → 1100: bit[1] changes (1→0)
        - 1100 → 1000: bit[2] changes (1→0)
        - 1000 → 0000: bit[3] changes (1→0)

        THIS IS WHY Johnson counters are used at USE_JOHNSON=1!
        Single-bit transitions prevent metastability when crossing clock domains.
        """
        self.log.info(f"SCENARIO 2: Single-bit transitions (CDC safety){self.get_time_ns_str()}")

        # Setup
        await self.reset_dut()
        await self.wait_cycles(2)

        # Enable and count. Drive enable right after an edge so it settles
        # a full cycle before the first sampled edge -- driving it just
        # before the edge raced the DUT and produced a spurious cycle-0
        # 'Hamming distance = 0' error on every run (test-audit finding).
        await RisingEdge(self.clk)
        self.enable.value = 1
        prev_value = int(self.counter_gray.value)

        for cycle in range(self.SEQUENCE_LENGTH):
            await RisingEdge(self.clk)
            await ReadOnly()  # let the edge's NBA updates settle before reading
            curr_value = int(self.counter_gray.value)

            # Calculate Hamming distance
            hamming_dist = bin(prev_value ^ curr_value).count('1')

            if hamming_dist != 1:
                self.log.error(f"Cycle {cycle}: Hamming distance = {hamming_dist} (SHOULD BE 1!){self.get_time_ns_str()}")
                self.scenario_errors += 1
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
        await Timer(1, 'ns')  # settle NBA updates, stay writeable (ReadOnly blocks the disable below)

        # Hold state (disable)
        stored_value = int(self.counter_gray.value)
        self.enable.value = 0
        self.log.info(f"Disabling at 0b{stored_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
        await self.wait_cycles(5)

        # Verify held
        held_value = int(self.counter_gray.value)
        if held_value != stored_value:
            self.log.error(f"State changed during disable: 0b{stored_value:0{self.WIDTH}b} → 0b{held_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
            self.scenario_errors += 1

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
        await Timer(1, 'ns')  # let the reset's NBA update land (ReadOnly blocks rst_n write below)

        # Check immediate reset
        reset_value = int(self.counter_gray.value)
        if reset_value != 0:
            self.log.error(f"Reset failed: got 0b{reset_value:0{self.WIDTH}b}, expected 0000{self.get_time_ns_str()}")
            self.scenario_errors += 1

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
