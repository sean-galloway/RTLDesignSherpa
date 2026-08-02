# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterBinGrayWaveDromTB
# Purpose: Testbench for counter_bingray_wavedrom
# Subsystem: framework
#
# Extracted from val/cdc/test_counter_bingray_wavedrom.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator


class CounterBinGrayWaveDromTB(TBBase):
    """Extended testbench for Binary-Gray Counter with WaveDrom visualization support

    Inherits from TBBase and adds WaveDrom capture capabilities to demonstrate:
    - Binary and Gray code outputs simultaneously
    - Single-bit transitions in Gray code (CDC safety)
    - Binary-to-Gray conversion relationship
    - Counter_bin_next lookahead feature
    - Relationship to fifo_async CDC mechanism
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        random.seed(self.SEED)

        # Calculate max value
        self.MAX_VALUE = (1 << self.WIDTH) - 1

        self.log.info(f"BinGray Counter WaveDrom TB initialized{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX_VALUE={self.MAX_VALUE}{self.get_time_ns_str()}")

        # Signal mappings
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_bin = self.dut.counter_bin
        self.counter_bin_next = self.dut.counter_bin_next
        self.counter_gray = self.dut.counter_gray

        # Clock configuration
        self.clock_period = 10  # 10ns = 100MHz

        # WaveDrom infrastructure
        self.wave_generator = None
        self.wave_solver = None

        # Calculate expected sequences
        self._calculate_expected_sequences()

    def _binary_to_gray(self, binary_val):
        """Convert binary value to Gray code"""
        return binary_val ^ (binary_val >> 1)

    def _calculate_expected_sequences(self):
        """Calculate the expected binary and Gray sequences"""
        self.expected_bin_sequence = []
        self.expected_gray_sequence = []

        for i in range(1 << self.WIDTH):
            self.expected_bin_sequence.append(i)
            self.expected_gray_sequence.append(self._binary_to_gray(i))

        if self.DEBUG:
            self.log.debug(f"First 16 binary: {[hex(x) for x in self.expected_bin_sequence[:16]]}{self.get_time_ns_str()}")
            self.log.debug(f"First 16 Gray: {[hex(x) for x in self.expected_gray_sequence[:16]]}{self.get_time_ns_str()}")

    def setup_wavedrom(self):
        """Set up WaveDrom system for Binary-Gray counter waveform capture

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

        # Counter outputs
        counter_signals = ['counter_bin', 'counter_bin_next', 'counter_gray']
        self.wave_generator.add_interface_group("Counter Outputs", counter_signals)

        # Configure signals
        bingray_signals = {
            'clk': 'clk',
            'rst_n': 'rst_n',
            'enable': 'enable',
            'counter_bin': 'counter_bin',
            'counter_bin_next': 'counter_bin_next',
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
        self.wave_solver.add_interface("bingray", bingray_signals)

        # Add dummy constraint to trigger data capture
        # This constraint looks for enable going high, which happens at start of each scenario
        enable_constraint = TemporalConstraint(
            name="bingray_counter_capture",
            events=[
                TemporalEvent("enable_high", SignalTransition("bingray_enable", 0, 1))
            ],
            temporal_relation=TemporalRelation.SEQUENCE,
            max_window_size=150,  # Large enough to capture full scenarios
            required=False,
            max_matches=10,  # Allow multiple captures
            clock_group="clk",
            signals_to_show=['bingray_clk', 'bingray_rst_n', 'bingray_enable',
                           'bingray_counter_bin', 'bingray_counter_bin_next', 'bingray_counter_gray']
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

    async def scenario_binary_vs_gray(self):
        """SCENARIO 1: Binary vs Gray code comparison

        Demonstrates the fundamental difference between binary and Gray encoding:
        - Binary: Normal sequential counting (0→1→2→3→...)
        - Gray: Single-bit transitions between adjacent values
        - Shows full cycle through multiple states

        Key observations:
        - Binary can have multiple bits change (e.g., 0111→1000 changes 4 bits)
        - Gray always has exactly one bit change per transition
        - Gray code wraps around safely (1000→0000 changes 1 bit)

        This comparison shows WHY Gray code is essential for CDC:
        - Binary: Multiple bit changes → metastability risk
        - Gray: Single bit changes → CDC-safe
        """
        self.log.info(f"SCENARIO 1: Binary vs Gray comparison{self.get_time_ns_str()}")

        # WAVEDROM REQUIREMENT v1.2: 2-3 initial setup cycles
        self.enable.value = 0
        await self.wait_cycles(2)

        # Start counting
        self.enable.value = 1

        # Capture full sequence for WIDTH=4 (16 states)
        for cycle in range(min(self.MAX_VALUE + 1, 16)):
            await RisingEdge(self.clk)

            actual_bin = int(self.counter_bin.value)
            actual_gray = int(self.counter_gray.value)
            expected_bin = self.expected_bin_sequence[cycle]
            expected_gray = self.expected_gray_sequence[cycle]

            if actual_bin != expected_bin or actual_gray != expected_gray:
                self.log.error(f"Cycle {cycle}: Bin expected {expected_bin}, got {actual_bin}; Gray expected {expected_gray}, got {actual_gray}{self.get_time_ns_str()}")
            else:
                self.log.debug(f"Cycle {cycle}: Bin=0x{actual_bin:X}, Gray=0x{actual_gray:X}{self.get_time_ns_str()}")

        # A few more cycles to show wraparound
        await self.wait_cycles(3)

    async def scenario_single_bit_transitions(self):
        """SCENARIO 2: Single-bit transitions in Gray code (CDC safety)

        Demonstrates the critical CDC safety property of Gray codes:
        - Each Gray code transition changes EXACTLY one bit
        - Hamming distance between adjacent values = 1
        - Prevents intermediate glitch states

        Example transitions (4-bit):
        - 0000→0001: bit[0] changes
        - 0001→0011: bit[1] changes
        - 0011→0010: bit[0] changes
        - 0010→0110: bit[2] changes

        THIS IS WHY fifo_async uses Gray code!
        When synchronizing pointers across clock domains:
        - Single-bit transition → only one synchronizer can go metastable
        - Multiple-bit transitions → multiple synchronizers metastable → WRONG VALUE!

        Gray code ensures that even if metastability occurs,
        the synchronized value is either old or new - never garbage.
        """
        self.log.info(f"SCENARIO 2: Single-bit transitions (CDC safety){self.get_time_ns_str()}")

        # Setup
        await self.reset_dut()
        await self.wait_cycles(2)

        # Enable and count
        self.enable.value = 1
        prev_gray = int(self.counter_gray.value)

        # Test enough transitions to show pattern
        for cycle in range(min(self.MAX_VALUE + 1, 12)):
            await RisingEdge(self.clk)
            curr_gray = int(self.counter_gray.value)

            # Calculate Hamming distance
            hamming_dist = bin(prev_gray ^ curr_gray).count('1')

            if hamming_dist != 1:
                self.log.error(f"Cycle {cycle}: Hamming distance = {hamming_dist} (SHOULD BE 1!){self.get_time_ns_str()}")
            else:
                # Find which bit changed
                xor_result = prev_gray ^ curr_gray
                changed_bit = (xor_result & -xor_result).bit_length() - 1  # Find rightmost set bit
                self.log.debug(f"Cycle {cycle}: 0b{prev_gray:0{self.WIDTH}b} → 0b{curr_gray:0{self.WIDTH}b}, bit[{changed_bit}] changed{self.get_time_ns_str()}")

            prev_gray = curr_gray

        await self.wait_cycles(2)

    async def scenario_lookahead_signal(self):
        """SCENARIO 3: Counter_bin_next lookahead feature

        Demonstrates the combinational lookahead output:
        - counter_bin: Current value (registered)
        - counter_bin_next: Next value (combinational)
        - counter_bin_next predicts future value one cycle ahead

        Use cases for lookahead:
        - FIFO full/empty prediction (check one cycle early)
        - Pipeline control (prepare for next state)
        - Address generation (pre-calculate next address)

        When enable=0:
        - counter_bin holds current value
        - counter_bin_next equals counter_bin (no change)

        When enable=1:
        - counter_bin increments each cycle
        - counter_bin_next shows counter_bin + 1
        """
        self.log.info(f"SCENARIO 3: Lookahead signal{self.get_time_ns_str()}")

        # Setup
        await self.reset_dut()
        await self.wait_cycles(2)

        # Count with enable=1
        self.enable.value = 1
        for cycle in range(6):
            await RisingEdge(self.clk)

            curr_bin = int(self.counter_bin.value)
            next_bin = int(self.counter_bin_next.value)
            expected_next = (curr_bin + 1) % (1 << self.WIDTH)

            if next_bin != expected_next:
                self.log.error(f"Cycle {cycle}: Next expected {expected_next}, got {next_bin}{self.get_time_ns_str()}")
            else:
                self.log.debug(f"Cycle {cycle}: Bin={curr_bin}, Next={next_bin} ✓{self.get_time_ns_str()}")

        # Disable and show lookahead holds
        self.enable.value = 0
        held_value = int(self.counter_bin.value)
        await self.wait_cycles(4)

        # Verify next equals current when disabled
        curr_bin = int(self.counter_bin.value)
        next_bin = int(self.counter_bin_next.value)
        if curr_bin != held_value or next_bin != held_value:
            self.log.error(f"Values changed during disable!{self.get_time_ns_str()}")

        # Re-enable
        self.enable.value = 1
        await self.wait_cycles(4)

    async def scenario_enable_and_reset(self):
        """SCENARIO 4: Enable control and reset behavior

        Demonstrates control signals:
        - enable: Gates counting (both outputs hold when disabled)
        - rst_n: Asynchronous reset to zero (both outputs)

        Enable control:
        - When enable=0: Both counter_bin and counter_gray hold value
        - When enable=1: Counting resumes from held state

        Reset behavior:
        - Asynchronous: Takes effect immediately
        - Both outputs: counter_bin=0, counter_gray=0
        - Reset during counting: Immediate return to zero
        - Counting resumes: Normal sequence from zero

        Clean state transitions:
        - No glitches during enable toggle
        - No intermediate states during reset
        - Predictable behavior for system integration
        """
        self.log.info(f"SCENARIO 4: Enable and reset control{self.get_time_ns_str()}")

        # Start from reset
        await self.reset_dut()
        await self.wait_cycles(2)

        # Count a few cycles
        self.enable.value = 1
        await self.wait_cycles(5)

        # Disable and hold
        stored_bin = int(self.counter_bin.value)
        stored_gray = int(self.counter_gray.value)
        self.enable.value = 0
        self.log.info(f"Disabling at Bin={stored_bin}, Gray={stored_gray}{self.get_time_ns_str()}")
        await self.wait_cycles(4)

        # Re-enable
        self.enable.value = 1
        self.log.info(f"Re-enabling from held state{self.get_time_ns_str()}")
        await self.wait_cycles(5)

        # Apply reset mid-counting
        pre_reset_bin = int(self.counter_bin.value)
        self.log.info(f"Applying reset at Bin={pre_reset_bin}{self.get_time_ns_str()}")
        self.rst_n.value = 0
        await RisingEdge(self.clk)

        # Check immediate reset
        reset_bin = int(self.counter_bin.value)
        reset_gray = int(self.counter_gray.value)
        if reset_bin != 0 or reset_gray != 0:
            self.log.error(f"Reset failed: Bin={reset_bin}, Gray={reset_gray}{self.get_time_ns_str()}")

        self.rst_n.value = 1
        await self.wait_cycles(5)

    async def generate_all_wavedrom_scenarios(self):
        """Generate all Binary-Gray counter WaveDrom scenarios.

        Follows FIFO pattern - all scenarios captured in one sampling session.
        No temporal constraints needed - direct waveform generation.
        """
        self.log.info(f"=== Generating All Binary-Gray Counter WaveDrom Scenarios ==={self.get_time_ns_str()}")

        # Scenario 1: Binary vs Gray comparison
        await self.reset_dut()
        await self.scenario_binary_vs_gray()
        await self.wait_cycles(10)  # Separation between scenarios

        # Scenario 2: Single-bit transitions
        await self.reset_dut()
        await self.scenario_single_bit_transitions()
        await self.wait_cycles(10)

        # Scenario 3: Lookahead signal
        await self.reset_dut()
        await self.scenario_lookahead_signal()
        await self.wait_cycles(10)

        # Scenario 4: Enable and reset
        await self.reset_dut()
        await self.scenario_enable_and_reset()
        await self.wait_cycles(10)

        self.log.info(f"✓ All Binary-Gray Counter WaveDrom scenarios generated{self.get_time_ns_str()}")
