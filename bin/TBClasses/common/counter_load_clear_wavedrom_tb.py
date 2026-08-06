# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterLoadClearWaveDromTB
# Purpose: Testbench for counter_load_clear_wavedrom
# Subsystem: framework
#
# Extracted from val/common/test_counter_load_clear_wavedrom.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.triggers import RisingEdge, Timer, ClockCycles
import math
from TBClasses.shared.tbbase import TBBase
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

        # The scenarios load a fixed match value of 8 (scenario_clear_operation),
        # which needs a 4-bit loadval -- so MAX must be at least 16. Say that
        # here rather than let cocotb raise "Int value (8) out of range for
        # assignment of 3-bit signal" from inside a scenario, which points at
        # the assignment instead of at the grid entry that caused it.
        if self.MAX_VALUE < 16:
            raise ValueError(
                f"counter_load_clear wavedrom scenarios need MAX >= 16 "
                f"(loadval is $clog2(MAX) bits and the scenarios load 8); "
                f"got MAX={self.MAX_VALUE}")

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
