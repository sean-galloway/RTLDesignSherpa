# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FifoAsyncWaveDromTB
# Purpose: WaveDrom scenario TB for the async FIFO
#
# Subsystem: cdc
# Author: sean galloway
"""WaveDrom scenario testbench for fifo_async (rtl/cdc/fifo_async.sv).

    NOT gaxi_fifo_async -- that is a different module in rtl/amba/gaxi with a
    valid/ready interface. This DUT has the write/wr_data/wr_full and
    read/rd_data/rd_empty ports the wavedrom constraints key on, and the test
    builds it from rtl/cdc/filelists/fifo_async.f.

Moved out of val/cdc/test_fifo_async_wavedrom.py (CDC-004): a 237-line TB
class lived inside its own 526-line test file, against the convention every
other TB here follows -- the cdc wavedrom siblings
(counter_johnson_wavedrom_tb, counter_bingray_wavedrom_tb) already live here.
The class body is unchanged by the move.
"""

from cocotb.triggers import RisingEdge
from TBClasses.fifo.fifo_buffer import FifoBufferTB
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class FifoAsyncWaveDromTB(FifoBufferTB):
    """
    Extended FIFO testbench with WaveDrom support for Gray code visualization.

    Inherits all FIFO test functionality from FifoBufferTB and adds WaveDrom
    waveform capture capabilities for the standard Gray code CDC implementation.
    """

    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        super().__init__(dut, wr_clk=wr_clk, wr_rstn=wr_rstn,
                        rd_clk=rd_clk, rd_rstn=rd_rstn)

        # WaveDrom components
        self.wave_solver = None
        self.wave_generator = None
        self.field_config_wave = None

    def setup_wavedrom(self):
        """
        Set up WaveDrom system for FIFO async waveform capture.

        Focuses on signals that demonstrate Gray code CDC:
        - Both clock domains (wr_clk and rd_clk)
        - Write and read interfaces
        - Gray code pointers (if visible)
        - Full/empty and almost-full/almost-empty flags
        """
        try:
            self.log.info("Setting up WaveDrom for FIFO Async (Gray Code)...")

            # Create field configuration for FIFO signals
            self.field_config_wave = FieldConfig.from_dict(
                field_dict={
                    'wr_data': {'bits': self.DW, 'default': 0},
                    'rd_data': {'bits': self.DW, 'default': 0},
                },
                lsb_first=True
            )

            # Create WaveJSON generator
            self.wave_generator = WaveJSONGenerator(debug_level=2)

            # WAVEDROM REQUIREMENT v1.2: Signal grouping MANDATORY
            # Group 1: Clocks and Resets (ALWAYS FIRST)
            clock_signals = ['wr_clk', 'wr_rst_n', 'rd_clk', 'rd_rst_n']
            self.wave_generator.add_interface_group("Clocks & Reset", clock_signals)

            # Group 2: Write Interface
            write_signals = ['write', 'wr_data', 'wr_full', 'wr_almost_full']
            self.wave_generator.add_interface_group("Write Interface", write_signals)

            # Group 3: Read Interface
            read_signals = ['read', 'rd_data', 'rd_empty', 'rd_almost_empty']
            self.wave_generator.add_interface_group("Read Interface", read_signals)

            # Create temporal constraint solver
            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.field_config_wave
            )

            # Add clock groups for both domains
            self.wave_solver.add_clock_group(
                name="wr_clk",
                clock_signal=self.wr_clk,
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.field_config_wave
            )

            self.wave_solver.add_clock_group(
                name="rd_clk",
                clock_signal=self.rd_clk,
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.field_config_wave
            )

            # Define signal mappings
            fifo_signals = {
                'wr_clk': 'wr_clk',
                'wr_rst_n': 'wr_rst_n',
                'rd_clk': 'rd_clk',
                'rd_rst_n': 'rd_rst_n',
                'write': 'write',
                'wr_data': 'wr_data',
                'wr_full': 'wr_full',
                'wr_almost_full': 'wr_almost_full',
                'read': 'read',
                'rd_data': 'rd_data',
                'rd_empty': 'rd_empty',
                'rd_almost_empty': 'rd_almost_empty',
            }

            self.wave_solver.add_interface("fifo", fifo_signals, field_config=self.field_config_wave)

            # Add dummy constraint to trigger waveform generation
            # This constraint looks for write signal going high
            write_constraint = TemporalConstraint(
                name="fifo_async_capture",
                events=[
                    TemporalEvent("write_high", SignalTransition("fifo_write", 0, 1))
                ],
                temporal_relation=TemporalRelation.SEQUENCE,
                # The emitted wave is sliced at
                #   start = seq_start - context_before
                #   end   = seq_end + context_after + post_match_cycles + 1
                # and with context_* left at None they resolve to
                # max(3, window_size // 4). At window=200 that gave ~50 trailing
                # samples, which ends the capture while the fill is still
                # finishing -- so BFM reads, which can only follow the fill,
                # never appeared. max_window_size alone changes nothing; the
                # trailing context is the knob. (CDC-003)
                max_window_size=300,
                context_cycles_before=5,
                context_cycles_after=150,
                required=False,
                max_matches=10,  # Allow multiple captures
                clock_group="wr_clk",
                signals_to_show=['fifo_wr_clk', 'fifo_wr_rst_n', 'fifo_rd_clk', 'fifo_rd_rst_n',
                                'fifo_write', 'fifo_wr_data', 'fifo_wr_full', 'fifo_wr_almost_full',
                                'fifo_read', 'fifo_rd_data', 'fifo_rd_empty', 'fifo_rd_almost_empty']
            )
            write_constraint.skip_boundary_detection = True
            self.wave_solver.add_constraint(write_constraint)

            self.log.info("✓ WaveDrom setup complete for FIFO Async")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            import traceback
            traceback.print_exc()
            self.wave_solver = None
            self.wave_generator = None


    # ---- CDC-003: reads go through the BFM, not the pin -------------------
    # FifoBufferTB starts an auto-consuming FIFOSlave; poking dut.read by hand
    # contends with it. Instead give the slave an exact read_delay SEQUENCE.
    # FlexRandomizer takes a list and LOOPS it (value = sequence[0];
    # sequence.rotate(-1)), so the first consult holds the reader off while the
    # FIFO fills and every consult after that is the scenario's drain spacing.
    # One randomizer, no mid-scenario switch, no sleeping-slave latency.
    def _read_schedule(self, fill_hold, spacing):
        """read_delay = [fill_hold, spacing] looping forever."""
        self.read_slave.set_randomizer(
            FlexRandomizer({'read_delay': [fill_hold, spacing]}))

    async def _await_drain(self, timeout_cycles=400):
        """Wait for the BFM to empty the FIFO; the sequence paces the reads."""
        empty = getattr(self.dut, 'rd_empty', None)
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.rd_clk_name, 1)
            if empty is not None and empty.value.is_resolvable and empty.value.integer == 1:
                return True
        self.log.error("drain did not complete within timeout")
        return False

    async def scenario_write_fill_read_empty(self):
        """
        SCENARIO 1: Basic write-fill-read-empty cycle

        Demonstrates standard async FIFO operation with Gray code CDC.
        """
        self._read_schedule(fill_hold=44, spacing=2)
        self.log.info("=== Scenario 1: Write-Fill-Read-Empty (Gray Code) ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Write until almost full
        num_writes = self.TEST_DEPTH - 1
        for i in range(num_writes):
            packet = FIFOPacket(self.field_config)
            packet.data = 0x100 + i
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 2)

        # Fill completely
        packet = FIFOPacket(self.field_config)
        packet.data = 0x1FF
        await self.write_master.send(packet)
        await self.wait_clocks(self.wr_clk_name, 5)

        # Read everything out
        await self.wait_clocks(self.rd_clk_name, 3)
        await self._await_drain()
        self.log.info("✓ Scenario 1 complete")

    async def scenario_gray_code_sync(self):
        """
        SCENARIO 2: Gray code pointer synchronization

        Demonstrates efficient Gray code CDC with logarithmic pointer width.
        """
        self._read_schedule(fill_hold=31, spacing=4)
        self.log.info("=== Scenario 2: Gray Code Synchronization ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Writes to show Gray code progression
        for i in range(4):
            packet = FIFOPacket(self.field_config)
            packet.data = 0x200 + i
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 5)

        await self.wait_clocks(self.wr_clk_name, 10)

        # Reads with async clock
        await self.wait_clocks(self.rd_clk_name, 3)
        await self._await_drain()
        self.log.info("✓ Scenario 2 complete")

    async def scenario_power_of_2_depth(self):
        """
        SCENARIO 3: Power-of-2 depth utilization

        Demonstrates efficient addressing with power-of-2 depth.
        """
        self._read_schedule(fill_hold=33, spacing=1)
        self.log.info("=== Scenario 3: Power-of-2 Depth Utilization ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Fill with pattern showing full depth
        for i in range(self.TEST_DEPTH):
            packet = FIFOPacket(self.field_config)
            packet.data = (i << 4) | i  # Pattern: 0x00, 0x11, 0x22, ...
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 1)

        await self.wait_clocks(self.wr_clk_name, 5)

        # Read out showing wrap-around
        await self.wait_clocks(self.rd_clk_name, 3)
        await self._await_drain()
        self.log.info("✓ Scenario 3 complete")

    async def generate_all_wavedrom_scenarios(self):
        """Generate all FIFO async WaveDrom scenarios."""
        self.log.info("=== Generating All FIFO Async WaveDrom Scenarios ===")

        await self.scenario_write_fill_read_empty()
        await self.wait_clocks(self.wr_clk_name, 10)

        await self.scenario_gray_code_sync()
        await self.wait_clocks(self.wr_clk_name, 10)

        await self.scenario_power_of_2_depth()
        await self.wait_clocks(self.wr_clk_name, 10)

        self.log.info("✓ All FIFO Async WaveDrom scenarios generated")

