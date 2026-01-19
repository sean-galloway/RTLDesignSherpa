# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_sync_wavedrom
# Purpose: WaveDrom waveform generation for fifo_sync (synchronous FIFO)
#
# Documentation: docs/markdown/RTLCommon/fifo_sync.md
# Subsystem: tests
#
# Author: Claude Code (sean galloway)
# Created: 2025-10-20

"""
WaveDrom Waveform Generation for Synchronous FIFO

This test generates high-quality waveforms showcasing the fifo_sync
implementation for single clock domain operation.

KEY FEATURES TO SHOWCASE:
1. Single clock domain operation (no CDC complexity)
2. Simple pointer management (binary counters)
3. Back-to-back operations capability
4. Flow control with full/empty flags
5. Comparison baseline for async variants

WAVEDROM SCENARIOS (v1.2 Requirements):
- Quality over quantity: 3-4 focused scenarios
- Clock signal ALWAYS first
- 2-3 initial setup cycles
- Meaningful signal grouping
- Arrows show causal relationships only

SCENARIOS:
1. Basic write-fill-read-empty cycle
2. Back-to-back write and read operations
3. Simultaneous write-read ping-pong
4. Full/empty flag transitions
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig

class FifoSyncWaveDromTB(FifoBufferTB):
    """
    Extended FIFO testbench with WaveDrom support for synchronous FIFO.

    Inherits all FIFO test functionality from FifoBufferTB and adds WaveDrom
    waveform capture capabilities for single clock domain operation.
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
        Set up WaveDrom system for synchronous FIFO waveform capture.

        Focuses on signals that demonstrate simple single-clock operation:
        - Single clock domain
        - Write and read interfaces
        - Binary pointer management (simpler than async)
        - Full/empty flags
        """
        try:
            self.log.info("Setting up WaveDrom for Synchronous FIFO...")

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
            # Group 1: Clock and Reset (ALWAYS FIRST)
            clock_signals = ['clk', 'rst_n']
            self.wave_generator.add_interface_group("Clock & Reset", clock_signals)

            # Group 2: Write Interface
            write_signals = ['write', 'wr_data', 'wr_full', 'wr_almost_full']
            self.wave_generator.add_interface_group("Write Interface", write_signals)

            # Group 3: Read Interface
            read_signals = ['read', 'rd_data', 'rd_empty', 'rd_almost_empty']
            self.wave_generator.add_interface_group("Read Interface", read_signals)

            # Group 4: Status
            status_signals = ['count']  # Internal count if visible
            self.wave_generator.add_interface_group("Status", status_signals)

            # Create temporal constraint solver
            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.field_config_wave
            )

            # Add single clock group
            self.wave_solver.add_clock_group(
                name="clk",
                clock_signal=self.wr_clk,  # Same clock for sync FIFO
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.field_config_wave
            )

            # Define signal mappings
            # Note: Sync FIFO uses different signal names (no wr_/rd_ prefixes on clk)
            fifo_signals = {
                'clk': 'clk',
                'rst_n': 'rst_n',
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

            self.log.info("✓ WaveDrom setup complete for Synchronous FIFO")

        except Exception as e:
            self.log.error(f"Failed to setup WaveDrom: {e}")
            import traceback
            traceback.print_exc()
            self.wave_solver = None
            self.wave_generator = None

    async def scenario_write_fill_read_empty(self):
        """
        SCENARIO 1: Basic write-fill-read-empty cycle

        Demonstrates basic synchronous FIFO operation.
        """
        self.log.info("=== Scenario 1: Write-Fill-Read-Empty (Sync FIFO) ===")

        # WAVEDROM REQUIREMENT: 2-3 initial setup cycles
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

        # Read everything out (same clock domain)
        for i in range(self.TEST_DEPTH):
            self.dut.read.value = 1
            await RisingEdge(self.wr_clk)  # Same clock
            self.dut.read.value = 0
            await self.wait_clocks(self.wr_clk_name, 2)

        await self.wait_clocks(self.wr_clk_name, 5)
        self.log.info("✓ Scenario 1 complete")

    async def scenario_back_to_back(self):
        """
        SCENARIO 2: Back-to-back write and read operations

        Demonstrates maximum throughput capability of sync FIFO.
        """
        self.log.info("=== Scenario 2: Back-to-Back Operations ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Back-to-back writes
        for i in range(5):
            packet = FIFOPacket(self.field_config)
            packet.data = 0x200 + i
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 1)  # Minimal delay

        await self.wait_clocks(self.wr_clk_name, 3)

        # Back-to-back reads
        for i in range(5):
            self.dut.read.value = 1
            await RisingEdge(self.wr_clk)
            self.dut.read.value = 0
            await self.wait_clocks(self.wr_clk_name, 1)

        await self.wait_clocks(self.wr_clk_name, 5)
        self.log.info("✓ Scenario 2 complete")

    async def scenario_simultaneous_write_read(self):
        """
        SCENARIO 3: Simultaneous write and read (ping-pong)

        Demonstrates sync FIFO ability to write and read in same cycle.
        """
        self.log.info("=== Scenario 3: Simultaneous Write-Read ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Pre-fill FIFO halfway
        for i in range(self.TEST_DEPTH // 2):
            packet = FIFOPacket(self.field_config)
            packet.data = 0x300 + i
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 1)

        await self.wait_clocks(self.wr_clk_name, 3)

        # Simultaneous read and write (steady-state operation)
        for i in range(6):
            # Write new data
            packet = FIFOPacket(self.field_config)
            packet.data = 0x3A0 + i
            await self.write_master.send(packet)

            # Read old data (same cycle)
            self.dut.read.value = 1
            await RisingEdge(self.wr_clk)
            self.dut.read.value = 0

        await self.wait_clocks(self.wr_clk_name, 5)
        self.log.info("✓ Scenario 3 complete")

    async def scenario_flag_transitions(self):
        """
        SCENARIO 4: Full/empty flag transitions

        Demonstrates flag behavior at boundaries.
        """
        self.log.info("=== Scenario 4: Flag Transitions ===")

        await self.wait_clocks(self.wr_clk_name, 3)

        # Fill to trigger wr_full
        for i in range(self.TEST_DEPTH):
            packet = FIFOPacket(self.field_config)
            packet.data = 0x400 + i
            await self.write_master.send(packet)
            await self.wait_clocks(self.wr_clk_name, 1)

        # Observe full flag
        await self.wait_clocks(self.wr_clk_name, 5)

        # Empty to trigger rd_empty
        for i in range(self.TEST_DEPTH):
            self.dut.read.value = 1
            await RisingEdge(self.wr_clk)
            self.dut.read.value = 0
            await self.wait_clocks(self.wr_clk_name, 1)

        # Observe empty flag
        await self.wait_clocks(self.wr_clk_name, 5)

        self.log.info("✓ Scenario 4 complete")

    async def generate_all_wavedrom_scenarios(self):
        """Generate all synchronous FIFO WaveDrom scenarios."""
        self.log.info("=== Generating All Synchronous FIFO WaveDrom Scenarios ===")

        await self.scenario_write_fill_read_empty()
        await self.wait_clocks(self.wr_clk_name, 10)

        await self.scenario_back_to_back()
        await self.wait_clocks(self.wr_clk_name, 10)

        await self.scenario_simultaneous_write_read()
        await self.wait_clocks(self.wr_clk_name, 10)

        await self.scenario_flag_transitions()
        await self.wait_clocks(self.wr_clk_name, 10)

        self.log.info("✓ All Synchronous FIFO WaveDrom scenarios generated")

@cocotb.test(timeout_time=500, timeout_unit="us")
async def fifo_sync_wavedrom_test(dut):
    """Generate WaveDrom waveforms for synchronous FIFO."""
    tb = FifoSyncWaveDromTB(
        dut,
        wr_clk=dut.clk,
        wr_rstn=dut.rst_n,
        rd_clk=None,  # Same clock
        rd_rstn=None  # Same reset
    )

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start single clock
    await tb.start_clock('clk', tb.TEST_CLK_WR, 'ns')

    # Reset sequence
    await tb.assert_reset()
    await tb.wait_clocks('clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('clk', 5)

    # Set up WaveDrom
    tb.setup_wavedrom()

    if tb.wave_solver:
        await tb.wave_solver.start_sampling()

    try:
        await tb.generate_all_wavedrom_scenarios()

        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
            tb.wave_solver.debug_status()
            results = tb.wave_solver.get_results()

            tb.log.info(f"WaveDrom Results: {len(results['solutions'])} solutions")
            tb.log.info("🎉 SYNCHRONOUS FIFO WAVEDROM GENERATION COMPLETE! 🎉")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('clk', 10)

@pytest.mark.parametrize("data_width, depth, clk_period", [
    (8, 8, 10),   # Power-of-2 depth, single clock
])
def test_fifo_sync_wavedrom(request, data_width, depth, clk_period):
    """Pytest wrapper for synchronous FIFO WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "fifo_sync"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cl_str = TBBase.format_dec(clk_period, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_w{w_str}_d{d_str}_cl{cl_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=[rtl_dict['rtl_amba_includes']]

    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': '0',
        'INSTANCE_NAME': '"wavedrom_fifo"'
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(clk_period),
        'TEST_CLK_RD': str(clk_period),  # Same as write clock
        'TEST_MODE': 'fifo_mux',
        'TEST_KIND': 'sync',
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    compile_args = []
    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running Synchronous FIFO WaveDrom Generation")
    print(f"Single Clock Domain Operation")
    print(f"Width: {data_width}, Depth: {depth}")
    print(f"CLK: {clk_period}ns")
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
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ Synchronous FIFO WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Synchronous FIFO WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
