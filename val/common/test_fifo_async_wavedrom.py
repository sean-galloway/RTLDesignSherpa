# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_async_wavedrom
# Purpose: WaveDrom waveform generation for fifo_async showcasing Gray code CDC
#
# Documentation: docs/markdown/RTLCommon/fifo_async.md
# Subsystem: tests
#
# Author: Claude Code (sean galloway)
# Created: 2025-10-20

"""
WaveDrom Waveform Generation for Async FIFO (Standard Gray Code)

This test generates high-quality waveforms showcasing the fifo_async
implementation using standard Gray code for clock domain crossing.

KEY FEATURES TO SHOWCASE:
1. Standard Gray code pointer synchronization
2. Power-of-2 depth requirement
3. Efficient resource usage (logarithmic pointer width)
4. Cross-domain pointer transitions
5. Comparison point for fifo_async_div2 (Johnson counter variant)

WAVEDROM SCENARIOS (v1.2 Requirements):
- Quality over quantity: 3-4 focused scenarios
- Clock signals ALWAYS first
- 2-3 initial setup cycles
- Meaningful signal grouping
- Arrows show causal relationships only

SCENARIOS:
1. Basic write-fill-read-empty cycle (standard operation)
2. Cross-domain Gray code synchronization
3. Power-of-2 depth utilization
4. Almost-full/almost-empty flag operation
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run


# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge, TemporalConstraint, TemporalEvent,
    SignalTransition, TemporalRelation
)
from CocoTBFramework.components.wavedrom.wavejson_gen import WaveJSONGenerator
from CocoTBFramework.components.shared.field_config import FieldConfig


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
                max_window_size=200,  # Large enough to capture FIFO scenarios
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

    async def scenario_write_fill_read_empty(self):
        """
        SCENARIO 1: Basic write-fill-read-empty cycle

        Demonstrates standard async FIFO operation with Gray code CDC.
        """
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
        for i in range(self.TEST_DEPTH):
            self.dut.read.value = 1
            await RisingEdge(self.rd_clk)
            self.dut.read.value = 0
            await self.wait_clocks(self.rd_clk_name, 2)

        await self.wait_clocks(self.rd_clk_name, 5)
        self.log.info("✓ Scenario 1 complete")

    async def scenario_gray_code_sync(self):
        """
        SCENARIO 2: Gray code pointer synchronization

        Demonstrates efficient Gray code CDC with logarithmic pointer width.
        """
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
        for i in range(4):
            self.dut.read.value = 1
            await RisingEdge(self.rd_clk)
            self.dut.read.value = 0
            await self.wait_clocks(self.rd_clk_name, 4)

        await self.wait_clocks(self.rd_clk_name, 5)
        self.log.info("✓ Scenario 2 complete")

    async def scenario_power_of_2_depth(self):
        """
        SCENARIO 3: Power-of-2 depth utilization

        Demonstrates efficient addressing with power-of-2 depth.
        """
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
        for i in range(self.TEST_DEPTH):
            self.dut.read.value = 1
            await RisingEdge(self.rd_clk)
            self.dut.read.value = 0
            await self.wait_clocks(self.rd_clk_name, 1)

        await self.wait_clocks(self.rd_clk_name, 5)
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


@cocotb.test(timeout_time=500, timeout_unit="us")
async def fifo_async_wavedrom_test(dut):
    """Generate WaveDrom waveforms for fifo_async showcasing Gray code CDC - per scenario."""
    import shutil
    import subprocess

    tb = FifoAsyncWaveDromTB(
        dut,
        wr_clk=dut.wr_clk,
        wr_rstn=dut.wr_rst_n,
        rd_clk=dut.rd_clk,
        rd_rstn=dut.rd_rst_n
    )

    seed = int(os.environ.get('SEED', '12345'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    await tb.start_clock('wr_clk', tb.TEST_CLK_WR, 'ns')
    await tb.start_clock('rd_clk', tb.TEST_CLK_RD, 'ns')

    await tb.assert_reset()
    await tb.wait_clocks('wr_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('wr_clk', 5)

    tb.setup_wavedrom()

    # Output directory for waveforms
    output_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.dirname(__file__))),
        'docs', 'markdown', 'assets', 'WAVES', 'fifo_async'
    )
    os.makedirs(output_dir, exist_ok=True)

    # Scenario definitions: (method, output_filename)
    scenarios = [
        (tb.scenario_write_fill_read_empty, "fifo_async_write_fill_read_empty.json"),
        (tb.scenario_gray_code_sync, "fifo_async_gray_code_sync.json"),
        (tb.scenario_power_of_2_depth, "fifo_async_power_of_2_depth.json"),
    ]

    try:
        for scenario_method, output_filename in scenarios:
            # Reset and prepare for this scenario
            await tb.assert_reset()
            await tb.wait_clocks('wr_clk', 3)
            await tb.deassert_reset()
            await tb.wait_clocks('wr_clk', 2)

            # Clear previous constraint windows
            if tb.wave_solver:
                tb.wave_solver.clear_windows()

            # Start sampling for this scenario
            if tb.wave_solver:
                await tb.wave_solver.start_sampling()

            # Run the scenario
            await scenario_method()
            await tb.wait_clocks('wr_clk', 2)

            # Stop and generate waveform
            if tb.wave_solver:
                await tb.wave_solver.stop_sampling()
                await tb.wave_solver.solve_and_generate()

                results = tb.wave_solver.get_results()
                solutions = results.get('solutions', [])

                if solutions:
                    # Find the most recently generated JSON file
                    import glob
                    json_files = glob.glob("fifo_async_capture_*.json")
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

        tb.log.info("🎉 FIFO ASYNC WAVEDROM GENERATION COMPLETE! 🎉")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('wr_clk', 10)


@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period", [
    (8, 8, 10, 12),   # Power-of-2 depth, different clocks
])
def test_fifo_async_wavedrom(request, data_width, depth, wr_clk_period, rd_clk_period):
    """Pytest wrapper for fifo_async WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "fifo_async"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bingray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "bin2gray.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "gray2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_w{w_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')


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
        'TEST_CLK_WR': str(wr_clk_period),
        'TEST_CLK_RD': str(rd_clk_period),
        'TEST_MODE': 'fifo_mux',
        'TEST_KIND': 'async',
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    compile_args = []
    sim_args = []
    plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running FIFO Async WaveDrom Generation")
    print(f"Showcasing Gray Code CDC Mechanism")
    print(f"Width: {data_width}, Depth: {depth}")
    print(f"Write CLK: {wr_clk_period}ns, Read CLK: {rd_clk_period}ns")
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
        print(f"✓ FIFO Async WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ FIFO Async WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
