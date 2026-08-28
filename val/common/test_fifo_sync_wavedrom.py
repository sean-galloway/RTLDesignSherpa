# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_sync_wavedrom
# Purpose: WaveDrom waveform generation for fifo_sync (synchronous FIFO)
#
# Documentation: docs/markdown/rtl-common/fifo_sync.md
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

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.fifo.fifo_buffer import FifoBufferTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge,
    TemporalConstraint, TemporalEvent, SignalTransition, TemporalRelation
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

            # (no Status group: fifo_sync leaves fifo_control's count port
            # unconnected, so there is nothing to bind a 'count' trace to)

            # Create temporal constraint solver
            self.wave_solver = TemporalConstraintSolver(
                dut=self.dut,
                log=self.log,
                debug_level=2,
                wavejson_generator=self.wave_generator,
                default_field_config=self.field_config_wave
            )

            # Add single clock group. The name MUST be 'default': that is the
            # clock_group every TemporalConstraint defaults to, and the
            # sampler drops constraints whose group name does not match —
            # under any other name the windows stay at 0 cycles forever.
            self.wave_solver.add_clock_group(
                name="default",
                clock_signal=self.wr_clk,  # Same clock for sync FIFO
                edge=ClockEdge.RISING,
                sample_delay_ns=0.1,
                field_config=self.field_config_wave
            )

            # Bind signals UNPREFIXED, matching the names the interface groups
            # and the constraints below use. add_interface() would prefix every
            # binding with 'fifo_', so nothing would ever line up — that
            # mismatch is half of why this generator emitted no JSON
            # (COMMON-020); the gaxi fifo wavedrom test is the pattern.
            for sig in ('clk', 'rst_n', 'write', 'wr_full', 'wr_almost_full',
                        'read', 'rd_empty', 'rd_almost_empty'):
                self.wave_solver.add_signal_binding(sig, sig)
            for sig in ('wr_data', 'rd_data'):
                self.wave_solver.add_signal_binding(
                    sig, sig, self.field_config_wave.get_field(sig))

            # Register the temporal constraints — the other (and larger) half
            # of COMMON-020: without at least one add_constraint() the sampling
            # loop iterates an empty set and no window is ever captured. Each
            # constraint keys on a distinct single-signal transition that the
            # scenarios produce deterministically, so one long sampling session
            # captures all four (the solver auto-solves as each rolling window
            # fills and stops at max_matches).
            layout = [
                'clk', 'rst_n', '|',
                ['Write', 'write', 'wr_data', 'wr_full', 'wr_almost_full'], '|',
                ['Read', 'read', 'rd_data', 'rd_empty', 'rd_almost_empty'],
            ]
            scenarios = [
                # (name, signal, from, to, window, ctx_before, edges)
                ('fifo_sync_write_empty', 'write', 0, 1, 12, 3,
                 [('wr_data', 'rd_data', '->', 'data')]),
                ('fifo_sync_full_flag', 'wr_full', 0, 1, 20, 4,
                 [('write', 'wr_full', '->', 'fill')]),
                ('fifo_sync_empty_flag', 'rd_empty', 0, 1, 20, 4,
                 [('read', 'rd_empty', '->', 'drain')]),
                ('fifo_sync_almost_full', 'wr_almost_full', 0, 1, 16, 3,
                 [('write', 'wr_almost_full', '->', 'near-full')]),
            ]
            for name, sig, frm, to, window, ctx, edges in scenarios:
                self.wave_solver.add_constraint(TemporalConstraint(
                    name=name,
                    events=[TemporalEvent(f"{name}_ev", SignalTransition(sig, frm, to))],
                    temporal_relation=TemporalRelation.SEQUENCE,
                    max_window_size=window,
                    context_cycles_before=ctx,
                    context_cycles_after=2,
                    signals_to_show=layout,
                    edges=edges,
                ))

            self.log.info("✓ WaveDrom setup complete for Synchronous FIFO "
                          f"({len(scenarios)} constraints registered)")

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

        # TEST_LEVEL gates HOW MANY scenarios are produced, never the content
        # of any one: the committed JSON for a scenario must be byte-identical
        # at every level or the docs' diagrams would depend on how the suite
        # was invoked. gate stops here as a smoke check; func and full emit the
        # complete set, so the normal regeneration path always writes them all.
        _lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
        if _lvl not in ('gate', 'func', 'full'):
            _lvl = 'gate'
        if _lvl == 'gate':
            self.log.info("TEST_LEVEL=gate: emitted 2 of 4 scenarios (smoke)")
            return

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

    # The scenarios below drive dut.read by hand to stage exact fill/drain
    # shapes, but FifoBufferTB also starts an auto-consuming FIFOSlave whose
    # randomizer drains the FIFO on its own schedule — with it alive the FIFO
    # never reaches full (wr_full/wr_almost_full never assert, and those
    # constraints can never match) and the diagrams are not reproducible.
    # Kill it and own the read pin.
    tb.read_slave.kill()
    dut.read.value = 0

    # Set up WaveDrom. A failed setup nulls wave_solver and every wavedrom
    # step below is guarded on it, so without this assert a broken setup
    # would sail through as a pass with no JSON — the COMMON-020 failure
    # mode through a different door.
    tb.setup_wavedrom()
    assert tb.wave_solver is not None, \
        "WaveDrom setup failed (see log above) — cannot generate wave JSON"

    if tb.wave_solver:
        await tb.wave_solver.start_sampling()

    try:
        await tb.generate_all_wavedrom_scenarios()

        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
            # Actually solve. Without this the sampling loop iterates an empty
            # constraint set, no window is ever captured, and the run reports
            # "0 solutions" and PASSES -- a generator whose entire deliverable
            # is the wave JSON, producing none.
            await tb.wave_solver.solve_and_generate()
            tb.wave_solver.debug_status()
            results = tb.wave_solver.get_results()

            n = len(results['solutions'])
            tb.log.info(f"WaveDrom Results: {n} solutions")
            tb.log.info(f"Satisfied: {results['satisfied_constraints']}")
            if results['failed_constraints']:
                tb.log.warning(f"Unsatisfied: {results['failed_constraints']}")
            # The entire deliverable of this test is the wave JSON. Zero
            # solutions means the generator emitted nothing, which is exactly
            # the silent failure COMMON-020 existed for — fail loudly.
            assert n > 0, (
                "NO wave JSON produced: the constraint solver found no "
                "solutions. The generator's whole deliverable is the wave "
                "JSON, so an empty result is a failure, never a pass "
                "(COMMON-020).")
            tb.log.info("Synchronous FIFO wavedrom generation complete")

    finally:
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.wait_clocks('clk', 10)

def _wavedrom_grid(gate, func, full):
    """REG_LEVEL grid for a wavedrom generator.

    These produce the wave JSON the docs embed rather than a pass/fail check,
    so the depth rule sits differently for them -- but a diagram set still has
    a cheap and a comprehensive form, so the grid is not optional
    (test-runner.md: both mechanisms are a hard requirement).
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    return {'GATE': gate, 'FULL': full}.get(reg_level, func)

@pytest.mark.parametrize("data_width, depth, clk_period",
                         _wavedrom_grid([(8, 8, 10)], [(8, 8, 10), (16, 16, 10)],
                                        [(8, 8, 10), (16, 16, 10), (32, 8, 10)]))
def test_fifo_sync_wavedrom(request, data_width, depth, clk_period):
    """Pytest wrapper for synchronous FIFO WaveDrom generation."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "fifo_sync"
    toplevel = dut_name

    # Sources come from the filelist, never a hand-listed array: the array
    # here omitted the include dirs and reset_defs.svh the filelist carries,
    # and a dependency added to the module is invisible to it ([[filelists]]).
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/fifo_sync.f')

    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cl_str = TBBase.format_dec(clk_period, 3)
    test_name_plus_params = f"test_{dut_name}_wavedrom_w{w_str}_d{d_str}_cl{cl_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # (the hand-built include list that used to sit here OVERWROTE the one
    # get_sources_from_filelist returned above -- an assignment, not a
    # kwarg, so the filelist's include dirs were silently discarded)

    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': '0',
    }

    extra_env = {
        # Depth knob. Without this the TB reads TEST_LEVEL's default on every
        # run, so its gate/func/full branches are unreachable no matter what
        # REG_LEVEL selects ([[test-runner]]: both mechanisms are required,
        # and a mechanism nothing exports is not one).
        'TEST_LEVEL': os.environ.get('REG_LEVEL', 'FUNC').lower(),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        # Wavedrom generators produce the wave JSON the docs embed, so their
        # stimulus must be REPRODUCIBLE: a random seed per run means the
        # committed diagram changes for no reason. Fixed default, still
        # overridable with SEED=... for a one-off experiment.
        'SEED': os.environ.get('SEED', '12345'),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CLK_WR': str(clk_period),
        'TEST_CLK_RD': str(clk_period),  # Same as write clock
        'TEST_MODE': 'fifo_mux',
        'TEST_KIND': 'sync',
        'WAVEDROM_SHOW_STATUS': '1',
        'ENABLE_WAVEDROM': '1'
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]


    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this

    # the run produces no coverage.dat at all and `make coverage-report`

    # silently reports 0.0% from 0 merged files.

    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

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
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ Synchronous FIFO WaveDrom generation PASSED")
    except Exception as e:
        print(f"✗ Synchronous FIFO WaveDrom generation FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
