# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_wavedrom_example
# Purpose: GAXI WaveDrom Comprehensive Example Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXI WaveDrom Comprehensive Example Test

Demonstrates GAXI/FIFO wavedrom timing diagrams with all critical behaviors:

1. **Write Operations:**
   - Write when empty (immediate acceptance)
   - Write when going full (shows FIFO filling up)
   - Write when full (backpressure: wr_ready=0, then acceptance when space available)
   - Back-to-back writes

2. **Read Operations:**
   - Read when data available
   - Read/Write simultaneously

3. **Visualization:**
   - Clock included in all waveforms (designers need reference)
   - Internal signals shown (count, buffer state)
   - Separate wr/rd views (individual behavior)
   - Combined wr/rd views (relationship/coupling)
   - Arrows showing causality and relationships
   - Configurable trim margins (context cycles)

This is the REFERENCE EXAMPLE - copy patterns to your own tests.
"""

import os
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
import pytest
from cocotb_test.simulator import run

# Import GAXI wavedrom support
from CocoTBFramework.tbclasses.wavedrom_user.gaxi import (
    get_gaxi_field_config,
    create_gaxi_wavejson_generator,
)
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
from CocoTBFramework.tbclasses.shared.utilities import get_paths


async def run_basic_functional_test(dut):
    """Run basic functional test without waveform generation"""
    # Simple write/read verification
    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    dut.wr_data.value = 0

    await RisingEdge(dut.axi_aclk)

    # Write some data
    # IMPORTANT: Data must only change when handshake completes (valid=1 AND ready=1)
    dut.wr_valid.value = 1
    dut.wr_data.value = 0xAA
    await RisingEdge(dut.axi_aclk)
    # Only change data if previous beat was accepted (wr_ready was high)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0xBB
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0

    await RisingEdge(dut.axi_aclk)

    # Read back
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)
    assert dut.rd_data.value == 0xAA, f"Read mismatch: got {dut.rd_data.value:02x}, expected 0xAA"
    await RisingEdge(dut.axi_aclk)
    assert dut.rd_data.value == 0xBB, f"Read mismatch: got {dut.rd_data.value:02x}, expected 0xBB"
    dut.rd_ready.value = 0

    dut._log.info("✓ Basic functional test passed")


@cocotb.test(timeout_time=10, timeout_unit="sec")
async def gaxi_comprehensive_wavedrom_test(dut):
    """
    Comprehensive GAXI/FIFO/Skid Buffer waveform generation with segmented scenario capture.

    Uses SEGMENTED CAPTURE approach:
    - Each scenario captured in isolation (start/stop/solve/clear)
    - No spurious matches across scenarios
    - Cleaner, more deterministic waveforms
    - Better control over context trimming

    Comprehensive scenarios covering both FIFO and Skid Buffer behaviors:
    1. Zero-latency bypass (skid buffer) - write to empty shows immediate rd_valid
    2. Burst write until full (FIFO) - demonstrates backpressure when full
    3. Simultaneous read/write (pass-through) - count stays constant, data flows through
    4. Burst read until empty - shows rd_valid deassert when empty
    5. Fill then drain pattern - complete fill phase followed by drain phase
    6. Alternating read/write (continuous flow) - interleaved operations

    Each waveform includes:
    - Clock & Reset signals
    - Complete write interface (wr_valid, wr_ready, wr_data)
    - Complete read interface (rd_valid, rd_ready, rd_data)
    - Internal state (count, wr_xfer, rd_xfer) for debugging

    Environment Variables:
        TRIM_MODE: Waveform trimming (minimal/moderate/default)
        ENABLE_WAVEDROM: Enable waveform generation (1/0, default: 1)
    """
    # Start clock
    clock = Clock(dut.axi_aclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.axi_aresetn.value = 0
    await Timer(20, units="ns")
    dut.axi_aresetn.value = 1
    await RisingEdge(dut.axi_aclk)

    # Get test parameters
    trim_mode = os.environ.get('TRIM_MODE', 'default')
    context_before = {'minimal': 3, 'moderate': 4, 'default': 5}[trim_mode]
    context_after = {'minimal': 1, 'moderate': 3, 'default': None}[trim_mode]

    # Check if waveforms are enabled (default: yes)
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '1'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled (ENABLE_WAVEDROM=0), running test without waveforms")
        # Run basic functional test without wavedrom
        await run_basic_functional_test(dut)
        return

    # === Setup WaveDrom Infrastructure (ONCE) ===
    # Use 8-bit data for better waveform readability
    field_config = get_gaxi_field_config(data_width=8)
    wave_generator = create_gaxi_wavejson_generator(field_config, signal_prefix="")

    wave_solver = TemporalConstraintSolver(
        dut=dut,
        log=dut._log,
        wavejson_generator=wave_generator,
        default_field_config=field_config,
        debug_level=1
    )

    wave_solver.add_clock_group('default', dut.axi_aclk)

    # === Bind ALL Signals (ONCE) ===
    # Use auto_bind_signals() for protocol interfaces (DRY principle)
    # This automatically discovers and binds all GAXI protocol signals using FieldConfig

    # Auto-bind Write Interface (wr_valid, wr_ready, wr_data with field formatting)
    wave_solver.auto_bind_signals('gaxi', signal_prefix='wr_', field_config=field_config)

    # Auto-bind Read Interface (rd_valid, rd_ready, rd_data with field formatting)
    wave_solver.auto_bind_signals('gaxi', signal_prefix='rd_', field_config=field_config)

    # Manual bindings for clock, reset, and internal/custom signals
    # (these are not part of the GAXI protocol interface)
    wave_solver.add_signal_binding('clk', 'axi_aclk')
    wave_solver.add_signal_binding('rst_n', 'axi_aresetn')

    # Internal State signals (not in FieldConfig, require manual binding)
    from CocoTBFramework.components.shared.field_config import FieldDefinition
    count_field = FieldDefinition('count', 4, format='dec', description='FIFO count')
    wave_solver.add_signal_binding('count', 'count', count_field)  # 4-bit count as decimal
    wave_solver.add_signal_binding('wr_xfer', 'w_wr_xfer')  # Internal: write transfer
    wave_solver.add_signal_binding('rd_xfer', 'w_rd_xfer')  # Internal: read transfer

    # === Define Interface Groups for Waveform Organization ===
    # Note: Groups are NOT used by default - they require signal_order in constraints
    wave_generator.add_interface_group("Clock & Reset", ['clk', 'rst_n'])
    wave_generator.add_interface_group("Write Interface", ['wr_valid', 'wr_ready', 'wr_data'])
    wave_generator.add_interface_group("Read Interface", ['rd_valid', 'rd_ready', 'rd_data'])
    wave_generator.add_interface_group("Internal State", ['count', 'wr_xfer', 'rd_xfer'])

    # === Define Constraints (ONCE) ===
    # Comprehensive scenarios for FIFO/Skid Buffer behavior

    # Scenario 1: Zero-latency bypass (skid buffer feature)
    bypass_constraint = TemporalConstraint(
        name="zero_latency_bypass",
        events=[
            TemporalEvent("write_to_empty", SignalTransition("wr_valid", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=12,
        context_cycles_before=context_before,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('wr_data', 'rd_data', '->', 'data'),     # Data flow through buffer
            ('wr_xfer', 'count', '->', 'wr+'),        # Write increments count
            ('rd_xfer', 'count', '->', 'rd-'),        # Read decrements count
        ]
    )
    wave_solver.add_constraint(bypass_constraint)

    # Scenario 2: Burst write until full (FIFO characteristic)
    burst_write_constraint = TemporalConstraint(
        name="burst_write_full",
        events=[
            TemporalEvent("backpressure", SignalTransition("wr_ready", 1, 0)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=20,
        context_cycles_before=context_before,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('wr_xfer', 'count', '->', 'fill'),    # Writes increment count
        ]
    )
    wave_solver.add_constraint(burst_write_constraint)

    # Scenario 3: Simultaneous read/write (pass-through)
    simultaneous_constraint = TemporalConstraint(
        name="simultaneous_rdwr",
        events=[
            TemporalEvent("both_xfer", SignalTransition("wr_xfer", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=18,
        context_cycles_before=context_before,
        context_cycles_after=context_after,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('wr_data', 'rd_data', '->', 'data'),     # Direct data flow (pass-through)
            ('wr_xfer', 'count', '->', 'wr+'),        # Write increments
            ('rd_xfer', 'count', '->', 'rd-'),        # Read decrements (cancel)
        ]
    )
    wave_solver.add_constraint(simultaneous_constraint)

    # Scenario 4: Burst read until empty
    burst_read_constraint = TemporalConstraint(
        name="burst_read_empty",
        events=[
            TemporalEvent("read_start", SignalTransition("rd_ready", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=20,
        context_cycles_before=context_before,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('rd_xfer', 'count', '->', 'drain'),    # Reads decrement count
        ]
    )
    wave_solver.add_constraint(burst_read_constraint)

    # Scenario 5: Fill then drain pattern
    fill_drain_constraint = TemporalConstraint(
        name="fill_then_drain",
        events=[
            TemporalEvent("start_fill", SignalTransition("wr_valid", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=30,
        context_cycles_before=2,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('wr_data', 'rd_data', '->', 'buffered'),    # Data flow through buffer
        ]
    )
    wave_solver.add_constraint(fill_drain_constraint)

    # Scenario 6: Alternating read/write (continuous flow)
    alternating_constraint = TemporalConstraint(
        name="alternating_rdwr",
        events=[
            TemporalEvent("wr_start", SignalTransition("wr_valid", 0, 1)),
        ],
        temporal_relation=TemporalRelation.SEQUENCE,
        max_window_size=25,
        context_cycles_before=2,
        context_cycles_after=2,
        signals_to_show=[
            'clk', 'rst_n', '|',
            ['Write', 'wr_valid', 'wr_ready', 'wr_data'], '|',
            ['Read', 'rd_valid', 'rd_ready', 'rd_data'], '|',
            ['Internal', 'count', 'wr_xfer', 'rd_xfer']
        ],
        edges=[
            ('wr_data', 'rd_data', '~>', 'flow'),  # Continuous data flow (curved)
        ]
    )
    wave_solver.add_constraint(alternating_constraint)

    dut._log.info(f"✓ GAXI wavedrom configured: 6 comprehensive scenarios, segmented capture mode")
    dut._log.info(f"  1. Zero-latency bypass (skid buffer)")
    dut._log.info(f"  2. Burst write until full (FIFO)")
    dut._log.info(f"  3. Simultaneous read/write (pass-through)")
    dut._log.info(f"  4. Burst read until empty")
    dut._log.info(f"  5. Fill then drain pattern")
    dut._log.info(f"  6. Alternating read/write (continuous flow)")
    dut._log.info(f"  Trim mode: {trim_mode} (before={context_before}, after={context_after})")

    # === Initial Setup ===
    dut.rd_ready.value = 0
    dut.wr_valid.value = 0
    dut.wr_data.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 1: Zero-Latency Bypass (Skid Buffer Feature)
    # ========================================================================
    dut._log.info("=== Scenario 1: Zero-latency bypass (write to empty) ===")

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle: capture empty state

    # Write to empty FIFO - should see immediate rd_valid (zero-latency bypass)
    # IMPORTANT: Data must only change when handshake completes (valid=1 AND ready=1)
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x10
    await RisingEdge(dut.axi_aclk)
    # Only change data if previous beat was accepted (wr_ready was high)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x11
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 1 captured: zero-latency bypass")

    # Drain FIFO
    dut.rd_ready.value = 1
    for _ in range(4):
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 2: Burst Write Until Full (FIFO Characteristic)
    # ========================================================================
    dut._log.info("=== Scenario 2: Burst write until full ===")

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle

    # Burst write until FIFO full (depth=4)
    # IMPORTANT: Data must only change when handshake completes (valid=1 AND ready=1)
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x20
    await RisingEdge(dut.axi_aclk)
    # Only change data if previous beat was accepted (wr_ready was high)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x21
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x22
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x23
    await RisingEdge(dut.axi_aclk)
    # FIFO full - observe wr_ready go low, data must stay stable
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x24  # Only change if ready
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 2 captured: burst write until full")

    # Drain FIFO
    dut.rd_ready.value = 1
    for _ in range(4):
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 3: Simultaneous Read/Write (Pass-Through)
    # ========================================================================
    dut._log.info("=== Scenario 3: Simultaneous read/write (pass-through) ===")

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle

    # Pre-load 1 item
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x30
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x31
    await RisingEdge(dut.axi_aclk)

    # Now do simultaneous read/write (passes through FIFO)
    dut.rd_ready.value = 1
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x32
    await RisingEdge(dut.axi_aclk)  # Both wr_xfer and rd_xfer = 1
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x33
    await RisingEdge(dut.axi_aclk)  # Count stays constant
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x34
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 3 captured: simultaneous read/write")

    # Drain FIFO
    dut.rd_ready.value = 1
    for _ in range(4):
        await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 4: Burst Read Until Empty
    # ========================================================================
    dut._log.info("=== Scenario 4: Burst read until empty ===")

    # Pre-load FIFO with data
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x40
    await RisingEdge(dut.axi_aclk)
    dut.wr_data.value = 0x41
    await RisingEdge(dut.axi_aclk)
    dut.wr_data.value = 0x42
    await RisingEdge(dut.axi_aclk)
    dut.wr_data.value = 0x43
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle

    # Burst read until empty - observe rd_valid go low
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)  # Now empty
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 4 captured: burst read until empty")

    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 5: Fill Then Drain Pattern
    # ========================================================================
    dut._log.info("=== Scenario 5: Fill then drain pattern ===")

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle

    # Fill phase: write until full
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x50
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x51
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x52
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x53
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0

    # Idle (full FIFO)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # Drain phase: read until empty
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)
    dut.rd_ready.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 5 captured: fill then drain")

    await RisingEdge(dut.axi_aclk)
    await RisingEdge(dut.axi_aclk)

    # ========================================================================
    # SCENARIO 6: Alternating Read/Write (Continuous Flow)
    # ========================================================================
    dut._log.info("=== Scenario 6: Alternating read/write (continuous flow) ===")

    # Pre-load 2 items
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x60
    await RisingEdge(dut.axi_aclk)
    if dut.wr_ready.value == 1:
        dut.wr_data.value = 0x61
    await RisingEdge(dut.axi_aclk)
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.start_sampling()
    await RisingEdge(dut.axi_aclk)  # Setup cycle

    # Alternating pattern: write, read, write, read
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x62
    await RisingEdge(dut.axi_aclk)  # Write
    dut.wr_valid.value = 0
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)  # Read
    dut.rd_ready.value = 0
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x63
    await RisingEdge(dut.axi_aclk)  # Write
    dut.wr_valid.value = 0
    dut.rd_ready.value = 1
    await RisingEdge(dut.axi_aclk)  # Read
    dut.rd_ready.value = 0
    dut.wr_valid.value = 1
    dut.wr_data.value = 0x64
    await RisingEdge(dut.axi_aclk)  # Write
    dut.wr_valid.value = 0
    await RisingEdge(dut.axi_aclk)

    await wave_solver.stop_sampling()
    await wave_solver.solve_and_generate()
    wave_solver.clear_windows()
    dut._log.info("✓ Scenario 6 captured: alternating read/write")

    # === Final Report ===
    wave_solver.debug_status()

    dut._log.info(f"✓ GAXI Comprehensive Wavedrom Complete (Segmented Capture)")
    dut._log.info(f"  Total scenarios: 6")
    dut._log.info(f"  1. Zero-latency bypass (skid buffer)")
    dut._log.info(f"  2. Burst write until full (FIFO)")
    dut._log.info(f"  3. Simultaneous read/write (pass-through)")
    dut._log.info(f"  4. Burst read until empty")
    dut._log.info(f"  5. Fill then drain pattern")
    dut._log.info(f"  6. Alternating read/write (continuous flow)")
    dut._log.info(f"  Trim mode: {trim_mode}")


# ==============================================================================
# Test Parameter Generation
# ==============================================================================
def generate_params():
    """
    Generate test parameters with waveform flag.

    Returns list of tuples: (data_width, depth, trim_mode, enable_wavedrom)

    Examples for customization:
        # Single test with waveforms:
        return [(32, 4, 'default', True)]

        # Multiple configs, only one with waveforms:
        return [
            (32, 4, 'default', True),   # This one gets waveforms
            (32, 8, 'default', False),  # No waveforms
            (64, 4, 'default', False),  # No waveforms
        ]

        # All with waveforms (for development):
        widths = [32]
        depths = [4]
        trim_modes = ['minimal', 'default', 'moderate']
        return [(w, d, t, True) for w in widths for d in depths for t in trim_modes]
    """
    # Default: Test both with and without waveforms
    return [
        (32, 4, 'default', True),    # With waveforms
        (32, 4, 'default', False),   # Without waveforms (faster)
    ]

    # Uncomment for multiple trim modes:
    # return [
    #     (32, 4, 'minimal', True),
    #     (32, 4, 'default', True),
    #     (32, 4, 'moderate', True),
    # ]

    # Uncomment for extensive testing (48 configs, only 1 with waveforms):
    # params = []
    # for width in [8, 16, 32, 64]:
    #     for depth in [2, 4, 8, 16]:
    #         for trim_mode in ['minimal', 'default', 'moderate']:
    #             # Only enable waveforms for one specific config
    #             enable_wd = (width == 32 and depth == 4 and trim_mode == 'default')
    #             params.append((width, depth, trim_mode, enable_wd))
    # return params
    #
    # This gives you:
    # - 48 total test configurations
    # - 47 fast functional tests (no waveforms)
    # - 1 full wavedrom test (32-bit, depth=4, default trim)
    # Total test count: 48 (not 96 with separate wavedrom tests!)


params = generate_params()


# ==============================================================================
# PyTest Test Runner
# ==============================================================================
@pytest.mark.parametrize("data_width, depth, trim_mode, enable_wavedrom", params)
def test_gaxi_wavedrom_example(data_width, depth, trim_mode, enable_wavedrom):
    """
    Comprehensive GAXI wavedrom test runner with parametric configuration.

    Tests GAXI/FIFO behaviors with configurable parameters and optional waveforms.

    Args:
        data_width: Data width (8, 16, 32, 64)
        depth: FIFO depth (2, 4, 8, 16)
        trim_mode: Waveform trimming (minimal/default/moderate)
        enable_wavedrom: Generate waveforms (True/False)
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_common': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "gaxi_skid_buffer"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
    ]
    parameters = {
        'DATA_WIDTH': data_width,
        'DEPTH': depth
    }

    # Include data width and depth in test name for clarity
    wd_flag = "wd" if enable_wavedrom else "nowd"
    test_name = f"test_{worker_id}_{dut_name}_w{data_width}_d{depth}_{trim_mode}_{wd_flag}"

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'TRIM_MODE': trim_mode,
        'ENABLE_WAVEDROM': '1' if enable_wavedrom else '0',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        '-Wall',
        '-Wno-UNUSED',
        '-Wno-DECLFILENAME',
        '-Wno-WIDTHTRUNC',
        '-Wno-PINCONNECTEMPTY',
    ]

    for param, value in parameters.items():
        compile_args.append(f'-G{param}={value}')

    run(
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # VCD controlled by compile_args, not cocotb-test
        testcase="gaxi_comprehensive_wavedrom_test",
        includes=[rtl_dict['rtl_amba_includes']]
    )


if __name__ == "__main__":
    """
    Run comprehensive GAXI wavedrom example.

    Usage:
        pytest val/amba/test_gaxi_wavedrom_example.py -v
        pytest val/amba/test_gaxi_wavedrom_example.py::test_gaxi_wavedrom_example[default] -v
    """
    pass
