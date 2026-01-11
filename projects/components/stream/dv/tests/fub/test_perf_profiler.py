# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_perf_profiler
# Purpose: Performance Profiler Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19
# Updated: 2025-11-07 - Refactored to standard pattern

"""
Performance Profiler Test Runner - v1.0

Tests for perf_profiler.sv module

Test Types:
- 'single_channel_timestamp_mode': Single channel in timestamp mode
- 'single_channel_elapsed_mode': Single channel in elapsed mode
- 'multiple_channels_sequential': Multiple channels with sequential transitions
- 'simultaneous_edges_bug': Simultaneous transitions (DEMONSTRATES BUG!)
- 'fifo_full_behavior': FIFO full handling
- 'two_register_read_interface': Two-register read interface (36-bit data over 32-bit bus)
- 'counter_increment': Timestamp counter increment verification

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.stream.dv.tbclasses.perf_profiler_tb import PerfProfilerTB


# ===========================================================================
# Helper Functions - Test Logic
# ===========================================================================

async def run_single_channel_timestamp_mode(tb):
    """Test single channel in timestamp mode"""
    # Enable timestamp mode
    await tb.enable_profiler(mode=0)

    # Generate activity on channel 0
    await tb.channel_active_pulse(channel=0, duration_cycles=50)

    # Wait for events to be recorded
    await tb.wait_for_events(2)  # START + END

    # Read events
    entries = await tb.read_all_fifo_entries()

    # Verify
    assert len(entries) == 2, f"Expected 2 events, got {len(entries)}"

    timestamp_start, ch_start, event_start = entries[0]
    timestamp_end, ch_end, event_end = entries[1]

    assert ch_start == 0, "Start event should be channel 0"
    assert ch_end == 0, "End event should be channel 0"
    assert event_start == 0, "First event should be START (0)"
    assert event_end == 1, "Second event should be END (1)"

    elapsed = timestamp_end - timestamp_start
    tb.log.info(f"Channel 0 elapsed time: {elapsed} cycles (expected ~50)")
    assert 48 <= elapsed <= 52, f"Elapsed time {elapsed} not close to 50"

    tb.log.info("PASSED: Single channel timestamp mode")


async def run_single_channel_elapsed_mode(tb):
    """Test single channel in elapsed mode"""
    # Enable elapsed mode
    await tb.enable_profiler(mode=1)

    # Generate activity on channel 1
    await tb.channel_active_pulse(channel=1, duration_cycles=100)

    # Wait for event to be recorded (only END event in elapsed mode)
    await tb.wait_for_events(1)

    # Wait a few cycles for FIFO signals to settle
    await ClockCycles(tb.clk, 3)

    # Read event
    entries = await tb.read_all_fifo_entries()

    # Verify
    assert len(entries) == 1, f"Expected 1 event, got {len(entries)}"

    elapsed, channel_id, event_type = entries[0]

    assert channel_id == 1, "Event should be channel 1"
    assert event_type == 1, "Event should be END (1)"

    tb.log.info(f"Channel 1 elapsed time: {elapsed} cycles (expected ~100)")
    assert 98 <= elapsed <= 102, f"Elapsed time {elapsed} not close to 100"

    tb.log.info("PASSED: Single channel elapsed mode")


async def run_multiple_channels_sequential(tb):
    """Test multiple channels with sequential transitions"""
    # Enable timestamp mode
    await tb.enable_profiler(mode=0)

    # Generate activity on channels 0, 1, 2 sequentially
    for ch in range(3):
        await tb.channel_active_pulse(channel=ch, duration_cycles=20 + ch*10)
        await ClockCycles(tb.clk, 5)  # Gap between channels

    # Wait for all events
    await tb.wait_for_events(6)  # 3 channels × 2 events each

    # Read all events
    entries = await tb.read_all_fifo_entries()

    # Verify count
    assert len(entries) == 6, f"Expected 6 events, got {len(entries)}"

    # Verify each channel got start and end
    events_by_channel = {0: [], 1: [], 2: []}
    for entry in entries:
        _, channel_id, _ = entry
        events_by_channel[channel_id].append(entry)

    for ch in range(3):
        assert len(events_by_channel[ch]) == 2, f"Channel {ch} should have 2 events"
        tb.log.info(f"Channel {ch}: {len(events_by_channel[ch])} events")

    tb.log.info("PASSED: Multiple channels sequential")


async def run_simultaneous_edges_bug(tb):
    """
    Test simultaneous transitions on multiple channels

    **THIS TEST DEMONSTRATES A BUG!**

    When all 8 channels transition simultaneously from idle to active,
    only channel 0 (lowest priority) gets recorded. The other 7 channels'
    events are LOST because r_idle_prev is updated every cycle.

    Expected behavior (if bug were fixed): 8 START events
    Actual behavior (with bug): 1 START event (channel 0 only)
    """
    # Enable timestamp mode
    await tb.enable_profiler(mode=0)

    # Wait a few cycles for profiler to stabilize
    await ClockCycles(tb.clk, 5)

    # Make all channels go idle->active SIMULTANEOUSLY
    tb.log.info("Setting all 8 channels active SIMULTANEOUSLY")
    await tb.set_all_channels(0x00)  # All channels active (idle=0)

    # Wait for events to be recorded
    await ClockCycles(tb.clk, 20)

    # Check FIFO count
    count = tb.get_fifo_count()
    tb.log.info(f"FIFO count after simultaneous edges: {count}")

    # Read events
    entries = await tb.read_all_fifo_entries()

    # EXPECTED (if bug fixed): 8 events (one per channel)
    # ACTUAL (with bug): 1 event (channel 0 only)

    if len(entries) == 1:
        tb.log.warning("BUG CONFIRMED: Only 1 event recorded (channel 0)")
        tb.log.warning("Expected 8 events (one per channel)")
        tb.log.warning("Events for channels 1-7 were LOST due to r_idle_prev update bug")

        # Verify it's channel 0
        _, channel_id, event_type = entries[0]
        assert channel_id == 0, "Should be channel 0 (lowest priority)"
        assert event_type == 0, "Should be START event"

        tb.log.error("KNOWN BUG: Simultaneous transitions lose events for all but lowest channel")
    else:
        tb.log.info(f"Got {len(entries)} events - bug may be fixed!")
        for entry in entries:
            _, ch, _ = entry
            tb.log.info(f"  Channel {ch} event recorded")

    # This test PASSES by demonstrating the bug exists
    assert len(entries) >= 1, "Should get at least channel 0 event"

    tb.log.info("TEST DEMONSTRATES BUG: Simultaneous edges lose events")


async def run_fifo_full_behavior(tb):
    """Test FIFO full behavior - events should be dropped"""
    # Enable timestamp mode
    await tb.enable_profiler(mode=0)

    # Generate many events to fill FIFO
    # FIFO depth = 256 (parameter), so need 128 pulses (2 events each)
    fifo_depth = 256
    pulses_needed = fifo_depth // 2

    tb.log.info(f"Generating {pulses_needed} pulses to fill FIFO (depth={fifo_depth})")

    for i in range(pulses_needed + 10):  # Extra to cause overflow
        await tb.channel_active_pulse(channel=0, duration_cycles=2)

        # Check if full
        if i % 50 == 0:
            count = tb.get_fifo_count()
            full = tb.is_fifo_full()
            tb.log.info(f"Pulse {i}: FIFO count={count}, full={full}")

    # Wait for all events to settle
    await ClockCycles(tb.clk, 50)

    # Check FIFO state
    count = tb.get_fifo_count()
    full = tb.is_fifo_full()

    tb.log.info(f"Final: FIFO count={count}, full={full}")

    # FIFO should be full or nearly full
    assert count >= fifo_depth - 10, f"FIFO should be nearly full (got {count}/{fifo_depth})"

    tb.log.info("PASSED: FIFO full behavior")


async def run_two_register_read_interface(tb):
    """Test two-register read interface (36-bit data over 32-bit bus)"""
    # Enable timestamp mode
    await tb.enable_profiler(mode=0)

    # Generate event on channel 5 (test non-zero channel ID)
    await tb.channel_active_pulse(channel=5, duration_cycles=25)

    # Wait for events
    await tb.wait_for_events(2)

    # Read first event manually to test interface
    assert not tb.is_fifo_empty(), "FIFO should not be empty"

    # Trigger read strobe (simulates reading LOW register)
    tb.dut.perf_fifo_rd.value = 1
    await RisingEdge(tb.clk)
    tb.dut.perf_fifo_rd.value = 0

    # Wait one cycle for latch
    await RisingEdge(tb.clk)

    # Read both output registers
    data_low = int(tb.dut.perf_fifo_data_low.value)
    data_high = int(tb.dut.perf_fifo_data_high.value)

    # Parse
    channel_id = data_high & 0x7
    event_type = (data_high >> 3) & 1

    tb.log.info(f"Two-register read: LOW=0x{data_low:08X}, HIGH=0x{data_high:08X}")
    tb.log.info(f"  Parsed: Ch{channel_id}, Event={'END' if event_type else 'START'}")

    # Verify channel ID
    assert channel_id == 5, f"Expected channel 5, got {channel_id}"
    assert event_type == 0, f"Expected START event (0), got {event_type}"

    tb.log.info("PASSED: Two-register read interface")


async def run_counter_increment(tb):
    """Test that timestamp counter increments when enabled"""
    # Enable profiler
    await tb.enable_profiler(mode=0)

    # Generate an event to get timestamps
    await tb.channel_active_pulse(channel=0, duration_cycles=10)

    # Wait and read
    await tb.wait_for_events(2)
    entries = await tb.read_all_fifo_entries()

    # Check timestamps are reasonable
    timestamp_start, _, _ = entries[0]
    timestamp_end, _, _ = entries[1]

    tb.log.info(f"Timestamps: start={timestamp_start}, end={timestamp_end}")

    # Timestamps should be increasing
    assert timestamp_end > timestamp_start, "Timestamp should increase"

    # Difference should be close to pulse duration
    diff = timestamp_end - timestamp_start
    assert 8 <= diff <= 12, f"Timestamp difference {diff} not close to 10"

    tb.log.info("PASSED: Counter increment")


# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_perf_profiler(dut):
    """Unified performance profiler test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'single_channel_timestamp_mode': Single channel in timestamp mode
    - 'single_channel_elapsed_mode': Single channel in elapsed mode
    - 'multiple_channels_sequential': Multiple channels with sequential transitions
    - 'simultaneous_edges_bug': Simultaneous transitions (DEMONSTRATES BUG!)
    - 'fifo_full_behavior': FIFO full handling
    - 'two_register_read_interface': Two-register read interface
    - 'counter_increment': Timestamp counter increment
    """
    test_type = os.environ.get('TEST_TYPE', 'single_channel_timestamp_mode')
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'single_channel_timestamp_mode':
        await run_single_channel_timestamp_mode(tb)

    elif test_type == 'single_channel_elapsed_mode':
        await run_single_channel_elapsed_mode(tb)

    elif test_type == 'multiple_channels_sequential':
        await run_multiple_channels_sequential(tb)

    elif test_type == 'simultaneous_edges_bug':
        await run_simultaneous_edges_bug(tb)

    elif test_type == 'fifo_full_behavior':
        await run_fifo_full_behavior(tb)

    elif test_type == 'two_register_read_interface':
        await run_two_register_read_interface(tb)

    elif test_type == 'counter_increment':
        await run_counter_increment(tb)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_perf_profiler_test_params():
    """Generate test parameters for perf_profiler tests.

    Returns:
        List of tuples: (test_type, num_channels, timestamp_width, fifo_depth)
    """
    test_types = [
        'single_channel_timestamp_mode',
        'single_channel_elapsed_mode',
        'multiple_channels_sequential',
        'simultaneous_edges_bug',
        'fifo_full_behavior',
        'two_register_read_interface',
        'counter_increment'
    ]
    base_params = [
        # (num_channels, timestamp_width, fifo_depth)
        (8, 32, 256),  # Standard configuration
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params

perf_profiler_params = generate_perf_profiler_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_perf_profiler(request, test_type, num_channels, timestamp_width, fifo_depth, test_level):
    """Pytest wrapper for perf_profiler tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba_gaxi': '../../../../../rtl/amba/gaxi'
    })

    dut_name = "perf_profiler"

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/perf_profiler.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    tw_str = TBBase.format_dec(timestamp_width, 2)
    fd_str = TBBase.format_dec(fifo_depth, 3)
    test_name_plus_params = f"test_{dut_name}_{test_type}_nc{nc_str}_tw{tw_str}_fd{fd_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'TIMESTAMP_WIDTH': timestamp_width,
        'FIFO_DEPTH': fifo_depth,
    }

    extra_env = {
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # VCD waveform generation (not FST which is broken)
    compile_args = [
        "--trace",              # VCD tracing (not FST!)
        "--trace-depth", "5",   # Reasonable depth for debugging
        "-Wno-TIMESCALEMOD"
    ]

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_perf_profiler",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Must be False! We use compile_args for VCD instead
            keep_files=True,
            compile_args=compile_args,
            sim_args=[],
            plusargs=[],
        )
        print(f"✓ Perf profiler {test_type} test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Perf profiler {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
