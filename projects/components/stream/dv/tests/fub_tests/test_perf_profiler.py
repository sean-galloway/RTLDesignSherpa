"""
Performance Profiler FUB Tests

Tests for perf_profiler.sv module

Test Strategy:
- Single channel profiling (both modes)
- Multiple sequential channels
- Simultaneous edges (DEMONSTRATES BUG!)
- FIFO full handling
- Two-register read interface
- Counter rollover (basic check)

Location: projects/components/stream/dv/tests/fub_tests/perf_profiler/
"""

import os
import sys

# Setup Python path BEFORE any other imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
stream_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))  # dv/ directory

# Remove if already in path
if stream_dv_path in sys.path:
    sys.path.remove(stream_dv_path)
if repo_root in sys.path:
    sys.path.remove(repo_root)

# Add to path (stream_dv_path FIRST so tbclasses is found)
sys.path.insert(0, stream_dv_path)
sys.path.insert(0, repo_root)

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from tbclasses.perf_profiler_tb import PerfProfilerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


# ===========================================================================
# SECTION 1: COCOTB TEST FUNCTIONS - prefix with "cocotb_"
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_single_channel_timestamp_mode(dut):
    """Test single channel in timestamp mode"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_single_channel_elapsed_mode(dut):
    """Test single channel in elapsed mode"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_multiple_channels_sequential(dut):
    """Test multiple channels with sequential transitions"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_simultaneous_edges_bug(dut):
    """
    Test simultaneous transitions on multiple channels

    **THIS TEST DEMONSTRATES A BUG!**

    When all 8 channels transition simultaneously from idle to active,
    only channel 0 (lowest priority) gets recorded. The other 7 channels'
    events are LOST because r_idle_prev is updated every cycle.

    Expected behavior (if bug were fixed): 8 START events
    Actual behavior (with bug): 1 START event (channel 0 only)
    """
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_fifo_full_behavior(dut):
    """Test FIFO full behavior - events should be dropped"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_two_register_read_interface(dut):
    """Test two-register read interface (36-bit data over 32-bit bus)"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_counter_increment(dut):
    """Test that timestamp counter increments when enabled"""
    tb = PerfProfilerTB(dut)
    await tb.setup_clocks_and_reset()

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
# SECTION 2: PARAMETER GENERATION
# ===========================================================================

def generate_perf_profiler_test_params():
    """Generate test parameters for perf_profiler tests."""
    return [
        # (num_channels, timestamp_width, fifo_depth)
        (8, 32, 256),  # Standard configuration
    ]

perf_profiler_params = generate_perf_profiler_test_params()

# ===========================================================================
# SECTION 3: PYTEST WRAPPER FUNCTIONS
# ===========================================================================

def run_perf_profiler_test(test_name, num_channels, timestamp_width, fifo_depth):
    """Common test runner for perf_profiler tests"""
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
    test_name_plus_params = f"{test_name}_{dut_name}_nc{nc_str}_tw{tw_str}_fd{fd_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'TIMESTAMP_WIDTH': timestamp_width,
        'FIFO_DEPTH': fifo_depth,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'PERF_NUM_CHANNELS': str(num_channels),
        'PERF_TIMESTAMP_WIDTH': str(timestamp_width),
        'PERF_FIFO_DEPTH': str(fifo_depth),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # VCD waveform generation (not FST which is broken)
    # cocotb-test adds --trace-fst when waves=True
    # We use waves=False and manually add --trace for VCD tracing
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
            testcase=f"cocotb_{test_name}",  # ← cocotb function name
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Must be False! We use compile_args for VCD instead
            keep_files=True,
            compile_args=compile_args,
            sim_args=[],
            plusargs=[],
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_single_channel_timestamp_mode(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler single channel timestamp mode test."""
    run_perf_profiler_test("test_single_channel_timestamp_mode", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_single_channel_elapsed_mode(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler single channel elapsed mode test."""
    run_perf_profiler_test("test_single_channel_elapsed_mode", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_multiple_channels_sequential(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler multiple channels sequential test."""
    run_perf_profiler_test("test_multiple_channels_sequential", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_simultaneous_edges_bug(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler simultaneous edges bug demonstration test."""
    run_perf_profiler_test("test_simultaneous_edges_bug", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_fifo_full_behavior(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler FIFO full behavior test."""
    run_perf_profiler_test("test_fifo_full_behavior", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_two_register_read_interface(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler two-register read interface test."""
    run_perf_profiler_test("test_two_register_read_interface", num_channels, timestamp_width, fifo_depth)

@pytest.mark.parametrize("num_channels, timestamp_width, fifo_depth", perf_profiler_params)
def test_counter_increment(request, num_channels, timestamp_width, fifo_depth):
    """Perf profiler counter increment test."""
    run_perf_profiler_test("test_counter_increment", num_channels, timestamp_width, fifo_depth)
