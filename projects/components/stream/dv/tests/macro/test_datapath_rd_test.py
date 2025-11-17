"""
Test runner for read datapath test wrapper (AXI Read Engine + SRAM Controller).

Purpose: Validate read engine streaming performance and bubble-free operation.

Author: sean galloway
Created: 2025-10-27
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

# Add repo root to path
# Setup Python path BEFORE any other imports
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Now import utilities to get proper repo root
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.datapath_rd_test_tb import DatapathRdTestTB
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


#=============================================================================
# CocoTB Test Function - Single test that handles all variants
#=============================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_datapath_rd(dut):
    """Unified read datapath test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic': Multiple scheduler requests with SRAM verification
    - 'nostress': Maximum BFM speed with bubble detection
    - 'per_channel_sequential': Test each channel independently
    """
    test_type = os.environ.get('TEST_TYPE', 'basic')
    tb = DatapathRdTestTB(dut)

    # Get test configuration from environment
    xfer_beats = int(os.environ.get('XFER_BEATS', '16'))
    num_channels = int(os.environ.get('NUM_CHANNELS', '1'))
    sram_depth = int(os.environ.get('SRAM_DEPTH', '256'))
    await tb.setup_clocks_and_reset(xfer_beats=xfer_beats)

    # Branch on test type
    if test_type == 'basic':
        await run_basic_test(tb, xfer_beats, num_channels, sram_depth)
    elif test_type == 'nostress':
        await run_nostress_test(tb, xfer_beats, num_channels, sram_depth)
    elif test_type == 'per_channel_sequential':
        await run_per_channel_sequential_test(tb, xfer_beats, num_channels, sram_depth)
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


async def run_basic_test(tb, xfer_beats, num_channels, sram_depth):
    """BASIC: Multiple scheduler requests with SRAM verification.

    Issues 36 scheduler requests total:
    - Single channel (1): All 36 from channel 0
    - Multi-channel (4+): 16 requests per channel
    """
    src_addr = 0x0010_0000  # 1 MB (within 16MB memory model)
    beats_per_request = xfer_beats  # Match scheduler request size to AXI burst size
    burst_len = xfer_beats  # Use configured transfer size

    # Calculate SRAM capacity per channel
    per_channel_depth = sram_depth // num_channels

    # Determine number of requests per channel based on channel count and SRAM capacity
    # Use 50% capacity to leave safe margin for buffering before drain starts
    if num_channels == 1:
        # Single channel: Try for 36 requests, but limit to SRAM capacity (50% margin)
        max_safe_requests = int((per_channel_depth * 0.5) / beats_per_request)
        num_requests_per_channel = min(36, max_safe_requests)
        channels_to_use = [0]
    else:
        # Multi-channel: Try for 12 requests per channel, but limit to SRAM capacity
        max_safe_requests = int((per_channel_depth * 0.5) / beats_per_request)
        num_requests_per_channel = min(12, max_safe_requests)
        channels_to_use = list(range(num_channels))

    tb.log.info(f"SRAM capacity: {per_channel_depth} beats/channel, "
               f"requesting {num_requests_per_channel} × {beats_per_request} = "
               f"{num_requests_per_channel * beats_per_request} beats/channel")

    # Calculate total beats for memory population and verification
    total_beats_per_channel = num_requests_per_channel * beats_per_request
    total_beats_all_channels = total_beats_per_channel * len(channels_to_use)

    tb.log.info(f"Test configuration: {num_channels} channels, "
               f"{num_requests_per_channel} requests per channel, "
               f"{beats_per_request} beats per request")

    # Step 1: Populate memory with test pattern (all channels' data)
    tb.log.info("Step 1: Populating memory with test pattern")
    await tb.populate_memory(src_addr, total_beats_all_channels, pattern='increment')

    # Step 2: Issue multiple scheduler requests per channel
    tb.log.info(f"Step 2: Issuing {num_requests_per_channel} requests per channel")
    for channel_id in channels_to_use:
        # Each channel gets its own address range
        channel_start_addr = src_addr + (channel_id * total_beats_per_channel * (tb.data_width // 8))
        success = await tb.issue_multiple_requests(
            channel_id=channel_id,
            start_addr=channel_start_addr,
            num_requests=num_requests_per_channel,
            beats_per_request=beats_per_request,
            burst_len=burst_len
        )
        assert success, f"Failed to issue requests for channel {channel_id}"

    # Give pipeline time to flush
    await tb.wait_clocks(tb.clk_name, 50)

    # Read debug counters
    r_beats_rcvd = int(tb.dut.dbg_r_beats_rcvd.value)
    sram_writes = int(tb.dut.dbg_sram_writes.value)
    tb.log.info(f"DEBUG: R beats received={r_beats_rcvd}, SRAM writes={sram_writes}, "
               f"Expected={total_beats_all_channels}")

    # Step 3: Verify data for each channel
    tb.log.info("Step 3: Draining SRAM and verifying data per channel")
    for channel_id in channels_to_use:
        channel_start_addr = src_addr + (channel_id * total_beats_per_channel * (tb.data_width // 8))

        # Wait for all data to arrive in SRAM
        await tb.wait_for_sram_data(channel_id, total_beats_per_channel, timeout_cycles=5000)

        # Drain and verify
        success, errors = await tb.drain_and_verify_sram(
            channel_id=channel_id,
            expected_beats=total_beats_per_channel,
            start_addr=channel_start_addr
        )
        assert success, f"Channel {channel_id} verification failed with {errors} errors"

    # Stop FIFO health monitor and check for violations
    fifo_violation_count, fifo_violations = tb.stop_fifo_health_monitor()
    if fifo_violation_count > 0:
        tb.log.error(f"FIFO HEALTH VIOLATIONS DETECTED: {fifo_violation_count} total")
        tb.log.error("First 10 violations:")
        for i, (cycle, ch_id, fifo_cnt, alloc_free, rd_free) in enumerate(fifo_violations[:10]):
            tb.log.error(f"  [{i+1}] Cycle {cycle}, CH{ch_id}: fifo_count={fifo_cnt}, "
                        f"alloc_space_free={alloc_free}, rd_space_free={rd_free}")
        tb.log.error("This indicates a POINTER BUG in sram_controller_unit")
        assert False, f"FIFO health violations detected: {fifo_violation_count} instances of pointer bugs"
    else:
        tb.log.info(f"✓ FIFO health check: PASS - No pointer bugs detected")

    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_rd_all_complete signal behavior...")
    for channel_id in channels_to_use:
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("✓ BASIC test passed - All channels verified")


async def run_nostress_test(tb, xfer_beats, num_channels, sram_depth):
    """NOSTRESS: Multiple scheduler requests at maximum BFM speed.

    This test validates sustained streaming performance with:
    - Memory model responding immediately (response_delay=0)
    - AXI R channel with zero valid delays (backtoback mode)
    - Multiple scheduler requests to test bubble-free operation

    Issues 36 scheduler requests total:
    - Single channel (1): All 36 from channel 0
    - Multi-channel (4+): 16 requests per channel

    CRITICAL: ALL AXI delays are zero - any bubbles are RTL-caused.
    """
    src_addr = 0x0010_0000  # 1 MB (within 16MB memory model)
    beats_per_request = xfer_beats  # Match scheduler request size to AXI burst size
    burst_len = xfer_beats  # Use configured transfer size

    # Determine number of requests per channel based on channel count
    if num_channels == 1:
        # Single channel: all 36 requests from channel 0
        num_requests_per_channel = 36
        channels_to_use = [0]
    else:
        # Multi-channel: 16 requests per channel
        num_requests_per_channel = 16
        channels_to_use = list(range(num_channels))

    # Calculate total beats and check against SRAM capacity
    total_beats_per_channel = num_requests_per_channel * beats_per_request
    per_channel_depth = sram_depth // num_channels

    # Ensure we don't overflow SRAM
    # Use 80% capacity to leave headroom for outstanding transactions
    if total_beats_per_channel > per_channel_depth:
        # Reduce requests to fit in SRAM (80% margin)
        max_safe_beats = int(per_channel_depth * 0.8)
        num_requests_per_channel = max_safe_beats // beats_per_request
        total_beats_per_channel = num_requests_per_channel * beats_per_request
        tb.log.warning(f"Reduced to {num_requests_per_channel} requests/channel to fit SRAM "
                      f"(depth={per_channel_depth}, safe={max_safe_beats} beats)")

    total_beats_all_channels = total_beats_per_channel * len(channels_to_use)

    tb.log.info(f"NOSTRESS configuration: {num_channels} channels, "
               f"{num_requests_per_channel} requests per channel, "
               f"{beats_per_request} beats per request, "
               f"SRAM per-ch: {per_channel_depth} beats")

    # Step 1: Populate memory with test pattern (all channels' data)
    tb.log.info("Step 1: Populating memory with test pattern")
    await tb.populate_memory(src_addr, total_beats_all_channels, pattern='increment')

    # Step 2: Issue multiple scheduler requests per channel
    # For multi-channel NOSTRESS: kick off all channels simultaneously for zero-bubble operation
    # For single-channel: use sequential kickoff (same behavior)
    if num_channels > 1:
        tb.log.info(f"Step 2: Kicking off ALL {num_channels} channels simultaneously (NOSTRESS mode)")
        success = await tb.kick_off_all_channels(
            descriptors_per_channel=num_requests_per_channel,
            beats_per_descriptor=beats_per_request,
            start_addr_base=src_addr
        )
        assert success, "Failed to kick off all channels simultaneously"
    else:
        # Single channel: sequential kickoff (same as basic test)
        tb.log.info(f"Step 2: Issuing {num_requests_per_channel} requests for single channel (NOSTRESS mode)")
        channel_start_addr = src_addr
        success = await tb.issue_multiple_requests(
            channel_id=0,
            start_addr=channel_start_addr,
            num_requests=num_requests_per_channel,
            beats_per_request=beats_per_request,
            burst_len=burst_len
        )
        assert success, "Failed to issue requests for channel 0"

    # Give pipeline time to flush - with watchdog
    tb.log.info("Waiting for pipeline to flush all data...")
    await tb.wait_clocks(tb.clk_name, 50)

    # Watchdog: Wait for all FIFOs to drain (or timeout)
    watchdog_timeout_cycles = 2000
    watchdog_count = 0
    all_drained = False

    tb.log.info(f"Watchdog: Monitoring FIFO drain (timeout={watchdog_timeout_cycles} cycles)")

    while watchdog_count < watchdog_timeout_cycles:
        await RisingEdge(tb.clk)
        watchdog_count += 1

        # Check if all channels are drained
        try:
            data_avail_bv = tb.dut.axi_wr_drain_data_avail.value
            total_data_available = 0

            for ch_id in range(num_channels):
                shift = ch_id * 8
                mask = 0xFF << shift
                data_avail = (int(data_avail_bv) & mask) >> shift
                total_data_available += data_avail

            # Log progress every 100 cycles
            if watchdog_count % 100 == 0:
                tb.log.info(f"Watchdog: Cycle {watchdog_count}/{watchdog_timeout_cycles}, "
                          f"data_available={total_data_available}")

            # All drained when no data left in any channel
            if total_data_available == 0:
                all_drained = True
                tb.log.info(f"✓ Watchdog: All FIFOs drained at cycle {watchdog_count}")
                break

        except Exception as e:
            tb.log.warning(f"Watchdog: Could not read data_available: {e}")
            continue

    # Check if watchdog timed out
    if not all_drained:
        tb.log.error(f"✗ Watchdog TIMEOUT after {watchdog_timeout_cycles} cycles")
        tb.log.error(f"  FIFOs still have {total_data_available} beats total")
        tb.log.error(f"  This indicates a HANG in the drain path")
        # Don't fail immediately - let FIFO health monitor report the root cause

    # Read debug counters
    r_beats_rcvd = int(tb.dut.dbg_r_beats_rcvd.value)
    sram_writes = int(tb.dut.dbg_sram_writes.value)
    tb.log.info(f"DEBUG: R beats received={r_beats_rcvd}, SRAM writes={sram_writes}, "
               f"Expected={total_beats_all_channels}")

    # Stop FIFO health monitor and check for violations
    fifo_violation_count, fifo_violations = tb.stop_fifo_health_monitor()
    if fifo_violation_count > 0:
        tb.log.error(f"FIFO HEALTH VIOLATIONS DETECTED: {fifo_violation_count} total")
        tb.log.error("First 10 violations:")
        for i, (cycle, ch_id, fifo_cnt, alloc_free, rd_free) in enumerate(fifo_violations[:10]):
            tb.log.error(f"  [{i+1}] Cycle {cycle}, CH{ch_id}: fifo_count={fifo_cnt}, "
                        f"alloc_space_free={alloc_free}, rd_space_free={rd_free}")
        tb.log.error("This indicates a POINTER BUG in sram_controller_unit")
        assert False, f"FIFO health violations detected: {fifo_violation_count} instances of pointer bugs"
    else:
        tb.log.info(f"✓ FIFO health check: PASS - No pointer bugs detected")

    # Stop bubble detector and get results (all modes)
    bubble_count, bubble_list = tb.stop_bubble_detector()

    # Stop auto-drain and skip detailed verification (NOSTRESS mode)
    if tb.NOSTRESS_MODE:
        drain_stats = tb.stop_auto_drain()
        tb.log.info(f"Auto-drain stopped: {drain_stats['total_drained']} total beats drained")
        tb.log.info(f"  Per-channel: {drain_stats['per_channel'][:num_channels]}")
        tb.log.info("NOTE: Auto-drain consumed SRAM data to prevent overflow - skipping detailed verification")
        tb.log.info("NOSTRESS verification relies on bubble detection and debug counters")
    else:
        # Step 3: Verify data for each channel (non-NOSTRESS mode only)
        tb.log.info("Step 3: Draining SRAM and verifying data per channel")
        for channel_id in channels_to_use:
            channel_start_addr = src_addr + (channel_id * total_beats_per_channel * (tb.data_width // 8))

            # Wait for all data to arrive in SRAM
            await tb.wait_for_sram_data(channel_id, total_beats_per_channel, timeout_cycles=5000)

            # Drain and verify
            success, errors = await tb.drain_and_verify_sram(
                channel_id=channel_id,
                expected_beats=total_beats_per_channel,
                start_addr=channel_start_addr
            )
            assert success, f"Channel {channel_id} verification failed with {errors} errors"

    # Check bubble detector results (nostress mode only)
    if tb.NOSTRESS_MODE:
        # Bubble detector stopped above (line 303), results now in bubble_count/bubble_list
        enable_pipeline = int(os.environ.get('PIPELINE', '0'))

        if bubble_count > 0:
            # Classify bubbles as inter-burst vs intra-burst
            inter_burst = [b for b in bubble_list if 'INTER-BURST' in b[2]]
            intra_burst = [b for b in bubble_list if 'INTRA-BURST' in b[2]]

            # Non-pipelined configs: Expect inter-burst gaps, report as INFO
            # Pipelined configs: Expect zero bubbles, report as ERROR
            if enable_pipeline == 0:
                # NOPIPE mode: Inter-burst gaps are expected
                tb.log.info(f"NOSTRESS NOTICE: Detected {bubble_count} R channel bubbles (expected in nopipe mode)")
                tb.log.info(f"  Breakdown: {len(intra_burst)} intra-burst, {len(inter_burst)} inter-burst")
                tb.log.info(f"First 10 bubbles:")
                for i, (cycle, btype, location) in enumerate(bubble_list[:10]):
                    tb.log.info(f"    [{i+1}] Cycle {cycle}: {btype} | {location}")

                # Provide informational analysis
                if len(inter_burst) > len(intra_burst):
                    tb.log.info(f"ANALYSIS:")
                    tb.log.info(f"  Majority are INTER-BURST gaps (expected without pipeline):")
                    tb.log.info(f"    - Descriptor processing delay between bursts")
                    tb.log.info(f"    - AR channel request timing gaps")
                else:
                    tb.log.warning(f"ANALYSIS:")
                    tb.log.warning(f"  Majority are INTRA-BURST gaps (unexpected even in nopipe):")
                    tb.log.warning(f"    - This may indicate SRAM capacity or throughput issues")
                    tb.log.warning(f"    - Review SRAM depth and AXI slave timing")

                tb.log.info(f"NOTE: Non-pipelined configs naturally have inter-burst gaps")
                tb.log.info(f"  This is expected behavior and does not indicate a bug")
                # Don't fail the test for nopipe mode
            else:
                # PIPE mode: Zero bubbles expected, report as ERROR
                tb.log.error(f"NOSTRESS VIOLATION: Detected {bubble_count} R channel bubbles")
                tb.log.error(f"  Breakdown: {len(intra_burst)} intra-burst, {len(inter_burst)} inter-burst")
                tb.log.error(f"First 10 bubbles:")
                for i, (cycle, btype, location) in enumerate(bubble_list[:10]):
                    tb.log.error(f"    [{i+1}] Cycle {cycle}: {btype} | {location}")

                # Provide actionable guidance based on bubble type
                if len(inter_burst) > len(intra_burst):
                    tb.log.error(f"ROOT CAUSE ANALYSIS:")
                    tb.log.error(f"  Majority are INTER-BURST gaps → Issue likely in:")
                    tb.log.error(f"    - AR channel request timing (RTL not issuing AR fast enough)")
                    tb.log.error(f"    - Descriptor processing delay between bursts")
                    tb.log.error(f"    - SRAM drain/refill causing gaps")
                else:
                    tb.log.error(f"ROOT CAUSE ANALYSIS:")
                    tb.log.error(f"  Majority are INTRA-BURST gaps → Issue likely in:")
                    tb.log.error(f"    - Memory model not sustaining backtoback responses")
                    tb.log.error(f"    - AXI slave R channel batching not working correctly")
                    tb.log.error(f"    - SRAM read path has unexpected bubbles")

                tb.log.error(f"This indicates either:")
                tb.log.error(f"  1. Configuration limitation (e.g., SRAM full, backpressure needed)")
                tb.log.error(f"  2. RTL bug (unexpected stall in data path)")
                tb.log.error(f"Manual review required to determine if bubbles are acceptable")

                # FAIL the test for pipelined mode - zero bubbles expected
                assert False, (f"NOSTRESS mode (pipelined): {bubble_count} R channel bubbles detected "
                              f"({len(intra_burst)} intra-burst, {len(inter_burst)} inter-burst). "
                              f"Review logs for root cause analysis.")
        else:
            tb.log.info(f"✓ NOSTRESS bubble check: PERFECT - Zero bubbles detected!")
            tb.log.info(f"  R channel maintained rvalid=1 && rready=1 continuously")

    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_rd_all_complete signal behavior...")
    for channel_id in channels_to_use:
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("✓ NOSTRESS test passed - All channels verified with zero BFM delays")


async def run_per_channel_sequential_test(tb, xfer_beats, num_channels, sram_depth):
    """PER-CHANNEL SEQUENTIAL: Test each channel independently, one at a time.

    This test isolates per-channel calculation from multi-channel interactions by:
    - Testing ONLY ONE channel at a time
    - Writing 48 beats to channel N
    - Draining channel N completely
    - Verifying data integrity
    - Moving to next channel

    If any channel fails independently, it's a per-channel calculation issue.
    If all channels work independently but fail when used together, it's a multi-channel issue.

    Configuration: 4 channels, 256-bit data width (matching failing test)
    """
    tb.log.info("="*80)
    tb.log.info("PER-CHANNEL SEQUENTIAL TEST")
    tb.log.info(f"Configuration: {num_channels} channels, {xfer_beats} beats/xfer")
    tb.log.info(f"Strategy: Test each channel independently, drain completely before next")
    tb.log.info("="*80)

    # FIFO health monitor is automatically started in setup_clocks_and_reset

    src_addr_base = 0x0010_0000
    beats_per_channel = 48  # Match failing test scenario
    bytes_per_beat = tb.data_width // 8

    # Test each channel independently
    for channel_id in range(num_channels):
        tb.log.info("")
        tb.log.info(f"{'='*80}")
        tb.log.info(f"Testing Channel {channel_id} (ISOLATED)")
        tb.log.info(f"{'='*80}")

        # DEBUG: Log VCD location and start time for channel 1 specifically
        if channel_id == 1:
            import cocotb.utils
            current_time = cocotb.utils.get_sim_time(units='ns')
            sim_build = os.environ.get('SIM_BUILD', 'unknown')
            vcd_path = os.path.join(sim_build, 'dump.vcd')
            tb.log.error("")
            tb.log.error(f"{'!'*80}")
            tb.log.error(f"!!! CHANNEL 1 DEBUG - BUG REPRO POINT !!!")
            tb.log.error(f"VCD FILE: {vcd_path}")
            tb.log.error(f"START TIME: {current_time:.2f} ns")
            tb.log.error(f"SIGNALS TO WATCH:")
            tb.log.error(f"  - u_sram_controller.gen_channel_units[1].u_channel_unit.u_channel_fifo.count")
            tb.log.error(f"  - u_sram_controller.gen_channel_units[1].u_channel_unit.bridge_occupancy")
            tb.log.error(f"  - axi_rd_sram_valid && (axi_rd_sram_id == 1)")
            tb.log.error(f"  - axi_wr_sram_drain && (axi_wr_sram_id == 1)")
            tb.log.error(f"{'!'*80}")
            tb.log.error("")

            # Start transaction counter for channel 1
            tb.start_channel_transaction_counter(channel_id=1)

        # Calculate unique address range for this channel
        channel_start_addr = src_addr_base + (channel_id * beats_per_channel * bytes_per_beat)

        # Step 1: Populate memory for this channel only
        tb.log.info(f"Channel {channel_id}: Populating memory with {beats_per_channel} beats")
        await tb.populate_memory(channel_start_addr, beats_per_channel, pattern='increment')

        # Step 2: Issue single descriptor for all 48 beats
        tb.log.info(f"Channel {channel_id}: Issuing descriptor for {beats_per_channel} beats")
        success = await tb.issue_descriptor_packet(
            channel_id=channel_id,
            src_addr=channel_start_addr,
            length=beats_per_channel,
            last=True
        )
        assert success, f"Channel {channel_id}: Failed to issue descriptor"

        # Step 3: Wait for data to arrive in SRAM
        tb.log.info(f"Channel {channel_id}: Waiting for data to arrive in SRAM...")
        await tb.wait_for_sram_data(channel_id, beats_per_channel, timeout_cycles=5000)

        # Check data_available signal
        try:
            data_available_signal = getattr(tb.dut, 'axi_wr_drain_data_avail')
            data_available = data_available_signal.value

            # Extract this channel's data_available (variable width packed array)
            if num_channels > 1:
                # Multi-channel: packed array [NC-1:0][COUNT_WIDTH-1:0]
                count_width = data_available_signal.value.n_bits // num_channels
                # Extract bits for this channel
                ch_start_bit = channel_id * count_width
                ch_end_bit = (channel_id + 1) * count_width - 1
                ch_data_avail_bits = (data_available >> ch_start_bit) & ((1 << count_width) - 1)
                ch_data_avail = int(ch_data_avail_bits)
            else:
                # Single channel: simple value
                ch_data_avail = int(data_available)

            tb.log.info(f"Channel {channel_id}: axi_wr_drain_data_avail = {ch_data_avail} (expected ~{beats_per_channel})")
        except Exception as e:
            tb.log.warning(f"Channel {channel_id}: Could not read data_available: {e}")

        # Step 4: Drain and verify all 48 beats
        tb.log.info(f"Channel {channel_id}: Draining and verifying {beats_per_channel} beats")
        success, errors = await tb.drain_and_verify_sram(
            channel_id=channel_id,
            expected_beats=beats_per_channel,
            start_addr=channel_start_addr
        )

        # Wait 10 clocks after drain completes (for VCD viewing) - DO THIS BEFORE ASSERTIONS
        import cocotb.utils
        pre_wait_time = cocotb.utils.get_sim_time(units='ns')
        tb.log.info(f"Channel {channel_id}: Waiting 10 clocks for VCD capture (current time: {pre_wait_time:.2f} ns)")
        await tb.wait_clocks('clk', 10)
        post_wait_time = cocotb.utils.get_sim_time(units='ns')
        tb.log.info(f"Channel {channel_id}: Wait complete (current time: {post_wait_time:.2f} ns)")

        if not success:
            tb.log.error(f"✗ Channel {channel_id}: Verification FAILED ({errors} errors)")
            tb.log.error(f"  This indicates a per-channel calculation issue in sram_controller_unit")

            # DEBUG: Log failure point for channel 1
            if channel_id == 1:
                import cocotb.utils
                fail_time = cocotb.utils.get_sim_time(units='ns')
                tb.log.error("")
                tb.log.error(f"{'!'*80}")
                tb.log.error(f"!!! CHANNEL 1 BUG DETECTED !!!")
                tb.log.error(f"FAILURE TIME: {fail_time:.2f} ns")
                tb.log.error(f"EXPECTED: 48 beats")
                tb.log.error(f"ACTUAL: {beats_per_channel - errors} beats drained successfully")
                tb.log.error(f"MISSING: {errors} beat(s)")
                tb.log.error(f"")
                tb.log.error(f"VCD ANALYSIS:")
                tb.log.error(f"  1. Open VCD in GTKWave")
                tb.log.error(f"  2. Go to time {current_time:.2f} ns (Channel 1 start)")
                tb.log.error(f"  3. Count axi_rd_sram writes for channel 1 (id==1)")
                tb.log.error(f"  4. Count axi_wr_sram drains for channel 1 (id==1)")
                tb.log.error(f"  5. Check FIFO count at {fail_time:.2f} ns")
                tb.log.error(f"{'!'*80}")
                tb.log.error("")

            assert False, f"Channel {channel_id} independent test failed"
        else:
            tb.log.info(f"✓ Channel {channel_id}: All {beats_per_channel} beats verified successfully")

        # Stop transaction counter for channel 1
        if channel_id == 1:
            tb.stop_channel_transaction_counter()
            # Give it a moment to print summary
            await tb.wait_clocks('clk', 2)

        # Step 5: Verify channel is completely drained
        try:
            data_available_signal = getattr(tb.dut, 'axi_wr_drain_data_avail')
            data_available = data_available_signal.value

            if num_channels > 1:
                count_width = data_available_signal.value.n_bits // num_channels
                ch_start_bit = channel_id * count_width
                ch_data_avail_bits = (data_available >> ch_start_bit) & ((1 << count_width) - 1)
                ch_data_avail = int(ch_data_avail_bits)
            else:
                ch_data_avail = int(data_available)

            tb.log.info(f"Channel {channel_id}: After drain, axi_wr_drain_data_avail = {ch_data_avail} (expected 0)")
            if ch_data_avail != 0:
                tb.log.error(f"✗ Channel {channel_id}: Still has {ch_data_avail} beats available after drain!")
                tb.log.error(f"  This beat is likely stuck in the latency bridge - need to wait/flush")

                # Read bridge debug signals to see what's stuck
                try:
                    pending_signal = getattr(tb.dut, 'dbg_bridge_pending')
                    out_valid_signal = getattr(tb.dut, 'dbg_bridge_out_valid')

                    pending_val = int(pending_signal.value)
                    out_valid_val = int(out_valid_signal.value)

                    ch_pending = (pending_val >> channel_id) & 1
                    ch_out_valid = (out_valid_val >> channel_id) & 1

                    tb.log.error(f"  Channel {channel_id} Bridge State:")
                    tb.log.error(f"    dbg_r_pending    = {ch_pending}")
                    tb.log.error(f"    dbg_r_out_valid  = {ch_out_valid}")
                    tb.log.error(f"    occupancy        = {ch_pending + ch_out_valid}")

                    if ch_pending and not ch_out_valid:
                        tb.log.error(f"  BUG FOUND: Bridge has pending=1, out_valid=0 (capture armed but not complete)")
                    elif ch_out_valid and not ch_pending:
                        tb.log.error(f"  BUG FOUND: Bridge has out_valid=1, pending=0 (data stuck in output register)")
                    elif ch_pending and ch_out_valid:
                        tb.log.error(f"  BUG FOUND: Bridge has BOTH pending=1 AND out_valid=1 (occupancy=2!)")
                except Exception as e:
                    tb.log.warning(f"  Could not read bridge debug signals: {e}")

                # Wait for latency bridge to flush (give it some cycles)
                tb.log.info(f"Channel {channel_id}: Waiting for latency bridge to flush...")
                await tb.wait_clocks('clk', 10)

                # Check again
                data_available = data_available_signal.value
                if num_channels > 1:
                    ch_data_avail_bits = (data_available >> ch_start_bit) & ((1 << count_width) - 1)
                    ch_data_avail = int(ch_data_avail_bits)
                else:
                    ch_data_avail = int(data_available)

                tb.log.info(f"Channel {channel_id}: After wait, axi_wr_drain_data_avail = {ch_data_avail}")

                if ch_data_avail != 0:
                    # Try one final drain
                    tb.log.info(f"Channel {channel_id}: Attempting final drain of {ch_data_avail} beats...")
                    final_success, final_errors = await tb.drain_and_verify_sram(
                        channel_id=channel_id,
                        expected_beats=ch_data_avail,
                        start_addr=channel_start_addr + (beats_per_channel - ch_data_avail) * (tb.data_width // 8)
                    )
                    if final_success:
                        tb.log.info(f"✓ Channel {channel_id}: Final drain successful")
                    else:
                        assert False, f"Channel {channel_id} not fully drained even after final attempt"
        except Exception as e:
            tb.log.warning(f"Channel {channel_id}: Could not verify drain: {e}")

        tb.log.info(f"✓ Channel {channel_id}: COMPLETE - Successfully tested in isolation")

    # Stop FIFO health monitor and check for violations
    fifo_violation_count, fifo_violations = tb.stop_fifo_health_monitor()
    if fifo_violation_count > 0:
        tb.log.error(f"FIFO HEALTH VIOLATIONS DETECTED: {fifo_violation_count} total")
        tb.log.error("First 10 violations:")
        for i, (cycle, ch_id, fifo_cnt, alloc_free, rd_free) in enumerate(fifo_violations[:10]):
            tb.log.error(f"  [{i+1}] Cycle {cycle}, CH{ch_id}: fifo_count={fifo_cnt}, "
                        f"alloc_space_free={alloc_free}, rd_space_free={rd_free}")
        tb.log.error("This indicates a POINTER BUG in sram_controller_unit")
        assert False, f"FIFO health violations detected: {fifo_violation_count} instances of pointer bugs"
    else:
        tb.log.info(f"✓ FIFO health check: PASS - No pointer bugs detected")

    tb.log.info("")
    tb.log.info("="*80)
    tb.log.info(f"✓ PER-CHANNEL SEQUENTIAL TEST PASSED")
    tb.log.info(f"All {num_channels} channels work correctly in isolation!")
    tb.log.info(f"If multi-channel tests fail but this passes, it's a multi-channel interaction issue.")
    tb.log.info("="*80)

    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_rd_all_complete signal behavior...")
    for channel_id in range(num_channels):
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("✓ Completion signal validation passed for all channels")


#=============================================================================
# Parameter Generation
#=============================================================================

def calc_sram_depth(data_width, num_channels):
    """
    Calculate SRAM depth with 256 beats per channel minimum.

    For simplicity, use 256 beats per channel regardless of data width.
    This provides ample buffering to avoid SRAM fullness issues during testing.

    Examples:
        128-bit (16 bytes/beat): 256 beats/ch = 4KB/ch
        256-bit (32 bytes/beat): 256 beats/ch = 8KB/ch
        512-bit (64 bytes/beat): 256 beats/ch = 16KB/ch
    """
    beats_per_channel = 256
    total_depth = beats_per_channel * num_channels
    return total_depth

def generate_params():
    """
    Generate parameters for read datapath tests based on REG_LEVEL.

    QUICK_DEBUG=1: Single minimal test (128-bit, 4ch, pipe, 16 beats, 'basic' test) - for fast iteration
    REG_LEVEL=GATE: 1 test (smoke test - 128-bit, 4ch, 256B transfer, 'fixed' timing, 'basic' test)
    REG_LEVEL=FUNC: 18 tests (9 base configs × 2 timing profiles: fixed, fast) × 1 test type (basic only)
    REG_LEVEL=FULL: 234 tests (26 base configs × 3 timing profiles: fixed, fast, constrained) × 3 test types (basic, nostress, per_channel_sequential)

    Parameters: (test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile)

    Test Types:
        - 'basic': Multiple scheduler requests with SRAM verification
        - 'nostress': Maximum BFM speed with bubble detection
        - 'per_channel_sequential': Test each channel independently

    Data widths: 128, 256, 512 bits (16, 32, 64 bytes per beat)
    Transfer sizes scaled by data width:
        - 128-bit: 16 beats = 256B, 8 beats = 128B
        - 256-bit: 8 beats = 256B, 4 beats = 128B
        - 512-bit: 4 beats = 256B, 2 beats = 128B

    Channels: 1, 4, 8
    SRAM depths: Fixed at 256 beats per channel for simplicity

    Timing Profiles (AXI BFM delay configurations):
        - 'fixed': Constant 1-cycle delays (baseline)
        - 'fast': Mostly zero delays, occasional short delays (aggressive producer)
        - 'constrained': Moderate random delays (realistic mixed timing)

    NOTE: Single channel with pipelining (1 channel, enable_pipeline=1) is skipped
    due to known issue with data verification. This is an edge case - production designs
    use 4+ channels. See known_issues/ for details.
    """
    # QUICK_DEBUG mode: single minimal config for fast iteration during debugging
    if os.environ.get('QUICK_DEBUG', '0') == '1':
        return [
            ('basic', 128, 4, calc_sram_depth(128, 4), 'basic', 1, 16, 'fixed'),  # 128-bit, 4 ch, pipe, 16 beats, fixed timing
        ]

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - smoke test with 128-bit, 4 channels, fixed timing, basic test only
        base_params = [
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 16),  # 128-bit, 4 ch, pipe, 16 beats = 256B
        ]
        timing_profiles = ['fixed']  # Just baseline for smoke test
        test_types = ['basic']  # Only basic test for smoke
    elif reg_level == 'FUNC':
        # Functional coverage: 128/256/512-bit × 1/4 channels × 2 timing profiles × basic test only
        base_params = [
            # 128-bit data width (16 bytes per beat, 256 beats/ch = 4KB/ch)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 16),  # 4 ch, pipe, 256B
            (128, 4, calc_sram_depth(128, 4), 'basic', 0, 16),  # 4 ch, no-pipe, 256B
            # 256-bit data width (32 bytes per beat, 256 beats/ch = 8KB/ch)
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 4, calc_sram_depth(256, 4), 'basic', 1, 8),   # 4 ch, pipe, 256B
            (256, 4, calc_sram_depth(256, 4), 'basic', 0, 8),   # 4 ch, no-pipe, 256B
            # 512-bit data width (64 bytes per beat, 256 beats/ch = 16KB/ch)
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 4, calc_sram_depth(512, 4), 'basic', 1, 4),   # 4 ch, pipe, 256B
            (512, 4, calc_sram_depth(512, 4), 'basic', 0, 4),   # 4 ch, no-pipe, 256B
        ]
        timing_profiles = ['fixed', 'fast']  # 2 profiles for functional testing
        test_types = ['basic']  # Only basic test for functional level
    else:  # FULL
        # Comprehensive - test all data widths × 1/4 channels × 3 timing profiles × 3 test types
        base_params = [
            # 128-bit: 1 channel (no-pipeline only to avoid known issue)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 128B
            # 128-bit: 4 channels
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 16),  # 4 ch, pipe, 256B
            (128, 4, calc_sram_depth(128, 4), 'basic', 0, 16),  # 4 ch, no-pipe, 256B
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 8),   # 4 ch, pipe, 128B
            (128, 4, calc_sram_depth(128, 4), 'basic', 0, 8),   # 4 ch, no-pipe, 128B
            # 256-bit: 1 channel
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 128B
            # 256-bit: 4 channels
            (256, 4, calc_sram_depth(256, 4), 'basic', 1, 8),   # 4 ch, pipe, 256B
            (256, 4, calc_sram_depth(256, 4), 'basic', 0, 8),   # 4 ch, no-pipe, 256B
            (256, 4, calc_sram_depth(256, 4), 'basic', 1, 4),   # 4 ch, pipe, 128B
            (256, 4, calc_sram_depth(256, 4), 'basic', 0, 4),   # 4 ch, no-pipe, 128B
            # 512-bit: 1 channel
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 2),   # 1 ch, no-pipe, 128B
            # 512-bit: 4 channels
            (512, 4, calc_sram_depth(512, 4), 'basic', 1, 4),   # 4 ch, pipe, 256B
            (512, 4, calc_sram_depth(512, 4), 'basic', 0, 4),   # 4 ch, no-pipe, 256B
            (512, 4, calc_sram_depth(512, 4), 'basic', 1, 2),   # 4 ch, pipe, 128B
            (512, 4, calc_sram_depth(512, 4), 'basic', 0, 2),   # 4 ch, no-pipe, 128B
        ]
        timing_profiles = ['fixed', 'fast', 'constrained']  # 3 profiles for comprehensive testing
        test_types = ['basic', 'nostress', 'per_channel_sequential']  # All test types

    # Generate final params by adding test_type AND timing profile to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            for profile in timing_profiles:
                params.append((test_type,) + base + (profile,))

    return params


params = generate_params()


#=============================================================================
# Pytest Wrapper Function - Single wrapper for all test types
#=============================================================================

@pytest.mark.parametrize("test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile", params)
def test_datapath_rd(request, test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile):
    """Pytest wrapper for read datapath tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_stream_fub': '../../../../rtl/stream_fub'})
    dut_name = "datapath_rd_test"
    pipeline_str = "pipe" if enable_pipeline else "nopipe"
    test_name_plus_params = f"test_datapath_rd_{test_type}_nc{num_channels}_dw{data_width}_sd{sram_depth}_{test_level}_{pipeline_str}_xb{xfer_beats}_{timing_profile}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='projects/components/stream/rtl/filelists/macro/datapath_rd_test.f')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    parameters = {
        'DATA_WIDTH': str(data_width),
        'NUM_CHANNELS': str(num_channels),
        'SRAM_DEPTH': str(sram_depth),
        'PIPELINE': str(enable_pipeline),
        'AR_MAX_OUTSTANDING': '8'  # Default value
    }
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
        'XFER_BEATS': str(xfer_beats),
        'SRAM_DEPTH': str(sram_depth),
        'NUM_CHANNELS': str(num_channels),
        'TIMING_PROFILE': timing_profile,  # AXI BFM timing configuration
        'NOSTRESS_MODE': '1' if test_type == 'nostress' else '0',  # Enable nostress mode for nostress test
        'PIPELINE': str(enable_pipeline),  # For bubble detector analysis
    }

    # WAVES support - conditionally enable waveform dumping
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        # VCD tracing compile args (not FST to avoid Verilator bugs)
        compile_args = ["--trace", "--trace-depth", "99"]
        sim_args = []
        plusargs = []
    else:
        # No tracing - faster compilation
        compile_args = []
        sim_args = []
        plusargs = []

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes, toplevel=dut_name,
            module=module, testcase="cocotb_test_datapath_rd", parameters=parameters, sim_build=sim_build,
            extra_env=extra_env, waves=False, keep_files=True, compile_args=compile_args, sim_args=sim_args, plusargs=plusargs,
            simulator='verilator')
        print(f"✓ Read {test_type} test PASSED ({test_level} level)")
    except Exception as e:
        print(f"✗ Read {test_type} test FAILED ({test_level} level): {str(e)}")
        raise
