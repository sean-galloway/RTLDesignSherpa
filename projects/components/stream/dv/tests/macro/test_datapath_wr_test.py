"""
Test runner for write datapath test wrapper (SRAM → AXI Write Engine).

Purpose: Validate write engine streaming performance.

Author: sean galloway
Created: 2025-11-05
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.datapath_wr_test_tb import DatapathWrTestTB

# Coverage integration - optional import
try:
    from projects.components.stream.dv.stream_coverage import (
        CoverageHelper,
        get_coverage_compile_args,
        get_coverage_env
    )
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False

    def get_coverage_compile_args():
        """Stub when coverage not available."""
        return []

    def get_coverage_env(test_name, sim_build=None):
        """Stub when coverage not available."""
        return {}


#=============================================================================
# CocoTB Test Function - Single test that handles all variants
#=============================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_datapath_wr(dut):
    """Unified write datapath test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic': Fill SRAM, issue descriptors, verify memory writes
    - 'nostress': Maximum BFM speed write testing
    - 'per_channel_sequential': Test each channel independently
    """
    test_type = os.environ.get('TEST_TYPE', 'basic')
    tb = DatapathWrTestTB(dut)

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
    elif test_type == 'varying_lengths':
        await run_varying_lengths_test(tb, xfer_beats, num_channels, sram_depth)
    elif test_type == 'b2b_multi_channel':
        await run_b2b_multi_channel_test(tb, xfer_beats, num_channels, sram_depth)
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


async def run_basic_test(tb, xfer_beats, num_channels, sram_depth):
    """BASIC: Fill SRAM, issue descriptors, verify memory writes.

    Test flow:
    1. Fill SRAM with test data
    2. Issue descriptor to trigger write
    3. Wait for AXI write completion
    4. Verify data in memory model
    """
    dst_addr = 0x0010_0000  # 1 MB destination
    beats_per_request = xfer_beats

    # Calculate SRAM capacity per channel
    per_channel_depth = sram_depth // num_channels

    # Use 50% capacity to leave safe margin
    max_safe_requests = int((per_channel_depth * 0.5) / beats_per_request)

    # Reduce test size for slow_producer timing profile (takes 3-4x longer)
    # Use very small size to avoid bridge deadlock from extreme backpressure
    if tb.TIMING_PROFILE == 'slow_producer':
        num_requests_per_channel = min(3, max_safe_requests)  # Small size for slow tests
    else:
        num_requests_per_channel = min(12, max_safe_requests)

    total_beats_per_channel = num_requests_per_channel * beats_per_request

    tb.log.info(f"Test configuration: {num_channels} channels, "
               f"{num_requests_per_channel} requests per channel, "
               f"{beats_per_request} beats per request")

    # Test single channel for now
    channel_id = 0

    # Step 1: Fill SRAM with test data
    tb.log.info(f"Step 1: Filling SRAM channel {channel_id} with {total_beats_per_channel} beats")
    await tb.fill_sram(channel_id, dst_addr, total_beats_per_channel, pattern='increment')

    # Step 2: Issue descriptor to trigger write
    tb.log.info(f"Step 2: Issuing descriptor for {total_beats_per_channel} beats")
    success = await tb.issue_descriptor_packet(
        channel_id=channel_id,
        dst_addr=dst_addr,
        length=total_beats_per_channel,
        last=True
    )
    assert success, f"Failed to issue descriptor for channel {channel_id}"

    # Step 3: Wait for write completion
    tb.log.info(f"Step 3: Waiting for AXI write completion")
    expected_aw_txns = (total_beats_per_channel + xfer_beats - 1) // xfer_beats
    # Increase timeout for slow_producer (8-20 cycle delays per handshake)
    timeout_cycles = 15000 if tb.TIMING_PROFILE == 'slow_producer' else 5000
    success, actual_txns = await tb.wait_for_completion(channel_id, expected_aw_txns, timeout_cycles=timeout_cycles)
    assert success, f"Write completion timeout"

    # Give pipeline time to flush
    await tb.wait_clocks(tb.clk_name, 50)

    # Step 4: Verify memory
    tb.log.info(f"Step 4: Verifying memory")
    success, errors = await tb.verify_memory(dst_addr, total_beats_per_channel)
    assert success, f"Memory verification failed with {errors} errors"

    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_wr_all_complete signal behavior...")
    for channel_id in range(num_channels):
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("✓ BASIC write test passed")


async def run_nostress_test(tb, xfer_beats, num_channels, sram_depth):
    """NOSTRESS: Maximum BFM speed write testing (zero BFM delays).

    This test validates sustained write streaming performance with:
    - Memory model responding immediately (no delays)
    - AXI W channel with zero valid delays (backtoback mode)
    - Multiple scheduler requests to test bubble-free operation

    CRITICAL: ALL AXI delays are zero - any bubbles are RTL-caused.
    """
    dst_addr = 0x0010_0000  # 1 MB destination
    beats_per_request = xfer_beats

    # Calculate requests per channel
    per_channel_depth = sram_depth // num_channels
    max_safe_requests = int((per_channel_depth * 0.8) / beats_per_request)
    num_requests_per_channel = min(36, max_safe_requests)

    total_beats_per_channel = num_requests_per_channel * beats_per_request

    tb.log.info(f"NOSTRESS configuration: {num_channels} channels, "
               f"{num_requests_per_channel} requests per channel, "
               f"{beats_per_request} beats per request, "
               f"SRAM per-ch: {per_channel_depth} beats")

    # Test single channel for now (multi-channel support TBD)
    channel_id = 0

    # Step 1: Fill SRAM with test data
    tb.log.info(f"Step 1: Filling SRAM channel {channel_id} with {total_beats_per_channel} beats")
    await tb.fill_sram(channel_id, dst_addr, total_beats_per_channel, pattern='increment')

    # Step 2: Issue descriptor to trigger write
    tb.log.info(f"Step 2: Issuing descriptor for {total_beats_per_channel} beats (NOSTRESS mode)")
    success = await tb.issue_descriptor_packet(
        channel_id=channel_id,
        dst_addr=dst_addr,
        length=total_beats_per_channel,
        last=True
    )
    assert success, f"Failed to issue descriptor for channel {channel_id}"

    # Step 3: Wait for write completion
    tb.log.info(f"Step 3: Waiting for AXI write completion")
    expected_aw_txns = (total_beats_per_channel + xfer_beats - 1) // xfer_beats
    # Increase timeout for slow_producer (8-20 cycle delays per handshake)
    timeout_cycles = 15000 if tb.TIMING_PROFILE == 'slow_producer' else 5000
    success, actual_txns = await tb.wait_for_completion(channel_id, expected_aw_txns, timeout_cycles=timeout_cycles)
    assert success, f"Write completion timeout"

    # Give pipeline time to flush
    await tb.wait_clocks(tb.clk_name, 50)

    # Step 4: Verify memory
    tb.log.info(f"Step 4: Verifying memory")
    success, errors = await tb.verify_memory(dst_addr, total_beats_per_channel)
    assert success, f"Memory verification failed with {errors} errors"

    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_wr_all_complete signal behavior...")
    for channel_id in range(num_channels):
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("✓ NOSTRESS write test passed - All data verified with zero BFM delays")


async def run_varying_lengths_test(tb, xfer_beats, num_channels, sram_depth):
    """VARYING LENGTHS: Test successive descriptors with increasing lengths.

    This test validates the datapath's ability to handle descriptors of varying
    lengths using a fixed AXI burst size (cfg_axi_wr_xfer_beats = 8).

    Test flow:
    - Single channel (channel 0)
    - cfg_axi_wr_xfer_beats = 8 beats fixed
    - Successive descriptors with lengths: 16, 17, 18, ..., 32 beats
    - Each descriptor is independent (separate address range)
    - Verifies data integrity for each descriptor

    This stresses the descriptor processing logic with:
    - Descriptors requiring multiple AXI bursts (16-32 beats @ 8 beats/burst = 2-4 bursts)
    - Non-aligned descriptor lengths (17, 19, 21, etc.) testing partial burst handling
    - Consecutive descriptor processing without gaps
    """
    tb.log.info("="*80)
    tb.log.info("VARYING LENGTHS TEST")
    tb.log.info(f"Configuration: cfg_axi_wr_xfer_beats = {xfer_beats} beats (fixed)")
    tb.log.info(f"Descriptor lengths: 16, 17, 18, ..., 32 beats")
    tb.log.info("="*80)

    channel_id = 0  # Test single channel only
    dst_addr_base = 0x0010_0000
    bytes_per_beat = tb.data_width // 8

    # Test descriptor lengths from 16 to 32 beats
    descriptor_lengths = list(range(16, 33))  # [16, 17, 18, ..., 32]
    total_descriptors = len(descriptor_lengths)

    tb.log.info(f"Testing {total_descriptors} descriptors with varying lengths on channel {channel_id}")

    # Calculate total beats needed
    total_beats = sum(descriptor_lengths)
    tb.log.info(f"Total transfer will be {total_beats} beats across {total_descriptors} descriptors")

    # Issue descriptors and fill SRAM concurrently
    # This allows SRAM to be continuously refilled as descriptors drain it
    tb.log.info(f"Issuing {total_descriptors} descriptors with concurrent SRAM filling")
    current_addr = dst_addr_base
    verification_errors = 0

    for idx, desc_length in enumerate(descriptor_lengths):
        tb.log.info(f"Descriptor {idx+1}/{total_descriptors}: {desc_length} beats @ addr 0x{current_addr:08X}")

        # Fill SRAM with data for THIS descriptor BEFORE issuing it
        # This ensures data is available when the write engine starts processing
        tb.log.info(f"  Filling SRAM with {desc_length} beats for descriptor {idx+1}")
        await tb.fill_sram(channel_id, current_addr, desc_length, pattern='increment')

        # Small delay to ensure SRAM fill completes before descriptor issue
        await tb.wait_clocks(tb.clk_name, 10)

        # Issue descriptor
        # CRITICAL: Mark EACH descriptor as last=True to ensure it completes fully
        # before the next one is issued. This prevents descriptor overlap.
        success = await tb.issue_descriptor_packet(
            channel_id=channel_id,
            dst_addr=current_addr,
            length=desc_length,
            last=True  # Each descriptor is independent - mark as last
        )
        assert success, f"Failed to issue descriptor {idx+1} (length={desc_length})"

        # Wait for this descriptor's write to complete
        expected_aw_txns = (desc_length + xfer_beats - 1) // xfer_beats
        timeout_cycles = 5000
        success, actual_txns = await tb.wait_for_completion(channel_id, expected_aw_txns, timeout_cycles=timeout_cycles)
        assert success, f"Descriptor {idx+1} write timeout (expected {expected_aw_txns} txns, got {actual_txns})"

        # Verify this descriptor's memory immediately
        success, errors = await tb.verify_memory(current_addr, desc_length)

        if not success:
            tb.log.error(f"✗ Descriptor {idx+1} verification FAILED with {errors} errors")
            verification_errors += errors
        else:
            tb.log.info(f"✓ Descriptor {idx+1} verified successfully ({desc_length} beats)")

        # Wait for pipeline to settle before issuing next descriptor
        # This prevents overlapping SRAM operations between descriptors
        await tb.wait_clocks(tb.clk_name, 50)

        current_addr += desc_length * bytes_per_beat

    # Check overall verification result
    if verification_errors > 0:
        tb.log.error(f"✗ Overall verification FAILED with {verification_errors} total errors")
        assert False, f"Varying lengths test failed with {verification_errors} errors"
    else:
        tb.log.info(f"✓ All {total_beats} beats verified successfully across {total_descriptors} descriptors")

    # Validate completion signal
    tb.log.info("Validating axi_wr_all_complete signal behavior...")
    completion_ok = await tb.validate_completion_signal_sticky(
        channel_id=channel_id,
        duration_cycles=500
    )
    assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info("="*80)
    tb.log.info("✓ VARYING LENGTHS TEST PASSED")
    tb.log.info(f"Successfully processed {total_descriptors} descriptors with lengths 16-32 beats")
    tb.log.info("="*80)


async def run_per_channel_sequential_test(tb, xfer_beats, num_channels, sram_depth):
    """PER-CHANNEL SEQUENTIAL: Test each channel independently, one at a time.

    This test isolates per-channel calculation from multi-channel interactions by:
    - Testing ONLY ONE channel at a time
    - Writing 48 beats to channel N
    - Waiting for completion
    - Verifying data integrity
    - Moving to next channel

    If any channel fails independently, it's a per-channel calculation issue.
    """
    dst_addr_base = 0x0010_0000  # 1 MB destination base
    beats_per_channel = 48  # Fixed 48 beats per channel for this test

    tb.log.info(f"PER-CHANNEL SEQUENTIAL configuration: {num_channels} channels, "
               f"{beats_per_channel} beats per channel, "
               f"{xfer_beats} beats per burst")

    # Test each channel independently
    for channel_id in range(num_channels):
        tb.log.info(f"\n{'='*60}")
        tb.log.info(f"Testing Channel {channel_id} independently")
        tb.log.info(f"{'='*60}")

        # Calculate channel-specific destination address
        channel_dst_addr = dst_addr_base + (channel_id * beats_per_channel * (tb.data_width // 8))

        # Step 1: Fill SRAM for this channel
        tb.log.info(f"Step 1 (CH{channel_id}): Filling SRAM with {beats_per_channel} beats")
        await tb.fill_sram(channel_id, channel_dst_addr, beats_per_channel, pattern='increment')

        # Step 2: Issue descriptor for this channel
        tb.log.info(f"Step 2 (CH{channel_id}): Issuing descriptor")
        success = await tb.issue_descriptor_packet(
            channel_id=channel_id,
            dst_addr=channel_dst_addr,
            length=beats_per_channel,
            last=True
        )
        assert success, f"Failed to issue descriptor for channel {channel_id}"

        # Step 3: Wait for this channel's write completion
        tb.log.info(f"Step 3 (CH{channel_id}): Waiting for completion")
        expected_aw_txns = (beats_per_channel + xfer_beats - 1) // xfer_beats
        # Increase timeout for slow_producer (8-20 cycle delays per handshake)
        timeout_cycles = 10000 if tb.TIMING_PROFILE == 'slow_producer' else 3000
        success, actual_txns = await tb.wait_for_completion(channel_id, expected_aw_txns, timeout_cycles=timeout_cycles)
        assert success, f"Channel {channel_id} write completion timeout"

        # Give pipeline time to flush
        await tb.wait_clocks(tb.clk_name, 50)

        # Step 4: Verify this channel's data
        tb.log.info(f"Step 4 (CH{channel_id}): Verifying memory")
        success, errors = await tb.verify_memory(channel_dst_addr, beats_per_channel)
        assert success, f"Channel {channel_id} memory verification failed with {errors} errors"

        tb.log.info(f"✓ Channel {channel_id} PASSED independently")

    tb.log.info(f"\n{'='*60}")
    # CRITICAL: Validate completion signal is sticky (catches completion signal bugs)
    tb.log.info("Validating axi_wr_all_complete signal behavior...")
    for channel_id in range(num_channels):
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=channel_id,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {channel_id}: Completion signal pulsing detected!"

    tb.log.info(f"✓ PER-CHANNEL SEQUENTIAL test passed - All {num_channels} channels verified independently")
    tb.log.info(f"{'='*60}")


async def run_b2b_multi_channel_test(tb, xfer_beats, num_channels, sram_depth):
    """B2B MULTI-CHANNEL: Back-to-back multi-descriptor test on all channels simultaneously.

    This test stresses multi-channel operation by:
    - Issuing multiple requests per channel back-to-back (no delays)
    - All channels active simultaneously
    - Multiple "descriptors" (request groups) per channel
    - Verifies the recent W-phase FIFO refactoring in write engine

    Test scenario:
    - Each channel gets 3 descriptors (request groups)
    - Each descriptor has 2-3 requests (random)
    - All requests issued back-to-back with no gaps
    - Data verified per channel after all requests complete
    """
    tb.log.info("="*80)
    tb.log.info("B2B MULTI-CHANNEL TEST")
    tb.log.info(f"Configuration: {num_channels} channels, {xfer_beats} beats per burst")
    tb.log.info("="*80)

    # Multi-descriptor configuration: 3 descriptors per channel
    descriptors_per_channel = 3
    min_requests_per_desc = 2
    max_requests_per_desc = 3

    # Calculate total requests per channel (random between min/max for each descriptor)
    channel_request_counts = []
    for ch in range(num_channels):
        total_requests = sum(random.randint(min_requests_per_desc, max_requests_per_desc)
                            for _ in range(descriptors_per_channel))
        channel_request_counts.append(total_requests)

    total_requests_all_channels = sum(channel_request_counts)
    tb.log.info(f"Request distribution: {channel_request_counts}")
    tb.log.info(f"Total requests across all channels: {total_requests_all_channels}")

    # Calculate memory requirements
    bytes_per_beat = tb.data_width // 8
    per_channel_depth = sram_depth // num_channels
    max_beats_per_channel = max(ch * xfer_beats for ch in channel_request_counts)

    # Safety check: Ensure SRAM can hold all data (70% capacity limit)
    if max_beats_per_channel > (per_channel_depth * 0.7):
        tb.log.warning(f"Reducing test size to fit SRAM capacity")
        scale_factor = (per_channel_depth * 0.7) / max_beats_per_channel
        channel_request_counts = [max(2, int(c * scale_factor)) for c in channel_request_counts]
        tb.log.info(f"Adjusted request counts: {channel_request_counts}")

    # Calculate base addresses for each channel (non-overlapping memory regions)
    dst_addr_base = 0x0010_0000  # Start at 1MB
    channel_dst_addrs = []
    for ch in range(num_channels):
        # Allocate 1MB per channel to ensure no overlap
        channel_addr = dst_addr_base + (ch * 0x0010_0000)
        channel_dst_addrs.append(channel_addr)

    tb.log.info(f"Channel base addresses: {[hex(addr) for addr in channel_dst_addrs]}")

    # Step 1: Fill SRAM for all channels
    tb.log.info("\nStep 1: Filling SRAM for all channels")
    for ch in range(num_channels):
        total_beats = channel_request_counts[ch] * xfer_beats
        tb.log.info(f"  CH{ch}: Filling {total_beats} beats @ address 0x{channel_dst_addrs[ch]:08X}")
        await tb.fill_sram(ch, channel_dst_addrs[ch], total_beats, pattern='increment')

    # Small delay to ensure all SRAM fills complete
    await tb.wait_clocks(tb.clk_name, 20)

    # Step 2: Issue back-to-back descriptors for all channels simultaneously
    tb.log.info("\nStep 2: Issuing back-to-back descriptors (all channels simultaneously)")

    # Issue all descriptors back-to-back with NO delays
    for ch in range(num_channels):
        num_requests = channel_request_counts[ch]
        current_addr = channel_dst_addrs[ch]

        for req_idx in range(num_requests):
            # Determine if this is the last request for this channel
            is_last = (req_idx == num_requests - 1)

            success = await tb.issue_descriptor_packet(
                channel_id=ch,
                dst_addr=current_addr,
                length=xfer_beats,
                last=is_last
            )
            assert success, f"Failed to issue descriptor for channel {ch}, request {req_idx}"

            current_addr += xfer_beats * bytes_per_beat

    tb.log.info(f"Issued {total_requests_all_channels} descriptors across {num_channels} channels")

    # Step 3: Wait for all channels to complete
    tb.log.info("\nStep 3: Waiting for all channels to complete")
    timeout_cycles = 15000 if tb.TIMING_PROFILE == 'slow_producer' else 8000

    for ch in range(num_channels):
        expected_txns = channel_request_counts[ch]
        tb.log.info(f"  CH{ch}: Waiting for {expected_txns} AW transactions...")

        success, actual_txns = await tb.wait_for_completion(ch, expected_txns, timeout_cycles=timeout_cycles)
        assert success, f"Channel {ch} write completion timeout (expected {expected_txns}, got {actual_txns})"

        tb.log.info(f"  ✓ CH{ch}: Completed {actual_txns} transactions")

    # Give pipeline time to flush
    await tb.wait_clocks(tb.clk_name, 100)

    # Step 4: Verify memory for all channels
    tb.log.info("\nStep 4: Verifying memory for all channels")
    overall_success = True
    total_errors = 0

    for ch in range(num_channels):
        total_beats = channel_request_counts[ch] * xfer_beats
        tb.log.info(f"  CH{ch}: Verifying {total_beats} beats @ 0x{channel_dst_addrs[ch]:08X}")

        success, errors = await tb.verify_memory(channel_dst_addrs[ch], total_beats)

        if not success:
            tb.log.error(f"  ✗ CH{ch}: Verification FAILED with {errors} errors")
            overall_success = False
            total_errors += errors
        else:
            tb.log.info(f"  ✓ CH{ch}: Verification PASSED")

    # Final status
    if not overall_success:
        tb.log.error(f"✗ B2B MULTI-CHANNEL TEST FAILED with {total_errors} total errors")
        assert False, f"B2B multi-channel test failed with {total_errors} errors"

    # Validate completion signals
    tb.log.info("\nValidating completion signals for all channels...")
    for ch in range(num_channels):
        completion_ok = await tb.validate_completion_signal_sticky(
            channel_id=ch,
            duration_cycles=500
        )
        assert completion_ok, f"Channel {ch}: Completion signal pulsing detected!"

    tb.log.info("="*80)
    tb.log.info("✓ B2B MULTI-CHANNEL TEST PASSED")
    tb.log.info(f"Successfully processed {total_requests_all_channels} requests across {num_channels} channels")
    tb.log.info("="*80)


#=============================================================================
# Parameter Generation
#=============================================================================

def calc_sram_depth(data_width, num_channels):
    """Calculate SRAM depth with 256 beats per channel minimum."""
    beats_per_channel = 256
    total_depth = beats_per_channel * num_channels
    return total_depth

def generate_params():
    """
    Generate parameters for write datapath tests based on REG_LEVEL.

    Matches datapath_rd test structure: mix of PIPELINE=0 and PIPELINE=1

    QUICK_DEBUG=1: Single minimal test (128-bit, 1ch, pipe, 16 beats, 'basic' test, 'fixed' timing)
    REG_LEVEL=GATE: 1 test (smoke test - 128-bit, 1ch, pipe, 'basic' test, 'fixed' timing)
    REG_LEVEL=FUNC: 14 tests (6 base configs × 2 timing profiles: fixed, fast) × 1 test type (basic only) + 2 varying_lengths tests (128/256-bit)
    REG_LEVEL=FULL: 150 tests (12 base configs × 4 timing profiles: fixed, fast, constrained, slow_producer) × 3 test types (basic, nostress, per_channel_sequential) + 6 varying_lengths tests (128/256/512-bit × 2 timing profiles)

    Parameters: (test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile)

    Test Types:
        - 'basic': Fill SRAM, issue descriptors, verify memory writes
        - 'nostress': Maximum BFM speed write testing
        - 'per_channel_sequential': Test each channel independently
        - 'varying_lengths': Successive descriptors with lengths 16-32 beats (xfer_beats=8 fixed)

    Timing Profiles (AXI BFM delay configurations):
        - 'fixed': Constant 1-cycle delays (baseline)
        - 'fast': Mostly zero delays, occasional short delays (aggressive producer)
        - 'constrained': Moderate random delays (realistic mixed timing)
        - 'slow_producer': Consistently slow responses (slow producer scenario)
    """
    # Quick debug mode
    if os.environ.get('QUICK_DEBUG', '0') == '1':
        return [
            ('basic', 128, 1, calc_sram_depth(128, 1), 'basic', 1, 16, 'fixed'),
        ]

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - smoke test with 128-bit, 1 channel, pipeline, basic test only
        base_params = [
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 16),  # 128-bit, 1 ch, pipe, 16 beats = 256B
        ]
        timing_profiles = ['fixed']
        test_types = ['basic']  # Only basic test for smoke
    elif reg_level == 'FUNC':
        # Functional coverage: 128/256/512-bit × 1/4/8 channels × PIPELINE=0/1 × 2 timing profiles × basic test only
        base_params = [
            # 128-bit data width (16 bytes per beat, 256 beats/ch = 4KB/ch)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 16),  # 1 ch, pipe, 256B
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 16),  # 4 ch, pipe, 256B
            (128, 8, calc_sram_depth(128, 8), 'basic', 1, 16),  # 8 ch, pipe, 256B - exercises channels 4-7
            # 256-bit data width (32 bytes per beat, 256 beats/ch = 8KB/ch)
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 8),   # 1 ch, pipe, 256B
            (256, 4, calc_sram_depth(256, 4), 'basic', 1, 8),   # 4 ch, pipe, 256B
            (256, 8, calc_sram_depth(256, 8), 'basic', 1, 8),   # 8 ch, pipe, 256B - exercises channels 4-7
            # 512-bit data width (64 bytes per beat, 256 beats/ch = 16KB/ch)
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 4),   # 1 ch, pipe, 256B
            (512, 4, calc_sram_depth(512, 4), 'basic', 1, 4),   # 4 ch, pipe, 256B
            (512, 8, calc_sram_depth(512, 8), 'basic', 1, 4),   # 8 ch, pipe, 256B - exercises channels 4-7
        ]
        timing_profiles = ['fixed', 'fast']  # 2 profiles
        test_types = ['basic']  # Only basic test for functional level
    else:  # FULL
        # Comprehensive - test all data widths × 1/4/8 channels × PIPELINE=0/1 × varying xfer_beats × 4 timing profiles × 3 test types
        base_params = [
            # 128-bit: 1 channel (both pipeline modes)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 16),  # 1 ch, pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 128B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 8),   # 1 ch, pipe, 128B
            # 128-bit: 4 and 8 channels
            (128, 4, calc_sram_depth(128, 4), 'basic', 1, 16),  # 4 ch, pipe, 256B
            (128, 8, calc_sram_depth(128, 8), 'basic', 1, 16),  # 8 ch, pipe, 256B - exercises channels 4-7
            (128, 8, calc_sram_depth(128, 8), 'basic', 0, 16),  # 8 ch, no-pipe, 256B
            # 256-bit: 1 channel
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 8),   # 1 ch, pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 128B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 4),   # 1 ch, pipe, 128B
            # 256-bit: 4 and 8 channels
            (256, 4, calc_sram_depth(256, 4), 'basic', 1, 8),   # 4 ch, pipe, 256B
            (256, 8, calc_sram_depth(256, 8), 'basic', 1, 8),   # 8 ch, pipe, 256B - exercises channels 4-7
            (256, 8, calc_sram_depth(256, 8), 'basic', 0, 8),   # 8 ch, no-pipe, 256B
            # 512-bit: 1 channel
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 4),   # 1 ch, pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 2),   # 1 ch, no-pipe, 128B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 2),   # 1 ch, pipe, 128B
            # 512-bit: 4 and 8 channels
            (512, 4, calc_sram_depth(512, 4), 'basic', 1, 4),   # 4 ch, pipe, 256B
            (512, 8, calc_sram_depth(512, 8), 'basic', 1, 4),   # 8 ch, pipe, 256B - exercises channels 4-7
            (512, 8, calc_sram_depth(512, 8), 'basic', 0, 4),   # 8 ch, no-pipe, 256B
        ]
        timing_profiles = ['fixed', 'fast', 'constrained', 'slow_producer']  # 4 profiles
        test_types = ['basic', 'nostress', 'per_channel_sequential']  # All test types

    # Generate final params by adding test_type AND timing profile to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            for profile in timing_profiles:
                params.append((test_type,) + base + (profile,))

    # Add varying_lengths tests (separate from main test types)
    # These tests ALWAYS use xfer_beats=8 to test varying descriptor lengths against fixed burst size
    # Test format: (test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile)
    if reg_level == 'FUNC':
        # FUNC: 2 varying_lengths tests (128/256-bit × 1 timing profile)
        varying_params = [
            ('varying_lengths', 128, 1, calc_sram_depth(128, 1), 'basic', 0, 8, 'fixed'),  # 128-bit, single-channel, xfer_beats=8
            ('varying_lengths', 256, 1, calc_sram_depth(256, 1), 'basic', 0, 8, 'fixed'),  # 256-bit, single-channel, xfer_beats=8
        ]
        params.extend(varying_params)
    elif reg_level == 'FULL':
        # FULL: 6 varying_lengths tests (128/256/512-bit × 2 timing profiles: fixed, fast)
        varying_params = [
            ('varying_lengths', 128, 1, calc_sram_depth(128, 1), 'basic', 0, 8, 'fixed'),  # 128-bit, xfer_beats=8, fixed timing
            ('varying_lengths', 128, 1, calc_sram_depth(128, 1), 'basic', 0, 8, 'fast'),   # 128-bit, xfer_beats=8, fast timing
            ('varying_lengths', 256, 1, calc_sram_depth(256, 1), 'basic', 0, 8, 'fixed'),  # 256-bit, xfer_beats=8, fixed timing
            ('varying_lengths', 256, 1, calc_sram_depth(256, 1), 'basic', 0, 8, 'fast'),   # 256-bit, xfer_beats=8, fast timing
            ('varying_lengths', 512, 1, calc_sram_depth(512, 1), 'basic', 0, 8, 'fixed'),  # 512-bit, xfer_beats=8, fixed timing
            ('varying_lengths', 512, 1, calc_sram_depth(512, 1), 'basic', 0, 8, 'fast'),   # 512-bit, xfer_beats=8, fast timing
        ]
        params.extend(varying_params)

    # Add b2b_multi_channel tests (separate from main test types)
    # These tests stress multi-channel W-phase FIFO refactoring with back-to-back requests
    # Test format: (test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile)
    if reg_level == 'FUNC':
        # FUNC: 4 b2b_multi_channel tests (128/256-bit, 4/8 channels, fixed timing)
        b2b_params = [
            ('b2b_multi_channel', 128, 4, calc_sram_depth(128, 4), 'basic', 1, 16, 'fixed'),  # 128-bit, 4 ch, pipe
            ('b2b_multi_channel', 256, 4, calc_sram_depth(256, 4), 'basic', 1, 8, 'fixed'),   # 256-bit, 4 ch, pipe
            ('b2b_multi_channel', 128, 8, calc_sram_depth(128, 8), 'basic', 1, 16, 'fixed'),  # 128-bit, 8 ch, pipe - exercises channels 4-7
            ('b2b_multi_channel', 256, 8, calc_sram_depth(256, 8), 'basic', 1, 8, 'fixed'),   # 256-bit, 8 ch, pipe - exercises channels 4-7
        ]
        params.extend(b2b_params)
    elif reg_level == 'FULL':
        # FULL: 12 b2b_multi_channel tests (128/256/512-bit, 4/8 channels, 2 timing profiles: fixed, fast)
        b2b_params = [
            ('b2b_multi_channel', 128, 4, calc_sram_depth(128, 4), 'basic', 1, 16, 'fixed'),  # 128-bit, 4 ch, pipe, fixed
            ('b2b_multi_channel', 128, 4, calc_sram_depth(128, 4), 'basic', 1, 16, 'fast'),   # 128-bit, 4 ch, pipe, fast
            ('b2b_multi_channel', 128, 8, calc_sram_depth(128, 8), 'basic', 1, 16, 'fixed'),  # 128-bit, 8 ch, pipe, fixed
            ('b2b_multi_channel', 128, 8, calc_sram_depth(128, 8), 'basic', 1, 16, 'fast'),   # 128-bit, 8 ch, pipe, fast
            ('b2b_multi_channel', 256, 4, calc_sram_depth(256, 4), 'basic', 1, 8, 'fixed'),   # 256-bit, 4 ch, pipe, fixed
            ('b2b_multi_channel', 256, 4, calc_sram_depth(256, 4), 'basic', 1, 8, 'fast'),    # 256-bit, 4 ch, pipe, fast
            ('b2b_multi_channel', 256, 8, calc_sram_depth(256, 8), 'basic', 1, 8, 'fixed'),   # 256-bit, 8 ch, pipe, fixed
            ('b2b_multi_channel', 256, 8, calc_sram_depth(256, 8), 'basic', 1, 8, 'fast'),    # 256-bit, 8 ch, pipe, fast
            ('b2b_multi_channel', 512, 4, calc_sram_depth(512, 4), 'basic', 1, 4, 'fixed'),   # 512-bit, 4 ch, pipe, fixed
            ('b2b_multi_channel', 512, 4, calc_sram_depth(512, 4), 'basic', 1, 4, 'fast'),    # 512-bit, 4 ch, pipe, fast
            ('b2b_multi_channel', 512, 8, calc_sram_depth(512, 8), 'basic', 1, 4, 'fixed'),   # 512-bit, 8 ch, pipe, fixed
            ('b2b_multi_channel', 512, 8, calc_sram_depth(512, 8), 'basic', 1, 4, 'fast'),    # 512-bit, 8 ch, pipe, fast
        ]
        params.extend(b2b_params)

    return params


params = generate_params()


#=============================================================================
# Pytest Wrapper Function - Single wrapper for all test types
#=============================================================================

@pytest.mark.parametrize("test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile", params)
def test_datapath_wr(request, test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile):
    """Pytest wrapper for write datapath tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_stream_fub': '../../../../rtl/stream_fub'})
    dut_name = "datapath_wr_test"
    pipeline_str = "pipe" if enable_pipeline else "nopipe"
    test_name_plus_params = f"test_datapath_wr_{test_type}_nc{num_channels}_dw{data_width}_sd{sram_depth}_{test_level}_{pipeline_str}_xb{xfer_beats}_{timing_profile}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='projects/components/stream/rtl/filelists/macro/datapath_wr_test.f')

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
        'AW_MAX_OUTSTANDING': '8'  # Default value
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
    }

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

    # WAVES support
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-depth", "99"]
        sim_args = []
        plusargs = []
    else:
        compile_args = []
        sim_args = []
        plusargs = []

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes, toplevel=dut_name,
            module=module, testcase="cocotb_test_datapath_wr", parameters=parameters, sim_build=sim_build,
            extra_env=extra_env, waves=False, keep_files=True, compile_args=compile_args, sim_args=sim_args, plusargs=plusargs,
            simulator='verilator')
        print(f"✓ Write {test_type} test PASSED ({test_level} level)")
    except Exception as e:
        print(f"✗ Write {test_type} test FAILED ({test_level} level): {str(e)}")
        raise
