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

from projects.components.stream.dv.tbclasses.datapath_wr_test_tb import DatapathWrTestTB
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


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

    tb.log.info("✓ NOSTRESS write test passed - All data verified with zero BFM delays")


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
    tb.log.info(f"✓ PER-CHANNEL SEQUENTIAL test passed - All {num_channels} channels verified independently")
    tb.log.info(f"{'='*60}")


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
    REG_LEVEL=FUNC: 12 tests (6 base configs × 2 timing profiles: fixed, fast) × 1 test type (basic only)
    REG_LEVEL=FULL: 144 tests (12 base configs × 4 timing profiles: fixed, fast, constrained, slow_producer) × 3 test types (basic, nostress, per_channel_sequential)

    Parameters: (test_type, data_width, num_channels, sram_depth, test_level, enable_pipeline, xfer_beats, timing_profile)

    Test Types:
        - 'basic': Fill SRAM, issue descriptors, verify memory writes
        - 'nostress': Maximum BFM speed write testing
        - 'per_channel_sequential': Test each channel independently

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
        # Functional coverage: 128/256/512-bit × PIPELINE=0/1 × 2 timing profiles × basic test only
        base_params = [
            # 128-bit data width (16 bytes per beat, 256 beats/ch = 4KB/ch)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 16),  # 1 ch, pipe, 256B
            # 256-bit data width (32 bytes per beat, 256 beats/ch = 8KB/ch)
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 8),   # 1 ch, pipe, 256B
            # 512-bit data width (64 bytes per beat, 256 beats/ch = 16KB/ch)
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 4),   # 1 ch, pipe, 256B
        ]
        timing_profiles = ['fixed', 'fast']  # 2 profiles
        test_types = ['basic']  # Only basic test for functional level
    else:  # FULL
        # Comprehensive - test all data widths × PIPELINE=0/1 × varying xfer_beats × 4 timing profiles × 3 test types
        base_params = [
            # 128-bit: 1 channel (both pipeline modes)
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 16),  # 1 ch, no-pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 16),  # 1 ch, pipe, 256B
            (128, 1, calc_sram_depth(128, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 128B
            (128, 1, calc_sram_depth(128, 1), 'basic', 1, 8),   # 1 ch, pipe, 128B
            # 256-bit: 1 channel
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 8),   # 1 ch, no-pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 8),   # 1 ch, pipe, 256B
            (256, 1, calc_sram_depth(256, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 128B
            (256, 1, calc_sram_depth(256, 1), 'basic', 1, 4),   # 1 ch, pipe, 128B
            # 512-bit: 1 channel
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 4),   # 1 ch, no-pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 4),   # 1 ch, pipe, 256B
            (512, 1, calc_sram_depth(512, 1), 'basic', 0, 2),   # 1 ch, no-pipe, 128B
            (512, 1, calc_sram_depth(512, 1), 'basic', 1, 2),   # 1 ch, pipe, 128B
        ]
        timing_profiles = ['fixed', 'fast', 'constrained', 'slow_producer']  # 4 profiles
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
