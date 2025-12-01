"""
================================================================================
Stream Top Advanced Integration Tests
================================================================================

Advanced test suite for stream_top_ch8 - comprehensive STREAM DMA testing.

Test Suite Contents:
1. test_multi_channel_concurrent - Run 4 channels simultaneously
2. test_long_descriptor_chain - Test 8+ descriptor chains
3. test_variable_transfer_sizes - Test various transfer sizes (1, 16, 64, 128, 255 beats)
4. test_stress_all_channels - All 8 channels with heavy load
5. test_register_access - Comprehensive APB register read/write validation
6. test_back_to_back_transfers - Multiple sequential transfers per channel

Test Level Control (TEST_LEVEL environment variable):
- basic:  Quick smoke tests (~30s each) - minimal iterations, small transfers
- medium: Moderate coverage (~60-90s each) - standard iterations, medium transfers
- full:   Comprehensive validation (~180s each) - maximum iterations, all edge cases

Usage:
    # Run with default (basic) level
    pytest test_stream_top_advanced.py -v

    # Run with medium coverage
    TEST_LEVEL=medium pytest test_stream_top_advanced.py -v

    # Run with full coverage
    TEST_LEVEL=full pytest test_stream_top_advanced.py -v

These tests exercise:
- Multi-channel arbitration
- Long descriptor chain following
- Edge case transfer sizes
- Maximum throughput scenarios
- APB register functionality
- Channel reset and re-use

Author: RTL Design Sherpa
Date: 2025-11-30
"""

import os
import sys
import pytest
import cocotb
import random


# ==============================================================================
# Test Level Configuration
# ==============================================================================

def get_test_level_config():
    """
    Get test configuration based on TEST_LEVEL environment variable.

    Returns dict with level-specific parameters for all tests.
    """
    level = os.environ.get('TEST_LEVEL', 'basic').lower()

    configs = {
        'basic': {
            # Quick smoke tests (~30s each)
            'multi_channel': {
                'channels': [0, 1],
                'desc_count': 2,
                'transfer_sizes': [32],
            },
            'long_chain': {
                'chain_length': 4,
                'transfer_size': 16,
            },
            'variable_sizes': {
                'transfer_sizes': [1, 16, 64],
            },
            'stress': {
                'channels': 4,  # Only 4 channels
                'desc_count': 2,
                'transfer_sizes': [32],
            },
            'registers': {
                'test_patterns': [0x00, 0xFF, 0xAA],
            },
            'back_to_back': {
                'iterations': 3,
                'transfer_size': 16,
            },
        },
        'medium': {
            # Moderate coverage (~60-90s each)
            'multi_channel': {
                'channels': [0, 1, 2, 3],
                'desc_count': 4,
                'transfer_sizes': [32, 64],
            },
            'long_chain': {
                'chain_length': 8,
                'transfer_size': 32,
            },
            'variable_sizes': {
                'transfer_sizes': [1, 4, 16, 32, 64, 128],
            },
            'stress': {
                'channels': 6,
                'desc_count': 3,
                'transfer_sizes': [32, 48],
            },
            'registers': {
                'test_patterns': [0x00, 0xFF, 0xAA, 0x55, 0x0F, 0xF0],
            },
            'back_to_back': {
                'iterations': 5,
                'transfer_size': 32,
            },
        },
        'full': {
            # Comprehensive validation (~180s each)
            'multi_channel': {
                'channels': [0, 1, 2, 3, 4, 5, 6, 7],
                'desc_count': 6,
                'transfer_sizes': [32, 48, 64, 96],
            },
            'long_chain': {
                'chain_length': 16,
                'transfer_size': 48,
            },
            'variable_sizes': {
                'transfer_sizes': [1, 2, 4, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255],
            },
            'stress': {
                'channels': 8,  # All 8 channels
                'desc_count': 6,
                'transfer_sizes': [32, 48, 64, 96],
            },
            'registers': {
                'test_patterns': [0x00, 0xFF, 0xAA, 0x55, 0x0F, 0xF0, 0x01, 0x80, 0x42],
            },
            'back_to_back': {
                'iterations': 10,
                'transfer_size': 64,
            },
        },
    }

    return configs.get(level, configs['basic'])

# CRITICAL: Must setup paths BEFORE importing from CocoTBFramework
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Import utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, get_repo_root, create_view_cmd
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Use proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB, StreamRegisterMap


# ==============================================================================
# Common Test Infrastructure
# ==============================================================================

async def setup_stream_testbench(dut, rd_xfer_beats=16, wr_xfer_beats=16):
    """Common setup for all stream_top tests."""
    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '4096'))
    axi_id_width = int(os.environ.get('AXI_ID_WIDTH', '8'))
    apb_addr_width = int(os.environ.get('APB_ADDR_WIDTH', '12'))
    apb_data_width = int(os.environ.get('APB_DATA_WIDTH', '32'))

    # Initialize testbench
    tb = StreamCoreTB(
        dut=dut,
        num_channels=num_channels,
        addr_width=64,
        data_width=data_width,
        axi_id_width=axi_id_width,
        fifo_depth=fifo_depth,
        apb_addr_width=apb_addr_width,
        apb_data_width=apb_data_width
    )

    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)
    await tb.init_apb_master()

    # Basic initialization
    version = await tb.read_apb_register(0x108)  # VERSION register
    tb.log.info(f"STREAM version: 0x{version:08X}")

    await tb.enable_global()
    channel_mask = (1 << num_channels) - 1
    await tb.enable_channel_mask(channel_mask)
    await tb.configure_transfer_beats(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)
    await tb.configure_descriptor_address_range()

    return tb


def create_channel_descriptors(tb, channel, desc_count, transfer_sizes, base_offset=0):
    """Create descriptor chain for a channel and return descriptor list."""
    # Use smaller offsets to fit within memory model bounds
    # Descriptor memory: 512KB, use 8KB per channel (fits 8 channels)
    # Source/Dest memory: 32MB each, use 4MB per channel (fits 8 channels)
    desc_channel_offset = channel * 0x2000  # 8KB per channel for descriptors
    data_channel_offset = channel * 0x400000  # 4MB per channel for data

    base_src_addr = tb.src_mem_base + data_channel_offset + base_offset
    base_dst_addr = tb.dst_mem_base + data_channel_offset + base_offset

    descriptors = []

    for i in range(desc_count):
        # Rotate through transfer sizes
        transfer_size = transfer_sizes[i % len(transfer_sizes)]

        # Descriptor address (64-byte spacing, plenty of room with 8KB per channel)
        desc_addr = tb.desc_mem_base + desc_channel_offset + base_offset + (i * 64)
        next_desc_addr = desc_addr + 64 if i < desc_count - 1 else 0

        # Source/destination addresses (0x10000 = 64KB offset per descriptor)
        src_addr = base_src_addr + (i * 0x10000)
        dst_addr = base_dst_addr + (i * 0x10000)

        # Write test pattern to source memory
        for beat in range(transfer_size):
            beat_addr = src_addr + (beat * tb.data_bytes)
            # Pattern includes channel and descriptor index
            pattern = ((channel << 8) | (i << 4) | (beat & 0xF)) & 0xFF
            data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
            tb.write_source_data(beat_addr, data, tb.data_bytes)

        # Write descriptor to memory
        is_last = (i == desc_count - 1)
        tb.write_descriptor(
            addr=desc_addr,
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=transfer_size,
            next_ptr=next_desc_addr,
            priority=channel,  # Use channel as priority for testing
            last=is_last,
            channel_id=channel,
            interrupt=is_last
        )

        descriptors.append({
            'src_addr': src_addr,
            'dst_addr': dst_addr,
            'length': transfer_size,
            'desc_addr': desc_addr
        })

    return descriptors


# ==============================================================================
# CocoTB Test 1: Multi-Channel Concurrent
# ==============================================================================

@cocotb.test(timeout_time=5000, timeout_unit="us")
async def cocotb_test_multi_channel_concurrent(dut):
    """
    Test multiple channels running concurrently.

    This tests:
    - Channel arbitration
    - Resource sharing (AXI masters, SRAM)
    - Concurrent data integrity

    Scales with TEST_LEVEL:
    - basic:  2 channels, 2 descriptors each
    - medium: 4 channels, 4 descriptors each
    - full:   8 channels, 6 descriptors each
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['multi_channel']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    test_channels = test_config['channels']
    desc_count = test_config['desc_count']
    transfer_sizes = test_config['transfer_sizes']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Multi-Channel Concurrent Test (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Channels: {test_channels}, Descriptors per channel: {desc_count}")
    tb.log.info(f"Transfer sizes: {transfer_sizes}")

    # Create descriptors for all channels
    channel_descriptors = {}
    for channel in test_channels:
        descriptors = create_channel_descriptors(tb, channel, desc_count, transfer_sizes)
        channel_descriptors[channel] = descriptors
        tb.log.info(f"Created {len(descriptors)} descriptors for channel {channel}")

    # Kick off ALL channels simultaneously
    tb.log.info("\n=== Kicking off all channels concurrently ===")
    for channel in test_channels:
        first_desc_addr = tb.desc_mem_base + (channel * 0x2000)  # 8KB per channel
        await tb.kick_off_channel(channel, first_desc_addr)

    # Wait for all channels to complete
    tb.log.info("\n=== Waiting for all channels to complete ===")
    for channel in test_channels:
        success = await tb.wait_for_channel_idle(channel, timeout_us=500)
        if not success:
            raise AssertionError(f"Channel {channel} failed to complete")

    # Verify all transfers
    tb.log.info("\n=== Verifying all channel transfers ===")
    all_passed = True
    for channel in test_channels:
        tb.log.info(f"\nVerifying channel {channel}...")
        for idx, desc in enumerate(channel_descriptors[channel]):
            match = tb.verify_transfer(desc['src_addr'], desc['dst_addr'], desc['length'])
            if not match:
                tb.log.error(f"Channel {channel} Transfer {idx} FAILED")
                all_passed = False
            else:
                tb.log.info(f"Channel {channel} Transfer {idx} ({desc['length']} beats) OK")

    if not all_passed:
        raise AssertionError("Multi-channel concurrent test failed - data mismatch")

    # Print performance summary
    tb.log.info("\n=== Performance Summary ===")
    for channel in test_channels:
        stats = tb.get_performance_stats(channel)
        if stats:
            total_beats = sum(d['length'] for d in channel_descriptors[channel])
            tb.log.info(f"Channel {channel}: {stats['duration_ns']:.0f}ns for {total_beats} beats")

    tb.log.info("\n=== Multi-Channel Concurrent Test PASSED ===")


# ==============================================================================
# CocoTB Test 2: Long Descriptor Chain
# ==============================================================================

@cocotb.test(timeout_time=5000, timeout_unit="us")
async def cocotb_test_long_descriptor_chain(dut):
    """
    Test long descriptor chains (4-16 descriptors).

    This tests:
    - Descriptor chain following
    - Next pointer handling
    - Long-running transfers

    Scales with TEST_LEVEL:
    - basic:  4 descriptors, 16 beats each
    - medium: 8 descriptors, 32 beats each
    - full:   16 descriptors, 48 beats each
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['long_chain']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    channel = 0  # Always use channel 0 for this test
    chain_length = test_config['chain_length']
    transfer_size = test_config['transfer_size']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Long Descriptor Chain Test (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Channel: {channel}, Chain length: {chain_length}, Transfer size: {transfer_size}")

    # Create long descriptor chain
    transfer_sizes = [transfer_size]  # All same size for this test
    descriptors = create_channel_descriptors(tb, channel, chain_length, transfer_sizes)

    tb.log.info(f"\nCreated chain of {len(descriptors)} descriptors")
    for i, desc in enumerate(descriptors):
        tb.log.info(f"  Desc {i}: src=0x{desc['src_addr']:08X}, len={desc['length']}")

    # Kick off channel
    first_desc_addr = tb.desc_mem_base + (channel * 0x2000)  # 8KB per channel
    await tb.kick_off_channel(channel, first_desc_addr)

    # Wait for completion with longer timeout for long chain
    timeout_us = chain_length * 100  # ~100us per descriptor
    success = await tb.wait_for_channel_idle(channel, timeout_us=max(timeout_us, 1000))
    if not success:
        raise AssertionError(f"Long descriptor chain failed to complete")

    # Verify all transfers
    tb.log.info("\n=== Verifying descriptor chain ===")
    results = tb.verify_descriptor_chain(descriptors)

    if results['failed_descriptors'] > 0:
        raise AssertionError(f"Long chain test failed: {results['failed_descriptors']} descriptors had errors")

    # Performance stats
    stats = tb.get_performance_stats(channel)
    total_beats = chain_length * transfer_size
    if stats:
        tb.log.info(f"\nPerformance: {total_beats} beats in {stats['duration_ns']:.0f}ns")
        beats_per_ns = total_beats / stats['duration_ns']
        tb.log.info(f"Throughput: {beats_per_ns:.4f} beats/ns")

    tb.log.info("\n=== Long Descriptor Chain Test PASSED ===")


# ==============================================================================
# CocoTB Test 3: Variable Transfer Sizes
# ==============================================================================

@cocotb.test(timeout_time=5000, timeout_unit="us")
async def cocotb_test_variable_transfer_sizes(dut):
    """
    Test various transfer sizes including edge cases.

    This tests:
    - Minimum transfer (1 beat)
    - Small transfers (< AXI burst size)
    - Exact AXI burst size
    - Multi-burst transfers
    - Large transfers

    Scales with TEST_LEVEL:
    - basic:  3 sizes (1, 16, 64)
    - medium: 6 sizes (1, 4, 16, 32, 64, 128)
    - full:   16 sizes (all edge cases including boundary-1 and boundary+1)
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['variable_sizes']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    channel = 0  # Always use channel 0 for this test
    transfer_sizes = test_config['transfer_sizes']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Variable Transfer Sizes Test (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Channel: {channel}")
    tb.log.info(f"Transfer sizes to test: {transfer_sizes}")

    all_passed = True

    for idx, size in enumerate(transfer_sizes):
        tb.log.info(f"\n--- Testing transfer size: {size} beats ---")

        # Create single descriptor for this size
        # Use 256-byte spacing for descriptors (plenty of room)
        # Use 64KB spacing for data (fits many sizes in memory)
        desc_addr = tb.desc_mem_base + (channel * 0x2000) + (idx * 256)
        src_addr = tb.src_mem_base + (channel * 0x400000) + (idx * 0x10000)
        dst_addr = tb.dst_mem_base + (channel * 0x400000) + (idx * 0x10000)

        # Write test pattern
        for beat in range(size):
            beat_addr = src_addr + (beat * tb.data_bytes)
            pattern = ((idx << 8) | (beat & 0xFF)) & 0xFF
            data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
            tb.write_source_data(beat_addr, data, tb.data_bytes)

        # Write descriptor
        tb.write_descriptor(
            addr=desc_addr,
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=size,
            next_ptr=0,
            priority=0,
            last=True,
            interrupt=True
        )

        # Kick off transfer
        await tb.kick_off_channel(channel, desc_addr)

        # Wait for completion
        timeout_us = max(size * 5, 200)  # Scale timeout with size
        success = await tb.wait_for_channel_idle(channel, timeout_us=timeout_us)

        if not success:
            tb.log.error(f"Transfer size {size} TIMEOUT")
            all_passed = False
            continue

        # Verify
        match = tb.verify_transfer(src_addr, dst_addr, size)
        if not match:
            tb.log.error(f"Transfer size {size} DATA MISMATCH")
            all_passed = False
        else:
            tb.log.info(f"Transfer size {size} PASSED")

    if not all_passed:
        raise AssertionError("Variable transfer sizes test failed")

    tb.log.info("\n=== Variable Transfer Sizes Test PASSED ===")


# ==============================================================================
# CocoTB Test 4: Stress Test - All 8 Channels
# ==============================================================================

@cocotb.test(timeout_time=10000, timeout_unit="us")
async def cocotb_test_stress_all_channels(dut):
    """
    Stress test with multiple channels running concurrently.

    This tests:
    - Maximum resource contention
    - Multiple channels active simultaneously
    - Arbitration fairness
    - System throughput under load

    Scales with TEST_LEVEL:
    - basic:  4 channels, 2 descriptors each
    - medium: 6 channels, 3 descriptors each
    - full:   8 channels, 6 descriptors each
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['stress']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    num_channels = test_config['channels']
    desc_per_channel = test_config['desc_count']
    transfer_sizes = test_config['transfer_sizes']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Stress Test - {num_channels} Channels (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Channels: {num_channels}, Descriptors per channel: {desc_per_channel}")
    tb.log.info(f"Transfer sizes: {transfer_sizes}")

    # Create descriptors for all 8 channels
    channel_descriptors = {}
    for channel in range(num_channels):
        descriptors = create_channel_descriptors(tb, channel, desc_per_channel, transfer_sizes)
        channel_descriptors[channel] = descriptors

    total_descriptors = num_channels * desc_per_channel
    total_beats = sum(sum(d['length'] for d in descs) for descs in channel_descriptors.values())
    tb.log.info(f"Total: {total_descriptors} descriptors, {total_beats} beats")

    # Kick off ALL channels at once
    tb.log.info(f"\n=== Kicking off all {num_channels} channels ===")
    import cocotb.utils
    start_time = cocotb.utils.get_sim_time('ns')

    for channel in range(num_channels):
        first_desc_addr = tb.desc_mem_base + (channel * 0x2000)  # 8KB per channel
        await tb.kick_off_channel(channel, first_desc_addr)

    # Wait for all channels
    tb.log.info("\n=== Waiting for all channels to complete ===")
    all_completed = True
    for channel in range(num_channels):
        success = await tb.wait_for_channel_idle(channel, timeout_us=2000)
        if not success:
            tb.log.error(f"Channel {channel} TIMEOUT")
            all_completed = False

    end_time = cocotb.utils.get_sim_time('ns')
    total_duration = end_time - start_time

    if not all_completed:
        raise AssertionError("Stress test: Not all channels completed")

    # Verify all channels
    tb.log.info("\n=== Verifying all channel data ===")
    all_passed = True
    for channel in range(num_channels):
        channel_passed = True
        for idx, desc in enumerate(channel_descriptors[channel]):
            match = tb.verify_transfer(desc['src_addr'], desc['dst_addr'], desc['length'])
            if not match:
                tb.log.error(f"Channel {channel} Transfer {idx} FAILED")
                channel_passed = False
                all_passed = False

        if channel_passed:
            tb.log.info(f"Channel {channel} ALL PASSED")

    if not all_passed:
        raise AssertionError("Stress test: Data verification failed")

    # Performance summary
    tb.log.info(f"\n=== Stress Test Performance ===")
    tb.log.info(f"Total time: {total_duration:.0f}ns ({total_duration/1000:.1f}us)")
    tb.log.info(f"Total beats: {total_beats}")
    throughput = total_beats / total_duration
    tb.log.info(f"Aggregate throughput: {throughput:.4f} beats/ns")

    tb.log.info("\n=== Stress Test - All 8 Channels PASSED ===")


# ==============================================================================
# CocoTB Test 5: Register Access Validation
# ==============================================================================

@cocotb.test(timeout_time=1000, timeout_unit="us")
async def cocotb_test_register_access(dut):
    """
    Comprehensive APB register read/write validation.

    This tests:
    - VERSION register (read-only)
    - GLOBAL_CTRL/STATUS registers
    - CHANNEL_ENABLE register
    - CHANNEL_IDLE status
    - AXI_XFER_CONFIG register
    - DESCENG_ADDR registers

    Scales with TEST_LEVEL:
    - basic:  3 test patterns per register
    - medium: 6 test patterns per register
    - full:   9 test patterns per register
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['registers']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    test_patterns = test_config['test_patterns']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Register Access Validation Test (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Test patterns: {[hex(p) for p in test_patterns]}")

    all_passed = True

    # Test 1: VERSION register (read-only, hardcoded value)
    tb.log.info("\n--- Test 1: VERSION Register ---")
    version = await tb.read_apb_register(StreamRegisterMap.VERSION)
    # VERSION format: [31:16]=MINOR, [15:0]=MAJOR (0x0008005A = version 0.8.90)
    tb.log.info(f"VERSION: 0x{version:08X}")
    major = version & 0xFFFF
    minor = (version >> 16) & 0xFFFF
    tb.log.info(f"  Major: {major}, Minor: {minor}")
    if version == 0:
        tb.log.error("VERSION register returned 0 - readback path broken!")
        all_passed = False
    else:
        tb.log.info("VERSION register PASS")

    # Test 2: GLOBAL_CTRL register (read/write)
    tb.log.info("\n--- Test 2: GLOBAL_CTRL Register ---")
    # Write 0
    await tb.write_apb_register(StreamRegisterMap.GLOBAL_CTRL, 0x0)
    readback = await tb.read_apb_register(StreamRegisterMap.GLOBAL_CTRL)
    if readback != 0:
        tb.log.error(f"GLOBAL_CTRL: wrote 0x0, read 0x{readback:08X}")
        all_passed = False
    else:
        tb.log.info("GLOBAL_CTRL write 0x0: PASS")

    # Write 1
    await tb.write_apb_register(StreamRegisterMap.GLOBAL_CTRL, 0x1)
    readback = await tb.read_apb_register(StreamRegisterMap.GLOBAL_CTRL)
    if readback != 1:
        tb.log.error(f"GLOBAL_CTRL: wrote 0x1, read 0x{readback:08X}")
        all_passed = False
    else:
        tb.log.info("GLOBAL_CTRL write 0x1: PASS")

    # Test 3: CHANNEL_ENABLE register (read/write, 8 bits)
    tb.log.info("\n--- Test 3: CHANNEL_ENABLE Register ---")
    for pattern in test_patterns:
        await tb.write_apb_register(StreamRegisterMap.CHANNEL_ENABLE, pattern)
        readback = await tb.read_apb_register(StreamRegisterMap.CHANNEL_ENABLE)
        if readback != pattern:
            tb.log.error(f"CHANNEL_ENABLE: wrote 0x{pattern:02X}, read 0x{readback:02X}")
            all_passed = False
        else:
            tb.log.info(f"CHANNEL_ENABLE write 0x{pattern:02X}: PASS")

    # Restore to all enabled
    await tb.write_apb_register(StreamRegisterMap.CHANNEL_ENABLE, 0xFF)

    # Test 4: CHANNEL_IDLE status (read-only)
    tb.log.info("\n--- Test 4: CHANNEL_IDLE Status ---")
    idle_status = await tb.read_apb_register(StreamRegisterMap.CHANNEL_IDLE)
    tb.log.info(f"CHANNEL_IDLE: 0x{idle_status:02X} (binary: {idle_status:08b})")
    # All channels should be idle since we haven't started any transfers
    if idle_status != 0xFF:
        tb.log.warning(f"Expected all channels idle (0xFF), got 0x{idle_status:02X}")
    else:
        tb.log.info("All channels idle: PASS")

    # Test 5: AXI_XFER_CONFIG register
    tb.log.info("\n--- Test 5: AXI_XFER_CONFIG Register ---")
    test_values = [0x1010, 0x0808, 0xFF00, 0x00FF]
    for value in test_values:
        await tb.write_apb_register(StreamRegisterMap.AXI_XFER_CONFIG, value)
        readback = await tb.read_apb_register(StreamRegisterMap.AXI_XFER_CONFIG)
        if readback != value:
            tb.log.error(f"AXI_XFER_CONFIG: wrote 0x{value:04X}, read 0x{readback:04X}")
            all_passed = False
        else:
            rd_beats = value & 0xFF
            wr_beats = (value >> 8) & 0xFF
            tb.log.info(f"AXI_XFER_CONFIG 0x{value:04X} (RD={rd_beats}, WR={wr_beats}): PASS")

    # Restore default
    await tb.write_apb_register(StreamRegisterMap.AXI_XFER_CONFIG, 0x1010)

    # Test 6: DESCENG address range registers
    tb.log.info("\n--- Test 6: DESCENG Address Registers ---")
    test_base = 0x00010000
    test_limit = 0x0001FFFF

    await tb.write_apb_register(StreamRegisterMap.DESCENG_ADDR0_BASE, test_base)
    await tb.write_apb_register(StreamRegisterMap.DESCENG_ADDR0_LIMIT, test_limit)

    base_readback = await tb.read_apb_register(StreamRegisterMap.DESCENG_ADDR0_BASE)
    limit_readback = await tb.read_apb_register(StreamRegisterMap.DESCENG_ADDR0_LIMIT)

    if base_readback != test_base:
        tb.log.error(f"DESCENG_ADDR0_BASE: wrote 0x{test_base:08X}, read 0x{base_readback:08X}")
        all_passed = False
    else:
        tb.log.info(f"DESCENG_ADDR0_BASE: PASS")

    if limit_readback != test_limit:
        tb.log.error(f"DESCENG_ADDR0_LIMIT: wrote 0x{test_limit:08X}, read 0x{limit_readback:08X}")
        all_passed = False
    else:
        tb.log.info(f"DESCENG_ADDR0_LIMIT: PASS")

    # Summary
    tb.log.info(f"\n{'='*80}")
    if all_passed:
        tb.log.info("=== Register Access Validation PASSED ===")
    else:
        tb.log.error("=== Register Access Validation FAILED ===")
        raise AssertionError("Register access validation failed")


# ==============================================================================
# CocoTB Test 6: Back-to-Back Transfers
# ==============================================================================

@cocotb.test(timeout_time=5000, timeout_unit="us")
async def cocotb_test_back_to_back_transfers(dut):
    """
    Test multiple sequential transfers on same channel.

    This tests:
    - Channel re-use after completion
    - State machine reset between transfers
    - No resource leaks

    Scales with TEST_LEVEL:
    - basic:  3 iterations, 16 beats each
    - medium: 5 iterations, 32 beats each
    - full:   10 iterations, 64 beats each
    """
    tb = await setup_stream_testbench(dut)

    # Get level-based configuration
    level_config = get_test_level_config()
    test_config = level_config['back_to_back']
    test_level = os.environ.get('TEST_LEVEL', 'basic')

    channel = 0  # Always use channel 0 for this test
    num_iterations = test_config['iterations']
    transfer_size = test_config['transfer_size']

    tb.log.info(f"\n{'='*80}")
    tb.log.info(f"Back-to-Back Transfers Test (TEST_LEVEL={test_level})")
    tb.log.info(f"{'='*80}")
    tb.log.info(f"Channel: {channel}, Iterations: {num_iterations}, Transfer size: {transfer_size}")

    all_passed = True

    for iteration in range(num_iterations):
        tb.log.info(f"\n--- Iteration {iteration + 1}/{num_iterations} ---")

        # Unique addresses for each iteration to avoid memory overlap
        desc_addr = tb.desc_mem_base + (iteration * 0x1000)
        src_addr = tb.src_mem_base + (iteration * 0x100000)
        dst_addr = tb.dst_mem_base + (iteration * 0x100000)

        # Write unique test pattern for this iteration
        for beat in range(transfer_size):
            beat_addr = src_addr + (beat * tb.data_bytes)
            pattern = ((iteration << 4) | (beat & 0xF)) & 0xFF
            data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
            tb.write_source_data(beat_addr, data, tb.data_bytes)

        # Write descriptor
        tb.write_descriptor(
            addr=desc_addr,
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=transfer_size,
            next_ptr=0,
            priority=0,
            last=True,
            interrupt=True
        )

        # Kick off and wait
        await tb.kick_off_channel(channel, desc_addr)
        success = await tb.wait_for_channel_idle(channel, timeout_us=300)

        if not success:
            tb.log.error(f"Iteration {iteration + 1} TIMEOUT")
            all_passed = False
            continue

        # Verify
        match = tb.verify_transfer(src_addr, dst_addr, transfer_size)
        if not match:
            tb.log.error(f"Iteration {iteration + 1} DATA MISMATCH")
            all_passed = False
        else:
            stats = tb.get_performance_stats(channel)
            tb.log.info(f"Iteration {iteration + 1} PASSED ({stats['duration_ns']:.0f}ns)")

        # Small delay between iterations
        from cocotb.triggers import RisingEdge
        for _ in range(10):
            await RisingEdge(tb.clk)

    if not all_passed:
        raise AssertionError("Back-to-back transfers test failed")

    tb.log.info("\n=== Back-to-Back Transfers Test PASSED ===")


# ==============================================================================
# Pytest Wrapper Helper
# ==============================================================================

def create_pytest_wrapper(test_name, cocotb_testcase, default_params=None):
    """Create a pytest wrapper for a cocotb test."""

    if default_params is None:
        default_params = {}

    def test_func(request):
        module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
            'rtl_stream_top': '../../../../rtl/stream_top',
        })

        dut_name = "stream_top_ch8"

        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='projects/components/stream/rtl/filelists/top/stream_top_ch8.f'
        )

        rtl_parameters = {
            'NUM_CHANNELS': 8,
            'DATA_WIDTH': 512,
            'ADDR_WIDTH': 64,
            'SRAM_DEPTH': 4096,
            'APB_ADDR_WIDTH': 12,
            'APB_DATA_WIDTH': 32,
            'USE_AXI_MONITORS': 0,
            'CDC_ENABLE': 0,
        }

        # Get test level from environment (default: basic)
        test_level = os.environ.get('TEST_LEVEL', 'basic')
        test_name_plus_params = f"test_{dut_name}_{test_name}_{test_level}"

        worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
        if worker_id:
            test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

        log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
        results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
        sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
        os.makedirs(sim_build, exist_ok=True)
        os.makedirs(log_dir, exist_ok=True)

        extra_env = {
            'NUM_CHANNELS': '8',
            'DATA_WIDTH': '512',
            'FIFO_DEPTH': '4096',
            'AXI_ID_WIDTH': '8',
            'APB_ADDR_WIDTH': '12',
            'APB_DATA_WIDTH': '32',
            'TEST_LEVEL': test_level,  # Pass test level to cocotb
            'DUT': dut_name,
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': results_path,
        }

        # Add test-specific parameters (can override TEST_LEVEL defaults)
        for key, value in default_params.items():
            extra_env[key] = str(value)

        enable_waves = bool(int(os.environ.get('WAVES', '0')))
        if enable_waves:
            extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
            compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wno-fatal", "--timescale", "1ns/1ps"]
            sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
        else:
            compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps"]
            sim_args = []

        compile_args.extend([
            "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
            "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN", "-Wno-MULTIDRIVEN",
        ])

        create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

        from cocotb_test.simulator import run

        try:
            run(
                python_search=[tests_dir],
                verilog_sources=verilog_sources,
                includes=includes,
                toplevel=dut_name,
                module=module,
                testcase=cocotb_testcase,
                parameters=rtl_parameters,
                compile_args=compile_args,
                sim_args=sim_args,
                extra_env=extra_env,
                sim_build=sim_build,
                waves=False,
                keep_files=True,
                simulator='verilator',
            )
            print(f"PASS: {test_name}")
        except Exception as e:
            print(f"FAIL: {test_name}: {str(e)}")
            raise

    return test_func


# ==============================================================================
# Pytest Wrappers
# ==============================================================================

# Test 1: Multi-Channel Concurrent
# Tests: Channel arbitration, resource sharing, concurrent data integrity
# Scales: basic=2ch, medium=4ch, full=8ch
test_stream_top_multi_channel = create_pytest_wrapper(
    'multi_channel_concurrent',
    'cocotb_test_multi_channel_concurrent'
)

# Test 2: Long Descriptor Chain
# Tests: Descriptor chain following, next pointer handling
# Scales: basic=4 desc, medium=8 desc, full=16 desc
test_stream_top_long_chain = create_pytest_wrapper(
    'long_descriptor_chain',
    'cocotb_test_long_descriptor_chain'
)

# Test 3: Variable Transfer Sizes
# Tests: Edge cases (1 beat, boundary-1, boundary+1, max)
# Scales: basic=3 sizes, medium=6 sizes, full=16 sizes
test_stream_top_variable_sizes = create_pytest_wrapper(
    'variable_transfer_sizes',
    'cocotb_test_variable_transfer_sizes'
)

# Test 4: Stress Test - Multiple Channels
# Tests: Maximum resource contention, throughput under load
# Scales: basic=4ch, medium=6ch, full=8ch
test_stream_top_stress = create_pytest_wrapper(
    'stress_all_channels',
    'cocotb_test_stress_all_channels'
)

# Test 5: Register Access Validation
# Tests: APB register read/write for all registers
# Scales: basic=3 patterns, medium=6 patterns, full=9 patterns
test_stream_top_registers = create_pytest_wrapper(
    'register_access',
    'cocotb_test_register_access'
)

# Test 6: Back-to-Back Transfers
# Tests: Channel re-use, state machine reset, resource leaks
# Scales: basic=3 iter, medium=5 iter, full=10 iter
test_stream_top_back_to_back = create_pytest_wrapper(
    'back_to_back_transfers',
    'cocotb_test_back_to_back_transfers'
)


# ==============================================================================
# Main Entry Point
# ==============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v"])
