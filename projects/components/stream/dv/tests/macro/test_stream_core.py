"""
================================================================================
Stream Core Integration Test
================================================================================

Test suite for stream_core - complete STREAM DMA engine integration.

Tests the full integration of:
- scheduler_group_array (task scheduling)
- axi_read_engine (AXI master read)
- axi_write_engine (AXI master write)
- sram_controller (internal buffering)
- perf_profiler (performance monitoring)
- axi4_master_rd/wr (skid buffers)

Test Levels:
- basic: Quick smoke test (1-2 descriptors per channel, ~30s)
- medium: Moderate coverage (4-8 descriptors, ~90s)
- full: Comprehensive validation (16+ descriptors, ~180s)

Author: RTL Design Sherpa
Date: 2025-11-08
"""

import os
import sys
import pytest
import cocotb
import random
from pathlib import Path

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

# Coverage integration - optional import
try:
    from projects.components.stream.dv.stream_coverage import CoverageHelper
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False


def get_coverage_helper(test_name: str, log=None):
    """Get coverage helper if coverage is enabled."""
    if not COVERAGE_AVAILABLE:
        return None
    if os.environ.get('COVERAGE', '0') != '1':
        return None
    return CoverageHelper(test_name, log=log)


# ==============================================================================
# Test Parameters
# ==============================================================================

def generate_test_params():
    """Generate test parameter sets based on TEST_LEVEL (gate/func/full/burst)"""
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    # Test levels: gate (quick), func (functional), full (comprehensive), burst (burst matrix)
    level_configs = {
        'gate': {
            'desc_count': 2,      # 2 descriptors per channel
            'channels': [0],      # Single channel
            'transfer_sizes': [64],  # Single transfer size
            'timing_profile': 'fast',  # Fast/no-stress timing
        },
        'func': {
            'desc_count': 4,      # 4 descriptors per channel
            'channels': [0, 1],   # 2 channels
            'transfer_sizes': [64, 128],
            'timing_profile': 'fast',  # Still fast for quicker regression
        },
        'full': {
            'desc_count': 16,     # 16 descriptors per channel
            'channels': [0, 1, 2, 3],  # All channels
            'transfer_sizes': [64, 128, 256, 512],
            'timing_profile': 'mixed',  # Mix of fast, normal, constrained
        },
        'burst': {
            'desc_count': 6,      # 6 descriptors per channel (4-8 range for machinery churn)
            'channels': [0, 1],   # 2 channels for multi-channel stress
            'transfer_sizes': [256, 384, 512, 768],  # 8-96 bursts per descriptor (24 avg for 16-beat bursts)
            'timing_profile': 'fast',  # Fast/no-stress for debugging
        }
    }

    config = level_configs.get(test_level, level_configs['gate'])

    # Generate parameter sets
    params = []

    # Data width configurations: 128, 256, 512-bit (production widths)
    data_widths = [128, 256, 512]

    # Realistic SRAM sizing: Power-of-2 scaled depths
    # Based on testing: 128-bit works well with 4KB, but 512-bit needs 8KB minimum
    # See REALISTIC_SRAM_ANALYSIS.md for details
    fifo_depths = {
        128: 256,  # 4KB = 4096 / 16 bytes/entry (optimal from testing)
        256: 256,  # 8KB = 8192 / 32 bytes/entry (safe, power-of-2)
        512: 128,  # 8KB = 8192 / 64 bytes/entry (minimum for safe concurrent ops)
    }

    # Burst matrix test level - comprehensive burst size and segment size combinations
    # Design rule: Minimum SRAM per segment = MAX(2KB, 2 × single_burst_size)
    if test_level == 'burst':
        # 128-bit: 3 rd × 3 wr × 1 segment = 9 tests
        for rd_burst in [8, 16, 32]:
            for wr_burst in [8, 16, 32]:
                params.append({
                    'num_channels': 4,
                    'data_width': 128,
                    'fifo_depth': 128,  # 2KB segment (2048 / 16 bytes = 128 entries)
                    'axi_id_width': 8,
                    'desc_count': config['desc_count'],
                    'test_channels': config['channels'],
                    'transfer_sizes': config['transfer_sizes'],
                    'timing_profile': config['timing_profile'],
                    'rd_xfer_beats': rd_burst,
                    'wr_xfer_beats': wr_burst,
                    'scenario': f'burst_rd{rd_burst}_wr{wr_burst}_2KB',
                })

        # 256-bit: 2 rd × 2 wr × 2 segments = 8 tests
        for rd_burst in [8, 16]:
            for wr_burst in [8, 16]:
                for segment_kb, fifo_depth in [(2, 64), (4, 128)]:
                    params.append({
                        'num_channels': 4,
                        'data_width': 256,
                        'fifo_depth': fifo_depth,  # 2KB=64 or 4KB=128 entries
                        'axi_id_width': 8,
                        'desc_count': config['desc_count'],
                        'test_channels': config['channels'],
                        'transfer_sizes': config['transfer_sizes'],
                        'timing_profile': config['timing_profile'],
                        'rd_xfer_beats': rd_burst,
                        'wr_xfer_beats': wr_burst,
                        'scenario': f'burst_rd{rd_burst}_wr{wr_burst}_{segment_kb}KB',
                    })

        # 512-bit: 2 rd × 2 wr × 2 segments = 8 tests
        for rd_burst in [8, 16]:
            for wr_burst in [8, 16]:
                for segment_kb, fifo_depth in [(2, 32), (4, 64)]:
                    params.append({
                        'num_channels': 4,
                        'data_width': 512,
                        'fifo_depth': fifo_depth,  # 2KB=32 or 4KB=64 entries
                        'axi_id_width': 8,
                        'desc_count': config['desc_count'],
                        'test_channels': config['channels'],
                        'transfer_sizes': config['transfer_sizes'],
                        'timing_profile': config['timing_profile'],
                        'rd_xfer_beats': rd_burst,
                        'wr_xfer_beats': wr_burst,
                        'scenario': f'burst_rd{rd_burst}_wr{wr_burst}_{segment_kb}KB',
                    })

        return params

    # For full level, generate multiple scenarios with varied chain lengths
    if test_level == 'full':
        for dw in data_widths:
            # Scenario 1: Short chains (2-3 descriptors) - tests rapid completion
            params.append({
                'num_channels': 4,
                'data_width': dw,
                'fifo_depth': fifo_depths[dw],  # Scaled SRAM depth
                'axi_id_width': 8,
                'desc_count': 3,  # Short chains
                'test_channels': config['channels'],
                'transfer_sizes': [64, 128],
                'timing_profile': config['timing_profile'],
                'scenario': 'short_chains',
            })

            # Scenario 2: Medium chains (8-10 descriptors) - balanced
            params.append({
                'num_channels': 4,
                'data_width': dw,
                'fifo_depth': fifo_depths[dw],  # Scaled SRAM depth
                'axi_id_width': 8,
                'desc_count': 10,  # Medium chains
                'test_channels': config['channels'],
                'transfer_sizes': [128, 256],
                'timing_profile': config['timing_profile'],
                'scenario': 'medium_chains',
            })

            # Scenario 3: Long chains (full descriptor count) - endurance
            params.append({
                'num_channels': 4,
                'data_width': dw,
                'fifo_depth': fifo_depths[dw],  # Scaled SRAM depth
                'axi_id_width': 8,
                'desc_count': config['desc_count'],  # Full length
                'test_channels': config['channels'],
                'transfer_sizes': config['transfer_sizes'],
                'timing_profile': config['timing_profile'],
                'scenario': 'long_chains',
            })
    else:
        # For gate/func: single configuration per data width
        for dw in data_widths:
            params.append({
                'num_channels': 4,
                'data_width': dw,
                'fifo_depth': fifo_depths[dw],  # Scaled SRAM depth
                'axi_id_width': 8,
                'desc_count': config['desc_count'],
                'test_channels': config['channels'],
                'transfer_sizes': config['transfer_sizes'],
                'timing_profile': config['timing_profile'],
                'scenario': 'standard',
            })

    return params


# ==============================================================================
# CocoTB Test Functions
# ==============================================================================

@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_single_channel_transfer(dut):
    """Test basic single-channel DMA transfer following datapath pattern"""

    # Get test parameters from environment
    num_channels = int(os.environ.get('NUM_CHANNELS', '4'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    axi_id_width = int(os.environ.get('AXI_ID_WIDTH', '8'))
    # Support separate read/write burst sizes (default to unified if not specified)
    xfer_beats = int(os.environ.get('XFER_BEATS', '16'))
    rd_xfer_beats = int(os.environ.get('RD_XFER_BEATS', str(xfer_beats)))
    wr_xfer_beats = int(os.environ.get('WR_XFER_BEATS', str(xfer_beats)))
    desc_count = int(os.environ.get('DESC_COUNT', '2'))

    # Initialize testbench
    tb = StreamCoreTB(
        dut=dut,
        num_channels=num_channels,
        addr_width=64,
        data_width=data_width,
        axi_id_width=axi_id_width,
        fifo_depth=fifo_depth
    )

    # Initialize coverage if enabled
    test_name = f"test_stream_core_single_nc{num_channels:02d}_dw{data_width:04d}"
    coverage = get_coverage_helper(test_name, log=tb.log)

    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)
    tb.log.info(f"=== Single Channel Transfer Test ===")
    tb.log.info(f"Channels: {num_channels}, Data Width: {data_width}, "
               f"RdBurst: {rd_xfer_beats}, WrBurst: {wr_xfer_beats}, Descriptors: {desc_count}")

    # Test channel 0 only
    channel = 0
    transfer_beats = 64  # 64 beats per descriptor

    # Step 1: Create descriptor chain in descriptor memory
    tb.log.info(f"Step 1: Creating descriptor chain ({desc_count} descriptors)")
    for desc_idx in range(desc_count):
        # Allocate memory regions (64-byte aligned descriptors)
        desc_addr = tb.desc_mem_base + (desc_idx * 64)
        src_addr = tb.src_mem_base + (desc_idx * transfer_beats * tb.data_bytes)
        dst_addr = tb.dst_mem_base + (desc_idx * transfer_beats * tb.data_bytes)

        # Fill source memory with test pattern
        # Use global beat index so each descriptor has unique data
        for beat in range(transfer_beats):
            beat_addr = src_addr + (beat * tb.data_bytes)
            global_beat_idx = (desc_idx * transfer_beats) + beat  # Unique across all descriptors
            data = tb.create_test_pattern(global_beat_idx, pattern_type='increment')
            tb.write_source_data(beat_addr, data, tb.data_bytes)

        # Write descriptor to descriptor memory
        is_last = (desc_idx == desc_count - 1)
        next_ptr = 0 if is_last else (desc_addr + 64)

        tb.write_descriptor(
            addr=desc_addr,
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=transfer_beats,
            next_ptr=next_ptr,
            priority=0,
            last=is_last,
            channel_id=channel
        )

    # Step 2: Kick off channel via APB
    first_desc = tb.desc_mem_base
    tb.log.info(f"Step 2: Kicking off channel {channel} @ descriptor 0x{first_desc:08x}")
    await tb.kick_off_channel(channel, first_desc)

    # Step 3: Wait for completion
    tb.log.info(f"Step 3: Waiting for transfer completion")
    success = await tb.wait_for_channel_idle(channel, timeout_us=10000)
    assert success, f"Channel {channel} timeout"

    # Step 4: Verify all transfers
    tb.log.info(f"Step 4: Verifying data integrity")
    for desc_idx in range(desc_count):
        src_addr = tb.src_mem_base + (desc_idx * transfer_beats * tb.data_bytes)
        dst_addr = tb.dst_mem_base + (desc_idx * transfer_beats * tb.data_bytes)

        match = tb.verify_transfer(src_addr, dst_addr, transfer_beats)
        assert match, f"Data mismatch for descriptor {desc_idx}"
        tb.log.info(f"Descriptor {desc_idx} verified: {transfer_beats} beats OK")

    # Performance stats
    stats = tb.get_performance_stats(channel)
    if stats:
        tb.log.info(f"Transfer completed in {stats['duration_us']:.2f} us")

    # Print transaction summary for debugging
    tb.print_transaction_summary(channel=channel)

    # Sample coverage if enabled
    if coverage:
        # Sample AXI transactions (INCR burst type = 1, STREAM uses 64-byte bursts)
        burst_size = data_width // 8  # Convert data width to bytes
        for _ in range(desc_count):
            # Each descriptor generates read and write transactions
            coverage.sample_axi_read(
                burst_type=1,        # INCR
                burst_size=burst_size,
                burst_len=rd_xfer_beats,
                response=0           # OKAY
            )
            coverage.sample_axi_write(
                burst_type=1,        # INCR
                burst_size=burst_size,
                burst_len=wr_xfer_beats,
                response=0           # OKAY
            )

        # Sample functional scenarios
        coverage.sample_scenario("basic_transfer")
        if desc_count > 1:
            coverage.sample_scenario("descriptor_chain")

        # Sample handshakes
        coverage.sample_handshake("read_request")
        coverage.sample_handshake("read_response")
        coverage.sample_handshake("write_request")
        coverage.sample_handshake("write_response")

        # Save coverage
        coverage.save()
        tb.log.info(f"Coverage saved for {test_name}")

    tb.log.info("=== Test PASSED ===")


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_multi_channel_concurrent(dut):
    """Test concurrent multi-channel DMA transfers"""

    # Get test parameters
    num_channels = int(os.environ.get('NUM_CHANNELS', '4'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    axi_id_width = int(os.environ.get('AXI_ID_WIDTH', '8'))
    # Support separate read/write burst sizes (default to unified if not specified)
    xfer_beats = int(os.environ.get('XFER_BEATS', '16'))
    rd_xfer_beats = int(os.environ.get('RD_XFER_BEATS', str(xfer_beats)))
    wr_xfer_beats = int(os.environ.get('WR_XFER_BEATS', str(xfer_beats)))
    desc_count = int(os.environ.get('DESC_COUNT', '2'))
    test_channels_str = os.environ.get('TEST_CHANNELS', '0,1')
    test_channels = [int(x) for x in test_channels_str.split(',')]

    # Initialize testbench
    tb = StreamCoreTB(
        dut=dut,
        num_channels=num_channels,
        addr_width=64,
        data_width=data_width,
        axi_id_width=axi_id_width,
        fifo_depth=fifo_depth
    )

    # Initialize coverage if enabled
    test_name = f"test_stream_core_multi_nc{num_channels:02d}_dw{data_width:04d}_nch{len(test_channels):02d}"
    coverage = get_coverage_helper(test_name, log=tb.log)

    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)
    cocotb.log.info(f"=== Multi-Channel Concurrent Test ===")
    cocotb.log.info(f"Testing channels: {test_channels}, RdBurst: {rd_xfer_beats}, WrBurst: {wr_xfer_beats}, Descriptors/channel: {desc_count}")

    transfer_beats = 128  # 128 beats per transfer

    # Setup descriptors for all channels
    first_desc_addrs = {}

    for channel in test_channels:
        # Allocate descriptor chain for this channel
        channel_desc_base = tb.desc_mem_base + (channel * 0x1000)  # 4KB per channel
        first_desc_addrs[channel] = channel_desc_base

        for desc_idx in range(desc_count):
            desc_addr = channel_desc_base + (desc_idx * 64)

            # Allocate memory regions (separate per channel)
            src_addr = tb.src_mem_base + (channel * 0x100000) + (desc_idx * transfer_beats * (data_width // 8))
            dst_addr = tb.dst_mem_base + (channel * 0x100000) + (desc_idx * transfer_beats * (data_width // 8))

            # Create test pattern (channel-specific, unique per descriptor)
            for beat in range(transfer_beats):
                beat_addr = src_addr + (beat * (data_width // 8))
                # Pattern: channel + descriptor offset in upper bits, beat in lower bits
                # Use global beat index to ensure each descriptor has unique data
                global_beat_idx = (desc_idx * transfer_beats) + beat
                pattern = ((channel << 4) | (global_beat_idx & 0xFF)) & 0xFF
                # Use byte replication, not arithmetic multiply
                data = int.from_bytes(bytes([pattern] * (data_width // 8)), byteorder='little')
                tb.write_source_data(beat_addr, data, data_width // 8)

            # Write descriptor
            is_last = (desc_idx == desc_count - 1)
            next_ptr = 0 if is_last else (desc_addr + 64)

            tb.write_descriptor(
                addr=desc_addr,
                src_addr=src_addr,
                dst_addr=dst_addr,
                length=transfer_beats,
                next_ptr=next_ptr,
                priority=channel,  # Use channel as priority
                last=is_last
            )

        cocotb.log.info(f"Channel {channel}: {desc_count} descriptors @ 0x{channel_desc_base:08x}")

    # Kick off all channels concurrently
    for channel in test_channels:
        await tb.kick_off_channel(channel, first_desc_addrs[channel])
        cocotb.log.info(f"Kicked off channel {channel}")

    # Wait for all channels to complete
    for channel in test_channels:
        await tb.wait_for_channel_idle(channel, timeout_us=20000)
        cocotb.log.info(f"Channel {channel} completed")

    # Verify all transfers for all channels
    for channel in test_channels:
        for desc_idx in range(desc_count):
            src_addr = tb.src_mem_base + (channel * 0x100000) + (desc_idx * transfer_beats * (data_width // 8))
            dst_addr = tb.dst_mem_base + (channel * 0x100000) + (desc_idx * transfer_beats * (data_width // 8))

            match = tb.verify_transfer(src_addr, dst_addr, transfer_beats)
            assert match, f"Channel {channel} descriptor {desc_idx} data mismatch"

        cocotb.log.info(f"Channel {channel} verified OK")

    # Sample coverage if enabled
    if coverage:
        burst_size = data_width // 8
        total_transfers = len(test_channels) * desc_count

        # Sample AXI transactions for all channels
        for _ in range(total_transfers):
            coverage.sample_axi_read(
                burst_type=1,
                burst_size=burst_size,
                burst_len=rd_xfer_beats,
                response=0           # OKAY
            )
            coverage.sample_axi_write(
                burst_type=1,
                burst_size=burst_size,
                burst_len=wr_xfer_beats,
                response=0           # OKAY
            )

        # Sample scenarios - multi-channel specific
        coverage.sample_scenario("basic_transfer")
        coverage.sample_scenario("concurrent_rw")
        if desc_count > 1:
            coverage.sample_scenario("descriptor_chain")
        if len(test_channels) > 1:
            coverage.sample_scenario("full_pipeline")  # Multiple channels = full pipeline

        # Sample all handshakes
        coverage.sample_handshake("read_request")
        coverage.sample_handshake("read_response")
        coverage.sample_handshake("write_request")
        coverage.sample_handshake("write_response")

        # Save coverage
        coverage.save()
        cocotb.log.info(f"Coverage saved for {test_name}")

    cocotb.log.info("=== Test PASSED ===")


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_variable_sizes(dut):
    """Test transfers with variable sizes"""

    # Get test parameters
    num_channels = int(os.environ.get('NUM_CHANNELS', '4'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    axi_id_width = int(os.environ.get('AXI_ID_WIDTH', '8'))
    transfer_sizes_str = os.environ.get('TRANSFER_SIZES', '64,128,256')
    transfer_sizes = [int(x) for x in transfer_sizes_str.split(',')]

    # Initialize testbench
    tb = StreamCoreTB(
        dut=dut,
        num_channels=num_channels,
        addr_width=64,
        data_width=data_width,
        axi_id_width=axi_id_width,
        fifo_depth=fifo_depth
    )

    # Initialize coverage if enabled
    sizes_str = '_'.join(map(str, transfer_sizes[:3]))  # First 3 sizes for name
    test_name = f"test_stream_core_varsizes_dw{data_width:04d}_sz{sizes_str}"
    coverage = get_coverage_helper(test_name, log=tb.log)

    await tb.setup_clocks_and_reset()
    cocotb.log.info(f"=== Variable Size Transfer Test ===")
    cocotb.log.info(f"Transfer sizes: {transfer_sizes} beats")

    channel = 0
    desc_base = tb.desc_mem_base

    # Create descriptor chain with variable sizes
    for idx, transfer_beats in enumerate(transfer_sizes):
        desc_addr = desc_base + (idx * 64)
        src_addr = tb.src_mem_base + (idx * 0x10000)
        dst_addr = tb.dst_mem_base + (idx * 0x10000)

        # Create test pattern
        for beat in range(transfer_beats):
            beat_addr = src_addr + (beat * (data_width // 8))
            # Pattern includes transfer size info
            pattern = ((idx << 4) | (beat & 0xF)) & 0xFF
            # Use byte replication, not arithmetic multiply
            data = int.from_bytes(bytes([pattern] * (data_width // 8)), byteorder='little')
            tb.write_source_data(beat_addr, data, data_width // 8)

        # Write descriptor
        is_last = (idx == len(transfer_sizes) - 1)
        next_ptr = 0 if is_last else (desc_addr + 64)

        tb.write_descriptor(
            addr=desc_addr,
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=transfer_beats,
            next_ptr=next_ptr,
            priority=0,
            last=is_last
        )

        cocotb.log.info(f"Descriptor {idx}: {transfer_beats} beats")

    # Kick off and wait
    await tb.kick_off_channel(channel, desc_base)
    await tb.wait_for_channel_idle(channel, timeout_us=30000)

    # Verify all transfers
    for idx, transfer_beats in enumerate(transfer_sizes):
        src_addr = tb.src_mem_base + (idx * 0x10000)
        dst_addr = tb.dst_mem_base + (idx * 0x10000)

        match = tb.verify_transfer(src_addr, dst_addr, transfer_beats)
        assert match, f"Transfer {idx} ({transfer_beats} beats) data mismatch"
        cocotb.log.info(f"Transfer {idx} ({transfer_beats} beats) verified OK")

    # Sample coverage if enabled
    if coverage:
        burst_size = data_width // 8

        # Sample AXI transactions for each transfer size
        for transfer_beats in transfer_sizes:
            coverage.sample_axi_read(
                burst_type=1,
                burst_size=burst_size,
                burst_len=transfer_beats,
                response=0           # OKAY
            )
            coverage.sample_axi_write(
                burst_type=1,
                burst_size=burst_size,
                burst_len=transfer_beats,
                response=0           # OKAY
            )

        # Sample scenarios
        coverage.sample_scenario("basic_transfer")
        coverage.sample_scenario("descriptor_chain")  # Multiple sizes = chained

        # Sample handshakes
        coverage.sample_handshake("read_request")
        coverage.sample_handshake("read_response")
        coverage.sample_handshake("write_request")
        coverage.sample_handshake("write_response")

        # Save coverage
        coverage.save()
        cocotb.log.info(f"Coverage saved for {test_name}")

    cocotb.log.info("=== Test PASSED ===")


# ==============================================================================
# Pytest Wrapper Functions
# ==============================================================================

@pytest.mark.parametrize("params", generate_test_params())
def test_stream_core_single_channel(request, params):
    """Pytest wrapper for single-channel transfer test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    # Get sources from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/stream_core.f'
    )

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': params['num_channels'],
        'DATA_WIDTH': params['data_width'],
        'FIFO_DEPTH': params['fifo_depth'],
        'AXI_ID_WIDTH': params['axi_id_width'],
        'ADDR_WIDTH': 64,
    }

    # Create unique test name with scenario and timing profile
    dut_name = "stream_core"
    nc_str = f"{params['num_channels']:02d}"
    dw_str = f"{params['data_width']:04d}"
    fd_str = f"{params['fifo_depth']:04d}"
    dc_str = f"{params['desc_count']:02d}"
    scenario = params.get('scenario', 'standard')
    timing = params.get('timing_profile', 'fast')
    test_name_plus_params = f"test_{dut_name}_single_nc{nc_str}_dw{dw_str}_fd{fd_str}_dc{dc_str}_{scenario}_{timing}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Create log paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Environment variables for test
    extra_env = {
        'NUM_CHANNELS': str(params['num_channels']),
        'DATA_WIDTH': str(params['data_width']),
        'FIFO_DEPTH': str(params['fifo_depth']),
        'AXI_ID_WIDTH': str(params['axi_id_width']),
        'DESC_COUNT': str(params['desc_count']),
        'TIMING_PROFILE': params.get('timing_profile', 'fast'),
        'TEST_SCENARIO': params.get('scenario', 'standard'),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
    }

    # Add burst size parameters if specified
    if 'rd_xfer_beats' in params:
        extra_env['RD_XFER_BEATS'] = str(params['rd_xfer_beats'])
    if 'wr_xfer_beats' in params:
        extra_env['WR_XFER_BEATS'] = str(params['wr_xfer_beats'])

    # WAVES support - conditionally enable VCD tracing
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    else:
        compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = []

    # Create view command
    from CocoTBFramework.tbclasses.shared.utilities import create_view_cmd
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Import here to avoid issues
    from cocotb_test.simulator import run

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_single_channel_transfer",
            parameters=rtl_parameters,
            compile_args=compile_args,
            sim_args=sim_args,
            extra_env=extra_env,
            sim_build=sim_build,
            waves=False,  # Explicitly disable auto-FST
            keep_files=True,
            simulator='verilator',
        )
        print(f"✓ Stream core single channel test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Stream core single channel test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


@pytest.mark.parametrize("params", generate_test_params())
def test_stream_core_multi_channel(request, params):
    """Pytest wrapper for multi-channel concurrent test"""

    # Skip if only testing single channel
    if len(params['test_channels']) < 2:
        pytest.skip("Multi-channel test requires at least 2 channels")

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/stream_core.f'
    )

    rtl_parameters = {
        'NUM_CHANNELS': params['num_channels'],
        'DATA_WIDTH': params['data_width'],
        'FIFO_DEPTH': params['fifo_depth'],
        'AXI_ID_WIDTH': params['axi_id_width'],
        'ADDR_WIDTH': 64,
    }

    # Create unique test name
    dut_name = "stream_core"
    nc_str = f"{params['num_channels']:02d}"
    dw_str = f"{params['data_width']:04d}"
    fd_str = f"{params['fifo_depth']:04d}"
    dc_str = f"{params['desc_count']:02d}"
    nch_str = f"{len(params['test_channels']):02d}"
    scenario = params.get('scenario', 'standard')
    timing = params.get('timing_profile', 'fast')
    test_name_plus_params = f"test_{dut_name}_multi_nc{nc_str}_dw{dw_str}_fd{fd_str}_dc{dc_str}_nch{nch_str}_{scenario}_{timing}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Create log paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Environment variables for test
    extra_env = {
        'NUM_CHANNELS': str(params['num_channels']),
        'DATA_WIDTH': str(params['data_width']),
        'FIFO_DEPTH': str(params['fifo_depth']),
        'AXI_ID_WIDTH': str(params['axi_id_width']),
        'DESC_COUNT': str(params['desc_count']),
        'TEST_CHANNELS': ','.join(map(str, params['test_channels'])),
        'TIMING_PROFILE': params.get('timing_profile', 'fast'),
        'TEST_SCENARIO': params.get('scenario', 'standard'),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
    }

    # WAVES support - conditionally enable VCD tracing
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    else:
        compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = []

    # Create view command
    from CocoTBFramework.tbclasses.shared.utilities import create_view_cmd
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    from cocotb_test.simulator import run

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_multi_channel_concurrent",
            parameters=rtl_parameters,
            compile_args=compile_args,
            sim_args=sim_args,
            extra_env=extra_env,
            sim_build=sim_build,
            waves=False,  # Explicitly disable auto-FST
            keep_files=True,
            simulator='verilator',
        )
        print(f"✓ Stream core multi-channel test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Stream core multi-channel test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


@pytest.mark.parametrize("params", generate_test_params())
def test_stream_core_variable_sizes(request, params):
    """Pytest wrapper for variable size transfer test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/stream_core.f'
    )

    rtl_parameters = {
        'NUM_CHANNELS': params['num_channels'],
        'DATA_WIDTH': params['data_width'],
        'FIFO_DEPTH': params['fifo_depth'],
        'AXI_ID_WIDTH': params['axi_id_width'],
        'ADDR_WIDTH': 64,
    }

    # Create unique test name
    dut_name = "stream_core"
    nc_str = f"{params['num_channels']:02d}"
    dw_str = f"{params['data_width']:04d}"
    fd_str = f"{params['fifo_depth']:04d}"
    sizes_str = '_'.join(map(str, params['transfer_sizes']))
    scenario = params.get('scenario', 'standard')
    timing = params.get('timing_profile', 'fast')
    test_name_plus_params = f"test_{dut_name}_varsizes_nc{nc_str}_dw{dw_str}_fd{fd_str}_sz{sizes_str}_{scenario}_{timing}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Create log paths
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Environment variables for test
    extra_env = {
        'NUM_CHANNELS': str(params['num_channels']),
        'DATA_WIDTH': str(params['data_width']),
        'FIFO_DEPTH': str(params['fifo_depth']),
        'AXI_ID_WIDTH': str(params['axi_id_width']),
        'TRANSFER_SIZES': ','.join(map(str, params['transfer_sizes'])),
        'TIMING_PROFILE': params.get('timing_profile', 'fast'),
        'TEST_SCENARIO': params.get('scenario', 'standard'),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
    }

    # WAVES support - conditionally enable VCD tracing
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    else:
        compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = []

    # Create view command
    from CocoTBFramework.tbclasses.shared.utilities import create_view_cmd
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    from cocotb_test.simulator import run

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_variable_sizes",
            parameters=rtl_parameters,
            compile_args=compile_args,
            sim_args=sim_args,
            extra_env=extra_env,
            sim_build=sim_build,
            waves=False,  # Explicitly disable auto-FST
            keep_files=True,
            simulator='verilator',
        )
        print(f"✓ Stream core variable sizes test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Stream core variable sizes test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
