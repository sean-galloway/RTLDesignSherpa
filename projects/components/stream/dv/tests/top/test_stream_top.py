"""
================================================================================
Stream Top Integration Test
================================================================================

Test suite for stream_top_ch8 - complete STREAM DMA with APB configuration.

Tests the full integration of:
- APB4 configuration interface
- peakrdl_to_cmdrsp (APB to CMD/RSP conversion)
- apbtodescr (channel kick-off router)
- stream_config_block (register mapping)
- stream_core (complete datapath)

This test validates:
- APB configuration register access (when PeakRDL regs available)
- APB channel kick-off mechanism
- Complete DMA transfers via APB-initiated operations
- Multi-channel concurrent operation

Test Levels:
- gate: Quick smoke test (1-2 descriptors, single channel, ~30s)
- func: Functional coverage (4 descriptors, 2 channels, ~90s)
- full: Comprehensive validation (8+ descriptors, 4 channels, ~180s)

Author: RTL Design Sherpa
Date: 2025-11-25
"""

import os
import sys
import pytest
import cocotb

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
# Test Parameters
# ==============================================================================

def generate_test_params():
    """Generate test parameter sets based on TEST_LEVEL"""
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    # Test level configurations
    level_configs = {
        'gate': {
            'desc_count': 2,
            'channels': [0],
            'transfer_sizes': [64],
            'timing_profile': 'fast',
        },
        'func': {
            'desc_count': 4,
            'channels': [0, 1],
            'transfer_sizes': [64, 128],
            'timing_profile': 'fast',
        },
        'full': {
            'desc_count': 8,
            'channels': [0, 1, 2, 3],
            'transfer_sizes': [64, 128, 256],
            'timing_profile': 'mixed',
        }
    }

    config = level_configs.get(test_level, level_configs['gate'])

    # Generate parameter sets
    params = []

    # Start with single configuration - 512-bit, 8 channels (stream_top default)
    data_width = 512
    params.append({
        'num_channels': 8,  # stream_top_ch8 has 8 channels
        'data_width': data_width,
        'fifo_depth': 4096,  # stream_top default (larger than stream_core)
        'axi_id_width': 8,
        'apb_addr_width': 12,
        'apb_data_width': 32,
        'desc_count': config['desc_count'],
        'test_channels': config['channels'],
        'transfer_sizes': config['transfer_sizes'],
        'timing_profile': config['timing_profile'],
        'scenario': 'apb_config',
    })

    return params


# ==============================================================================
# CocoTB Test Functions
# ==============================================================================

@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_stream_top_basic(dut):
    """Test basic stream_top operation with APB configuration"""

    # Get test parameters from environment
    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '4096'))
    axi_id_width = int(os.environ.get('AXI_ID_WIDTH', '8'))
    apb_addr_width = int(os.environ.get('APB_ADDR_WIDTH', '12'))
    apb_data_width = int(os.environ.get('APB_DATA_WIDTH', '32'))
    rd_xfer_beats = int(os.environ.get('RD_XFER_BEATS', '16'))
    wr_xfer_beats = int(os.environ.get('WR_XFER_BEATS', '16'))
    desc_count = int(os.environ.get('DESC_COUNT', '2'))

    # Get transfer sizes from environment (comma-separated)
    transfer_sizes_str = os.environ.get('TRANSFER_SIZES', '64')
    transfer_sizes = [int(x) for x in transfer_sizes_str.split(',')]

    # Get test channels from environment (comma-separated)
    test_channels_str = os.environ.get('TEST_CHANNELS', '0')
    test_channels = [int(x) for x in test_channels_str.split(',')]

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

    # Initialize APB master for stream_top configuration interface
    await tb.init_apb_master()

    # Read version register to verify APB connectivity (with debug probing)
    version = await tb.read_apb_register(0x108, debug_probe=True)  # VERSION register
    tb.log.info(f"STREAM version: 0x{version:08X}")

    # Enable STREAM globally
    await tb.enable_global()

    # Enable all channels
    channel_mask = (1 << num_channels) - 1
    await tb.enable_channel_mask(channel_mask)

    # SANITY TEST: Verify readback of CHANNEL_ENABLE to confirm readback path works
    channel_en_readback = await tb.read_apb_register(0x120, debug_probe=True)  # CHANNEL_ENABLE address
    tb.log.info(f"CHANNEL_ENABLE readback: wrote=0x{channel_mask:02X}, read=0x{channel_en_readback:02X}")
    if channel_en_readback != channel_mask:
        tb.log.error(f"READBACK MISMATCH: CHANNEL_ENABLE readback path broken!")
    else:
        tb.log.info(f"READBACK OK: CHANNEL_ENABLE matches")

    # Configure AXI transfer beats (CRITICAL for stream_top!)
    # This register MUST be configured via APB, unlike stream_core which uses signals
    await tb.configure_transfer_beats(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)

    # Configure descriptor engine address range
    # Router now default-routes all non-m0/perf addresses to PeakRDL config space
    await tb.configure_descriptor_address_range()

    # Read global status
    status = await tb.read_global_status()
    tb.log.info(f"Global status after enable: 0x{status:08X}")
    tb.log.info(f"=== Stream Top Basic Test ===")
    tb.log.info(f"Channels: {num_channels}, Data Width: {data_width}, "
               f"FIFO Depth: {fifo_depth}")
    tb.log.info(f"Test channels: {test_channels}, Descriptors: {desc_count}")
    tb.log.info(f"Transfer sizes: {transfer_sizes}")

    # Run transfers for each test channel
    for channel in test_channels:
        tb.log.info(f"\n=== Testing Channel {channel} ===")

        # Create descriptor chain for this channel
        base_src_addr = tb.src_mem_base + (channel * 0x1000000)
        base_dst_addr = tb.dst_mem_base + (channel * 0x1000000)

        descriptors = []

        for i in range(desc_count):
            # Rotate through transfer sizes
            transfer_size = transfer_sizes[i % len(transfer_sizes)]

            # Descriptor address (64-byte spacing)
            desc_addr = tb.desc_mem_base + (channel * 0x100000) + (i * 64)
            next_desc_addr = desc_addr + 64 if i < desc_count - 1 else 0

            # Source/destination addresses (0x10000 offset per descriptor)
            src_addr = base_src_addr + (i * 0x10000)
            dst_addr = base_dst_addr + (i * 0x10000)

            # Write test pattern to source memory
            for beat in range(transfer_size):
                beat_addr = src_addr + (beat * tb.data_bytes)
                # Pattern includes channel and descriptor index
                pattern = ((channel << 8) | (i << 4) | (beat & 0xF)) & 0xFF
                # Byte replication
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
                priority=0,
                last=is_last,
                interrupt=is_last  # Generate interrupt on last descriptor
            )

            # Track descriptor for verification
            descriptors.append({
                'src_addr': src_addr,
                'dst_addr': dst_addr,
                'length': transfer_size
            })

            tb.log.info(f"Descriptor {i}: src=0x{src_addr:016X}, dst=0x{dst_addr:016X}, "
                       f"len={transfer_size} beats")

        # Kick off channel via APB write
        first_desc_addr = tb.desc_mem_base + (channel * 0x100000)
        await tb.kick_off_channel(channel, first_desc_addr)

        # Wait for completion (interrupt-based)
        await tb.wait_for_channel_idle(channel, timeout_us=200)  # 200us timeout (before 500us cocotb timeout)

        # Verify data transfer
        tb.log.info(f"Verifying data for channel {channel}...")
        all_passed = True
        for idx, desc in enumerate(descriptors):
            match = tb.verify_transfer(desc['src_addr'], desc['dst_addr'], desc['length'])
            if not match:
                tb.log.error(f"Transfer {idx} ({desc['length']} beats) data mismatch")
                all_passed = False
            else:
                tb.log.info(f"Transfer {idx} ({desc['length']} beats) verified OK")

        if all_passed:
            tb.log.info(f"Channel {channel} data verification PASSED")
        else:
            tb.log.error(f"Channel {channel} data verification FAILED")
            raise AssertionError(f"Channel {channel} data mismatch")

        # Get performance stats
        stats = tb.get_performance_stats(channel)
        if stats:
            tb.log.info(f"Channel {channel} performance: {stats['duration_ns']}ns")

    tb.log.info("\n=== Test Complete - All channels verified ===")


# ==============================================================================
# Pytest Wrappers
# ==============================================================================

@pytest.mark.parametrize("params", generate_test_params(), ids=lambda p: (
    f"nc{p['num_channels']:02d}_dw{p['data_width']:04d}_fd{p['fifo_depth']:04d}_"
    f"dc{p['desc_count']:02d}_nch{len(p['test_channels']):02d}_{p['scenario']}_{p['timing_profile']}"
))
def test_stream_top_basic(request, params):
    """Pytest wrapper for stream_top basic test"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/stream_top',
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    dut_name = "stream_top_ch8"

    # Get sources from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/top/stream_top_ch8.f'
    )

    # RTL parameters (stream_top has fixed parameters in module definition)
    rtl_parameters = {
        'NUM_CHANNELS': params['num_channels'],
        'DATA_WIDTH': params['data_width'],
        'ADDR_WIDTH': 64,
        'SRAM_DEPTH': params['fifo_depth'],
        'APB_ADDR_WIDTH': params['apb_addr_width'],
        'APB_DATA_WIDTH': params['apb_data_width'],
        'USE_AXI_MONITORS': 0,  # Disable monitors for basic integration testing
        'CDC_ENABLE': 0,        # Disable CDC for debugging (pclk = aclk)
    }

    # Create unique test name
    nc_str = f"{params['num_channels']:02d}"
    dw_str = f"{params['data_width']:04d}"
    fd_str = f"{params['fifo_depth']:04d}"
    dc_str = f"{params['desc_count']:02d}"
    scenario = params.get('scenario', 'standard')
    timing = params.get('timing_profile', 'fast')
    test_name_plus_params = f"test_{dut_name}_nc{nc_str}_dw{dw_str}_fd{fd_str}_dc{dc_str}_{scenario}_{timing}"

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

    # Set environment variables for test configuration
    extra_env = {
        'NUM_CHANNELS': str(params['num_channels']),
        'DATA_WIDTH': str(params['data_width']),
        'FIFO_DEPTH': str(params['fifo_depth']),
        'AXI_ID_WIDTH': str(params['axi_id_width']),
        'APB_ADDR_WIDTH': str(params['apb_addr_width']),
        'APB_DATA_WIDTH': str(params['apb_data_width']),
        'DESC_COUNT': str(params['desc_count']),
        'TRANSFER_SIZES': ','.join(map(str, params['transfer_sizes'])),
        'TEST_CHANNELS': ','.join(map(str, params['test_channels'])),
        'TIMING_PROFILE': params['timing_profile'],
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

    # Add warnings to suppress
    compile_args.extend([
        "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE",
        "-Wno-TIMESCALEMOD",
        "-Wno-SELRANGE",
        "-Wno-UNUSEDSIGNAL",
        "-Wno-UNDRIVEN",
        "-Wno-MULTIDRIVEN",  # PeakRDL-generated code has expected MULTIDRIVEN warnings
    ])

    # Create view command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Import cocotb_test.simulator.run
    from cocotb_test.simulator import run

    try:
        # Build and run
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_stream_top_basic",
            parameters=rtl_parameters,
            compile_args=compile_args,
            sim_args=sim_args,
            extra_env=extra_env,
            sim_build=sim_build,
            waves=False,  # Explicitly disable auto-FST
            keep_files=True,
            simulator='verilator',
        )
        print(f"✓ Stream top test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Stream top test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


# ==============================================================================
# Main Entry Point (for standalone execution)
# ==============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v"])
