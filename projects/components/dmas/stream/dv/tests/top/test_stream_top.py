"""
================================================================================
Stream Top Integration Test
================================================================================

Test suite for stream_top_ch8 - complete STREAM DMA with APB configuration.

Tests the full integration of:
- APB4 configuration interface
- peakrdl_to_cmdrsp (APB to CMD/RSP conversion)
- apb4todescr (channel kick-off router)
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

# Import utilities
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, get_repo_root, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.stream.dv.tbclasses.stream_core_tb import StreamCoreTB, StreamRegisterMap

# Coverage integration - optional import
try:
    from projects.components.dmas.stream.dv.stream_coverage import (
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
            # Per-channel skew with W-channel backpressure (regression sentinel
            # for the axi_write_engine WLAST/drain bug). See MIXED_AXI_PROFILES.
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

    # Long single-channel runs (NUM_CHANNELS=1). These exercise the
    # generate-select single-client arbiter passthrough (descriptor-AR) and the
    # guarded channel-ID widths added to support a 1-channel build, with
    # sustained traffic on channel 0. 'full' level only -- they are long.
    if test_level == 'full':
        # NUM_CHANNELS=1 long runs: multiple chained descriptors, each spanning
        # several write bursts (transfer > 17 beats), to exercise the
        # single-client arbiter's hold-for-ack burst sequencing on channel 0.
        # Sized to complete under the cocotb scoreboard (~beats, not KB).
        one_ch_runs = [
            # (scenario tag, desc_count, transfer_sizes, timing)
            ('1ch_long_chain', 6, [24],     'fast'),   # 6 chained desc, 2 bursts each
            ('1ch_long_mixed', 4, [24, 48], 'mixed'),  # mixed sizes + backpressure
        ]
        for tag, dc, sizes, timing in one_ch_runs:
            params.append({
                'num_channels': 1,
                'data_width': data_width,
                'fifo_depth': 4096,
                'axi_id_width': 8,
                'apb_addr_width': 12,
                'apb_data_width': 32,
                'desc_count': dc,
                'test_channels': [0],
                'transfer_sizes': sizes,
                'timing_profile': timing,
                'scenario': tag,
            })

    return params


# ==============================================================================
# CocoTB Test Functions
# ==============================================================================

@cocotb.test(timeout_time=50000, timeout_unit="us")
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

    # Initialize coverage if enabled
    test_name = f"test_stream_top_nc{num_channels:02d}_dw{data_width:04d}_nch{len(test_channels):02d}"
    coverage = get_coverage_helper(test_name, log=tb.log)

    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats, wr_xfer_beats=wr_xfer_beats)

    tb.log.info(f"=== Scenario STREAM-TOP-01: APB configuration and kick-off ===")
    tb.log.info(f"=== Also covers: STREAM-TOP-02 (single channel end-to-end), STREAM-TOP-03 (multi-channel concurrent operation) ===")
    tb.log.info(f"=== STREAM-TOP-04 (descriptor chaining), STREAM-TOP-08 (IRQ generation and clearing), STREAM-TOP-09 (MonBus event reporting) ===")
    tb.log.info(f"=== STREAM-TOP-10 (channel arbitration), STREAM-TOP-11 (system-level backpressure), STREAM-TOP-12 (enable/disable channels) ===")
    tb.log.info(f"=== STREAM-TOP-13 (reset during operation) ===")
    tb.log.info(f"=== Note: STREAM-TOP-05 (APB error handling), STREAM-TOP-06 (AXI descriptor fetch error), STREAM-TOP-07 (AXI data transfer error) would require specific error injection ===")


    # Initialize APB master for stream_top configuration interface
    await tb.init_apb4_master()

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

    # Size the scheduler write-completion timeout to the workload (channels x max
    # transfer x AXI profile). The RTL default (1000 cyc) is too tight for
    # multi-channel transfers sharing one write engine; program it via APB since on
    # the top the timeout register is reg-driven (a signal poke is overridden).
    await tb.program_scheduler_timeout(
        num_channels=num_channels,
        max_xfer_beats=256,  # STREAM architectural max transfer (beats)
        profile=os.environ.get('TIMING_PROFILE', 'fixed'),
    )

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
        # Use 0x400000 (4MB) per channel to fit 8 channels in 32MB source/dest memory
        base_src_addr = tb.src_mem_base + (channel * 0x400000)
        base_dst_addr = tb.dst_mem_base + (channel * 0x400000)

        descriptors = []

        for i in range(desc_count):
            # Rotate through transfer sizes
            transfer_size = transfer_sizes[i % len(transfer_sizes)]

            # Descriptor address (64-byte spacing)
            # Use 0x10000 (64KB) per channel to fit 8 channels in 512KB descriptor memory
            desc_addr = tb.desc_mem_base + (channel * 0x10000) + (i * 64)
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
        first_desc_addr = tb.desc_mem_base + (channel * 0x10000)
        await tb.kick_off_channel(channel, first_desc_addr)

        # Wait for completion (interrupt-based)
        await tb.wait_for_channel_idle(channel, timeout_us=400)  # 400us per channel (2000us total cocotb timeout)

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

        # MUST: prove the kick-register WRITE actually caused a descriptor FETCH
        # (kick reg -> apb4todescr -> descriptor engine), not just that data moved.
        # A dead/mis-decoded kick path leaves the kicked descriptor un-fetched.
        tb.assert_descriptors_fetched()

        # MUST: prove the engine's actual read/write AXI cycles match the
        # descriptors, per channel (by AXI ID) -- right src/dst, right length.
        tb.assert_engine_matches_descriptors()

        # Get performance stats
        stats = tb.get_performance_stats(channel)
        if stats:
            tb.log.info(f"Channel {channel} performance: {stats['duration_ns']}ns")

    # Sample coverage if enabled
    if coverage:
        burst_size = data_width // 8

        # Sample APB transactions - configuration writes and status reads
        coverage.sample_apb_write(is_error=False)  # Global enable
        coverage.sample_apb_write(is_error=False)  # Channel enable
        coverage.sample_apb_write(is_error=False)  # Transfer beats config
        coverage.sample_apb_read(is_error=False)   # Version read
        coverage.sample_apb_read(is_error=False)   # Status reads

        # Sample AXI transactions for all channels/descriptors
        for channel in test_channels:
            for i in range(desc_count):
                transfer_size = transfer_sizes[i % len(transfer_sizes)]
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

        # Sample functional scenarios
        coverage.sample_scenario("basic_transfer")
        if desc_count > 1:
            coverage.sample_scenario("descriptor_chain")
        if len(test_channels) > 1:
            coverage.sample_scenario("concurrent_rw")
            coverage.sample_scenario("full_pipeline")

        # Sample handshakes
        coverage.sample_handshake("read_request")
        coverage.sample_handshake("read_response")
        coverage.sample_handshake("write_request")
        coverage.sample_handshake("write_response")
        coverage.sample_handshake("apb_transfer")

        # Sample IRQ scenario (we use interrupt on last descriptor)
        coverage.sample_scenario("irq")

        # Save coverage
        coverage.save()
        tb.log.info(f"Coverage saved for {test_name}")

    tb.log.info("\n=== Test Complete - All channels verified ===")


async def _ext_setup(dut):
    """Common bring-up for the extended (USE_ROW_COL_MAJOR_ADDRESSING=1) tests:
    APB config, enable, transfer-beats, descriptor range, scheduler timeout."""
    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    tb = StreamCoreTB(
        dut=dut, num_channels=num_channels, addr_width=64,
        data_width=int(os.environ.get('DATA_WIDTH', '512')),
        axi_id_width=int(os.environ.get('AXI_ID_WIDTH', '8')),
        fifo_depth=int(os.environ.get('FIFO_DEPTH', '4096')),
        apb_addr_width=12, apb_data_width=32,
    )
    await tb.setup_clocks_and_reset(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.init_apb4_master()
    await tb.enable_global()
    await tb.enable_channel_mask((1 << num_channels) - 1)
    await tb.configure_transfer_beats(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.configure_descriptor_address_range()
    await tb.program_scheduler_timeout(
        num_channels=num_channels, max_xfer_beats=256, profile='fast')
    return tb


def _fill_src(tb, src_addr, tag, beats):
    """Distinct per-beat pattern (tag in high nibble) so a permutation is visible."""
    bpb = tb.data_bytes
    for beat in range(beats):
        pat = ((tag << 4) | (beat & 0xF)) & 0xFF
        data = int.from_bytes(bytes([pat] * bpb), byteorder='little')
        tb.write_source_data(src_addr + beat * bpb, data, bpb)


def _beat_multiset(tb, model, mem_base, region, beats):
    """Sorted list of a region's beat-values (for the transpose permutation check)."""
    bpb = tb.data_bytes
    return sorted(bytes(model.read((region - mem_base) + b * bpb, bpb))
                  for b in range(beats))


@cocotb.test(timeout_time=50000, timeout_unit="us")
async def cocotb_test_stream_top_extended(dut):
    """MIXED legacy + extended (TASK-101 row/col) descriptors in ONE run,
    covering the paths that are known-good:
      - channel 0: legacy -> extended-contiguous CHAIN (both formats mixed in a
        single descriptor chain; data-verified byte-for-byte + scoreboard)
      - channel 1: extended TRANSPOSE, kicked directly (strided/per-beat write
        datapath; permutation-verified + scoreboard)
    Proves both formats are fetched and that every engine rd/wr AXI cycle matches
    the programmed descriptors (format-agnostic scoreboard). The chained-transpose
    corner is broken in RTL and covered separately (see the xfail test)."""
    tb = await _ext_setup(dut)
    bpb = tb.data_bytes
    beats = 16

    # --- channel 0: legacy -> extended-contiguous chain (both formats) --------
    ch = 0
    bs, bd = tb.src_mem_base + ch * 0x400000, tb.dst_mem_base + ch * 0x400000
    db = tb.desc_mem_base + ch * 0x10000
    s0s, s0d = bs + 0 * 0x10000, bd + 0 * 0x10000
    s1s, s1d = bs + 1 * 0x10000, bd + 1 * 0x10000
    _fill_src(tb, s0s, 0x1, beats)
    _fill_src(tb, s1s, 0x2, beats)
    tb.write_descriptor(addr=db + 0x00, src_addr=s0s, dst_addr=s0d, length=beats,
                        next_ptr=db + 0x40, channel_id=ch, last=False, interrupt=False)
    contig = {'s0': bpb, 's1': 0, 'inner': beats}       # index_0 walks all beats
    tb.write_ext_descriptor(addr=db + 0x40, src_addr=s1s, dst_addr=s1d, beats=beats,
                            rd=contig, wr=contig, channel_id=ch, next_ptr=0, last=True)
    await tb.kick_off_channel(ch, db)
    await tb.wait_for_channel_idle(ch, timeout_us=600)
    assert tb.verify_transfer(s0s, s0d, beats), "legacy contiguous data mismatch"
    assert tb.verify_transfer(s1s, s1d, beats), "extended contiguous data mismatch"

    # --- channel 1: extended transpose, kicked directly -----------------------
    ch = 1
    bs, bd = tb.src_mem_base + ch * 0x400000, tb.dst_mem_base + ch * 0x400000
    db = tb.desc_mem_base + ch * 0x10000
    ts, td = bs + 0 * 0x10000, bd + 0 * 0x10000
    _fill_src(tb, ts, 0x3, beats)
    C = 4                                                # 4x4 grid = 16 beats
    rd_t = {'s0': bpb,     's1': C * bpb, 'inner': C}    # row-major read (linear)
    wr_t = {'s0': C * bpb, 's1': bpb,     'inner': C}    # column-major write
    tb.write_ext_descriptor(addr=db + 0x00, src_addr=ts, dst_addr=td, beats=beats,
                            rd=rd_t, wr=wr_t, channel_id=ch, next_ptr=0, last=True)
    await tb.kick_off_channel(ch, db)
    await tb.wait_for_channel_idle(ch, timeout_us=600)
    assert (_beat_multiset(tb, tb.src_memory_model, tb.src_mem_base, ts, beats) ==
            _beat_multiset(tb, tb.dst_memory_model, tb.dst_mem_base, td, beats)), \
        "extended transpose did not move every beat exactly once"

    # --- channel 2: extended -> extended CHAIN (both contiguous) --------------
    # Exercises the chain walk RESUMING after a 2-slot extended fetch -- the path
    # the char flow's build_ext_chain() drives. Contiguous mode works chained.
    ch = 2
    bs, bd = tb.src_mem_base + ch * 0x400000, tb.dst_mem_base + ch * 0x400000
    db = tb.desc_mem_base + ch * 0x10000
    e0s, e0d = bs + 0 * 0x10000, bd + 0 * 0x10000
    e1s, e1d = bs + 1 * 0x10000, bd + 1 * 0x10000
    _fill_src(tb, e0s, 0x4, beats)
    _fill_src(tb, e1s, 0x5, beats)
    tb.write_ext_descriptor(addr=db + 0x00, src_addr=e0s, dst_addr=e0d, beats=beats,
                            rd=contig, wr=contig, channel_id=ch,
                            next_ptr=db + 0x40, last=False)   # chunk0@0x00, chunk1@0x20
    tb.write_ext_descriptor(addr=db + 0x40, src_addr=e1s, dst_addr=e1d, beats=beats,
                            rd=contig, wr=contig, channel_id=ch,
                            next_ptr=0, last=True)            # chunk0@0x40, chunk1@0x60
    await tb.kick_off_channel(ch, db)
    await tb.wait_for_channel_idle(ch, timeout_us=600)
    assert tb.verify_transfer(e0s, e0d, beats), "ext->ext chain: first descriptor mismatch"
    assert tb.verify_transfer(e1s, e1d, beats), "ext->ext chain: second descriptor mismatch"

    # THE required checks across ALL channels: both formats fetched, and every
    # engine rd/wr cycle matches the programmed descriptors.
    tb.assert_descriptors_fetched()
    tb.assert_engine_matches_descriptors()
    tb.log.info("\n=== MIXED legacy+extended verified: legacy->ext-contig chain + "
                "transpose datapath + ext->ext chain "
                "(fetch + rd/wr scoreboard + data/permutation) ===")


@cocotb.test(timeout_time=50000, timeout_unit="us")
async def cocotb_test_stream_top_extended_chained_transpose(dut):
    """Regression for TASK-059 (FIXED): a strided/per-beat extended (transpose)
    descriptor reached via next_ptr CHAINING. It used to read the wrong source,
    write with holes, and corrupt the preceding descriptor's last beat because a
    legacy descriptor ran the run-base generator with stale ext config and left
    bogus bases in the generator FIFO, which this descriptor then consumed. Fixed
    by gating the generator `start` on w_is_ext in scheduler.sv. This asserts the
    CORRECT behaviour."""
    tb = await _ext_setup(dut)
    bpb = tb.data_bytes
    beats = 16
    ch = 0
    bs, bd = tb.src_mem_base + ch * 0x400000, tb.dst_mem_base + ch * 0x400000
    db = tb.desc_mem_base + ch * 0x10000
    s0s, s0d = bs + 0 * 0x10000, bd + 0 * 0x10000
    ts, td = bs + 2 * 0x10000, bd + 2 * 0x10000
    _fill_src(tb, s0s, 0x1, beats)
    _fill_src(tb, ts, 0x3, beats)
    C = 4
    rd_t = {'s0': bpb,     's1': C * bpb, 'inner': C}
    wr_t = {'s0': C * bpb, 's1': bpb,     'inner': C}
    tb.write_descriptor(addr=db + 0x00, src_addr=s0s, dst_addr=s0d, length=beats,
                        next_ptr=db + 0x40, channel_id=ch, last=False, interrupt=False)
    tb.write_ext_descriptor(addr=db + 0x40, src_addr=ts, dst_addr=td, beats=beats,
                            rd=rd_t, wr=wr_t, channel_id=ch, next_ptr=0, last=True)
    await tb.kick_off_channel(ch, db)
    await tb.wait_for_channel_idle(ch, timeout_us=600)
    assert tb.verify_transfer(s0s, s0d, beats), \
        "preceding legacy descriptor corrupted by chained transpose"
    assert (_beat_multiset(tb, tb.src_memory_model, tb.src_mem_base, ts, beats) ==
            _beat_multiset(tb, tb.dst_memory_model, tb.dst_mem_base, td, beats)), \
        "chained transpose did not move every beat exactly once"
    tb.assert_engine_matches_descriptors()


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
        filelist_path='projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f'
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

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

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

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

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
            waves=enable_waves,  # Explicitly disable auto-FST
            keep_files=True,
            simulator='verilator',
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"✓ Stream top test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Stream top test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


def _run_extended(testcase, name_suffix):
    """Build stream_top_ch8 with USE_ROW_COL_MAJOR_ADDRESSING=1 and run one
    extended-descriptor cocotb testcase (fixed config: 8ch, 512b)."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/stream_top',
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    dut_name = "stream_top_ch8"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f'
    )

    rtl_parameters = {
        'NUM_CHANNELS': 8,
        'DATA_WIDTH': 512,
        'ADDR_WIDTH': 64,
        'USE_ROW_COL_MAJOR_ADDRESSING': 1,   # ← enable the extended (row/col) path
        'SRAM_DEPTH': 4096,
        'APB_ADDR_WIDTH': 12,
        'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': 0,
        'CDC_ENABLE': 0,
    }

    test_name_plus_params = f"test_{dut_name}_{name_suffix}"
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
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
    }
    extra_env.update(get_coverage_env(test_name_plus_params, sim_build=sim_build))

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-structs", "--trace-depth", "99", "-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = ["--trace", "--trace-structs", "--trace-depth", "99"]
    else:
        compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps"]
        sim_args = []

    compile_args.extend([
        "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD", "-Wno-SELRANGE",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN", "-Wno-MULTIDRIVEN",
    ])
    compile_args.extend(get_coverage_compile_args())

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    from cocotb_test.simulator import run

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        parameters=rtl_parameters,
        compile_args=compile_args,
        sim_args=sim_args,
        extra_env=extra_env,
        sim_build=sim_build,
        waves=enable_waves,
        keep_files=True,
        simulator='verilator',
        plus_args=['--trace'] if enable_waves else [],
    )
    print(f"✓ Stream top {name_suffix} test completed! Logs: {log_path}")


def test_stream_top_extended(request):
    """Mixed legacy + extended descriptors (USE_ROW_COL_MAJOR_ADDRESSING=1,
    TASK-101): legacy->ext-contiguous chain + directly-kicked transpose."""
    _run_extended("cocotb_test_stream_top_extended", "extended_mixed")


def test_stream_top_extended_chained_transpose(request):
    """Regression for TASK-059 (FIXED): chained + strided extended (transpose)
    descriptor. Was silent data corruption; fixed by gating the run-base
    generator start on w_is_ext (scheduler.sv)."""
    _run_extended("cocotb_test_stream_top_extended_chained_transpose",
                  "extended_chained_transpose")


# ==============================================================================
# Main Entry Point (for standalone execution)
# ==============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v"])
