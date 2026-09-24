"""
Perf capture FIFO read protocol -- STREAM TASK-086.

The register walk reads PERF_DATA_LOW/HIGH/STATUS with the FIFO EMPTY, so it
returns zeros whatever the hardware does. That is why the non-atomic read in
TASK-085 survived: the defect and the fix were indistinguishable to the suite.
This test drives the FIFO NON-EMPTY and asserts the pairing protocol.

Protocol under test (45fa4972e): both PERF_DATA_LOW and PERF_DATA_HIGH read
the FIFO head; the entry is popped once BOTH have been read, in either order.

The decisive check is READ LOW TWICE -> NO POP. Under the old design the LOW
read alone popped, so two LOW reads dropped two entries; that is the exact
defect this test exists to catch.

Every register is addressed BY NAME through stream_regmap.py.
"""

import os
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dmas.stream.dv.tbclasses.stream_core_tb import StreamCoreTB

PERF_EN = 1 << 0          # PERF_CONFIG.PERF_EN   -- timestamp mode when MODE=0
STATUS_EMPTY = 1 << 0     # PERF_STATUS.EMPTY
STATUS_FULL = 1 << 1      # PERF_STATUS.FULL


def _status(word):
    """Decode PERF_STATUS: EMPTY[0], FULL[1], COUNT[31:16]."""
    return {
        'empty': bool(word & STATUS_EMPTY),
        'full': bool(word & STATUS_FULL),
        'count': (word >> 16) & 0xFFFF,
    }


def _parse_high(word):
    """PERF_DATA_HIGH = {28'b0, event_type, channel_id[2:0]}."""
    return word & 0x7, (word >> 3) & 0x1


@cocotb.test(timeout_time=2000, timeout_unit="us")
async def cocotb_test_perf_fifo_pairing(dut):
    """Drive the perf FIFO non-empty and verify the both-read pop protocol."""
    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '512'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '4096'))
    channel = int(os.environ.get('PERF_CHANNEL', '0'))
    beats = int(os.environ.get('PERF_BEATS', '16'))

    tb = StreamCoreTB(
        dut=dut,
        num_channels=num_channels,
        addr_width=64,
        data_width=data_width,
        axi_id_width=int(os.environ.get('AXI_ID_WIDTH', '8')),
        fifo_depth=fifo_depth,
        apb_addr_width=int(os.environ.get('APB_ADDR_WIDTH', '13')),
        apb_data_width=int(os.environ.get('APB_DATA_WIDTH', '32')),
    )

    await tb.setup_clocks_and_reset(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.init_apb4_master()

    # GLOBAL_EN first: cfg_perf_enable is `reg_perf_config_perf_en &
    # reg_global_ctrl_global_en` in stream_config_block, so enabling the
    # profiler without global enable captures NOTHING and this test would
    # pass vacuously.
    await tb.enable_global()
    await tb.enable_channel_mask(1 << channel)
    await tb.configure_transfer_beats(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.configure_descriptor_address_range()
    await tb.program_scheduler_timeout(num_channels=num_channels, max_xfer_beats=16)

    # Enable the profiler in timestamp mode, BY NAME.
    await tb.write_reg('PERF_CONFIG', PERF_EN)
    readback = await tb.read_reg('PERF_CONFIG')
    assert readback & PERF_EN, (
        f"PERF_CONFIG readback 0x{readback:08X} has PERF_EN clear -- the "
        f"profiler never enabled, so nothing below would be meaningful")

    # Run a transfer so the scheduler produces idle/active transitions, which
    # is what perf_profiler captures (channel_idle <- scheduler_idle).
    # Addresses MUST come from the TB's memory regions: write_source_data
    # computes `addr - src_mem_base` as a model offset, so an invented base
    # indexes negatively (src_mem_base is 0x8000_0000, dst is 0x9000_0000).
    desc_addr = tb.desc_mem_base + (channel * 0x10000)
    src_addr = tb.src_mem_base + (channel * 0x400000)
    dst_addr = tb.dst_mem_base + (channel * 0x400000)
    for beat in range(beats):
        pattern = ((channel << 8) | (beat & 0xF)) & 0xFF
        data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
        tb.write_source_data(src_addr + beat * tb.data_bytes, data, tb.data_bytes)
    tb.write_descriptor(addr=desc_addr, src_addr=src_addr, dst_addr=dst_addr,
                        length=beats, next_ptr=0, priority=0, last=True,
                        channel_id=channel, interrupt=True)

    await tb.kick_off_channel(channel, desc_addr)
    # Capture the verdict: wait_for_channel_idle returns False on TIMEOUT.
    # Discarding it would let an unfinished transfer through, and the perf
    # entries read below would then come from a run that never completed.
    idle_ok = await tb.wait_for_channel_idle(channel, timeout_us=400)
    assert idle_ok, (
        f"channel {channel} did not reach idle within 400us -- the transfer "
        f"did not complete, so the perf FIFO contents below are not trustworthy")

    # ---- guard: the FIFO MUST be non-empty, or this test proves nothing ----
    st = _status(await tb.read_reg('PERF_STATUS'))
    tb.log.info(f"PERF_STATUS after transfer: {st}")
    assert not st['empty'] and st['count'] > 0, (
        f"perf FIFO is EMPTY after a {beats}-beat transfer ({st}) -- the whole "
        f"point of TASK-086 is to read it NON-empty; a passing run here would "
        f"be vacuous")
    start_count = st['count']

    # ---- P1: reading LOW alone must NOT pop -------------------------------
    low_a = await tb.read_reg('PERF_DATA_LOW')
    after_one = _status(await tb.read_reg('PERF_STATUS'))['count']
    low_a2 = await tb.read_reg('PERF_DATA_LOW')
    after_two = _status(await tb.read_reg('PERF_STATUS'))['count']
    assert after_one == start_count and after_two == start_count, (
        f"reading PERF_DATA_LOW popped the FIFO: count {start_count} -> "
        f"{after_one} -> {after_two}. The entry must be retired only once "
        f"BOTH halves have been read (TASK-085).")
    assert low_a2 == low_a, (
        f"two LOW reads of the same head entry differ: "
        f"0x{low_a:08X} vs 0x{low_a2:08X}")

    # ---- P2: the HIGH read completes the pair and pops exactly one --------
    high_a = await tb.read_reg('PERF_DATA_HIGH')
    after_pair = _status(await tb.read_reg('PERF_STATUS'))['count']
    assert after_pair == start_count - 1, (
        f"completing the LOW/HIGH pair should retire exactly one entry: "
        f"count {start_count} -> {after_pair}")
    ch_a, ev_a = _parse_high(high_a)
    assert ch_a == channel, f"entry channel_id {ch_a} != kicked channel {channel}"
    assert ev_a in (0, 1), f"event_type {ev_a} out of range"
    # DATA COHERENCE, not just the pop protocol. Before 45fa4972e the LOW
    # read returned the capture flop BEFORE its own pop reached it, so the
    # first entry read back was the RESET VALUE (ts=0, ev=0). A zero
    # timestamp is therefore the signature of the original defect.
    assert low_a != 0, (
        "PERF_DATA_LOW returned 0 for a captured entry -- that is the stale "
        "pre-pop value the capture flop used to expose (TASK-085)")
    tb.log.info(f"entry A: ts=0x{low_a:08X} ch={ch_a} ev={ev_a}")

    # ---- P3: the reverse order works identically --------------------------
    low_b = ev_b = None
    if after_pair > 0:
        high_b = await tb.read_reg('PERF_DATA_HIGH')
        mid = _status(await tb.read_reg('PERF_STATUS'))['count']
        assert mid == after_pair, (
            f"reading PERF_DATA_HIGH alone popped the FIFO: "
            f"count {after_pair} -> {mid}")
        low_b = await tb.read_reg('PERF_DATA_LOW')
        after_rev = _status(await tb.read_reg('PERF_STATUS'))['count']
        assert after_rev == after_pair - 1, (
            f"HIGH-then-LOW should retire exactly one entry: "
            f"count {after_pair} -> {after_rev}")
        ch_b, ev_b = _parse_high(high_b)
        assert ch_b == channel, f"entry channel_id {ch_b} != kicked channel {channel}"
        tb.log.info(f"entry B (reverse order): ts=0x{low_b:08X} ch={ch_b} ev={ev_b}")
        assert low_b != low_a or ev_b != ev_a, (
            "entry B is identical to entry A -- the pop did not advance the FIFO")

    # ---- P4: one transfer yields exactly one START and one END ------------
    # This is what the old design could not produce: its first entry was the
    # all-zero reset value (ev=0) and the real END event was never observed,
    # so the two entries came back as {START, START}.
    if ev_b is not None:
        assert {ev_a, ev_b} == {0, 1}, (
            f"expected one START (0) and one END (1) for a single transfer, "
            f"got event types {{{ev_a}, {ev_b}}} -- a duplicated event type "
            f"means the two halves were not read as coherent entries")
        ts_start = low_a if ev_a == 0 else low_b
        ts_end = low_b if ev_b == 1 else low_a
        assert 0 < ts_start < ts_end, (
            f"START must carry a non-zero timestamp earlier than END: "
            f"start=0x{ts_start:08X} end=0x{ts_end:08X}")
        tb.log.info(f"pairing OK: START@0x{ts_start:08X} -> END@0x{ts_end:08X}")

    tb.log.info("PASSED: perf FIFO both-read pop protocol")


def test_stream_top_perf_fifo(request):
    """Pytest wrapper -- drives the perf FIFO non-empty (TASK-086)."""
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/stream_top',
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    dut_name = "stream_top_ch8"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/dmas/stream/rtl/filelists/top/stream_top_ch8.f')

    rtl_parameters = {
        'NUM_CHANNELS': 8, 'DATA_WIDTH': 512, 'ADDR_WIDTH': 64,
        'SRAM_DEPTH': 4096, 'APB_ADDR_WIDTH': 13, 'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': 0, 'CDC_ENABLE': 0,
    }

    test_name_plus_params = f"test_{dut_name}_perf_fifo"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        **level_env(os.environ.get('REG_LEVEL', 'func').lower()),
        'NUM_CHANNELS': '8', 'DATA_WIDTH': '512', 'FIFO_DEPTH': '4096',
        'AXI_ID_WIDTH': '8', 'APB_ADDR_WIDTH': '13', 'APB_DATA_WIDTH': '32',
        'PERF_CHANNEL': '0', 'PERF_BEATS': '16',
        'DUT': dut_name, 'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_perf_fifo_pairing",
        parameters=rtl_parameters,
        compile_args=["-Wno-fatal", "--timescale", "1ns/1ps"],
        sim_args=[],
        extra_env=extra_env,
        sim_build=sim_build,
        keep_files=True,
        simulator='verilator',
    )
