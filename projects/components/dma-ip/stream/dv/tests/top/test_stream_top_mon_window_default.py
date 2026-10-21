# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_top_mon_window_default
# Purpose: A DEFAULT build (monitors off, USE_MON_REGS left at its default)
#          must answer the MON register window and let a host read the
#          always-built axi_bus_meter counters through it.
#
# WHY THIS EXISTS
# ---------------
# stream_core builds the two axi_bus_meter instances and the beat/byte/burst/
# window counters regardless of USE_AXI_MONITORS, but their registers
# (RDMON/WRMON_PERF_*) and their RUN bits live in the MON window at 0x1000.
# USE_MON_REGS used to default to USE_AXI_MONITORS, so on a default
# (monitors-off) build every MON access answered PSLVERR: the meters were
# built, and RUN could never be set nor a counter read. Owner ruling
# 2026-10-13: USE_MON_REGS defaults to 1, independent of USE_AXI_MONITORS.
#
# The negative direction -- an EXPLICIT USE_MON_REGS=0 still errors the window
# -- stays in test_stream_top_mon_gate.py.
#
# Like that file, this one reads PSLVERR from the BFM packet, because
# StreamCoreTB.read_reg discards it. Registers are addressed BY NAME.

import os
import sys

import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from projects.components.dma_ip.stream.dv.tbclasses.stream_core_tb import StreamCoreTB
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402

STREAM_TEST_SEED = os.environ.get('RANDOM_SEED', '12345')

NUM_CHANNELS = 8
DATA_WIDTH = 512
BEATS = 16
CHANNEL = 0

# Bus-meter readbacks that must be nonzero / equal to the transfer after a run.
METER_SIDES = ('RDMON', 'WRMON')


async def _xfer(tb, addr, write, wdata=0):
    """One APB transfer, returning BOTH prdata and the completer's error flag."""
    from CocoTBFramework.components.apb.apb_packet import APBPacket
    pkt = APBPacket(
        pwrite=1 if write else 0,
        paddr=addr,
        pwdata=wdata,
        pstrb=0xF,
        pprot=0,
        data_width=32,
        addr_width=tb.apb_addr_width,
        strb_width=4,
    )
    await tb.apb4_master.busy_send(pkt)
    await RisingEdge(tb.clk)
    return int(pkt.fields.get('prdata', 0)), int(pkt.fields.get('pslverr', 0))


async def _rd(tb, reg, failures):
    addr = tb.reg_offset(reg)
    val, err = await _xfer(tb, addr, write=0)
    if err:
        failures.append(f"{reg} READ at 0x{addr:X} returned PSLVERR on a default build")
    return val


async def _wr(tb, reg, value, failures):
    addr = tb.reg_offset(reg)
    _, err = await _xfer(tb, addr, write=1, wdata=value)
    if err:
        failures.append(f"{reg} WRITE at 0x{addr:X} returned PSLVERR on a default build")


@cocotb.test(timeout_time=3000, timeout_unit="us")
async def cocotb_test_mon_window_default_readable(dut):
    """Default build: MON window answers, and the bus meters count a transfer."""
    tb = StreamCoreTB(
        dut=dut,
        num_channels=NUM_CHANNELS,
        addr_width=64,
        data_width=DATA_WIDTH,
        axi_id_width=8,
        fifo_depth=4096,
        apb_addr_width=13,
        apb_data_width=32,
    )
    await tb.setup_clocks_and_reset(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.init_apb4_master()

    # Vacuity guard: if PSLVERR did not bind, every "no error" below is free.
    assert tb.apb4_master.is_signal_present('PSLVERR'), (
        "PSLVERR did not bind on the APB master; the no-error checks below "
        "would be vacuous")

    failures = []

    # ---- 1. the window answers, and its status registers read sane --------
    # MON_FIFO_* report the monitor error FIFO; with no monitors built it is
    # empty with count 0. EMPTY=1 is the truthful value (0 would claim data).
    for reg in ('MON_FIFO_STATUS', 'MON_FIFO_COUNT', 'RDMON_PERF_STATUS',
                'WRMON_PERF_STATUS', 'DAXMON_PERF_STATUS'):
        addr = tb.reg_offset(reg)
        if not (addr >> 12) & 1:
            failures.append(f"{reg} resolved to 0x{addr:X}, outside the MON window")
    fifo_status = await _rd(tb, 'MON_FIFO_STATUS', failures)
    fifo_count = await _rd(tb, 'MON_FIFO_COUNT', failures)
    if fifo_status != 0x2:
        failures.append(f"MON_FIFO_STATUS = 0x{fifo_status:X} on a monitors-off build; "
                        f"expected 0x2 (EMPTY only)")
    if fifo_count != 0:
        failures.append(f"MON_FIFO_COUNT = 0x{fifo_count:X} on a monitors-off build; expected 0")

    # ---- 2. arm the read and write perf windows, BY NAME ------------------
    for side in METER_SIDES:
        await _wr(tb, f'{side}_PERF_CTRL', 1, failures)
        rb = await _rd(tb, f'{side}_PERF_CTRL', failures)
        if (rb & 1) != 1:
            failures.append(f"{side}_PERF_CTRL.RUN did not latch (0x{rb:X})")

    if failures:
        # Before the default change, every access above errors; stop here so the
        # report is the window failure, not a cascade of zero counters.
        assert not failures, "MON window not usable on a default build:\n  " + \
            "\n  ".join(failures)

    # ---- 3. run one transfer ----------------------------------------------
    await tb.enable_global()
    await tb.enable_channel_mask(1 << CHANNEL)
    await tb.configure_transfer_beats(rd_xfer_beats=16, wr_xfer_beats=16)
    await tb.configure_descriptor_address_range()
    await tb.program_scheduler_timeout(num_channels=NUM_CHANNELS, max_xfer_beats=16)

    desc_addr = tb.desc_mem_base + (CHANNEL * 0x10000)
    src_addr = tb.src_mem_base + (CHANNEL * 0x400000)
    dst_addr = tb.dst_mem_base + (CHANNEL * 0x400000)
    for beat in range(BEATS):
        pattern = ((CHANNEL << 8) | (beat & 0xF)) & 0xFF
        data = int.from_bytes(bytes([pattern] * tb.data_bytes), byteorder='little')
        tb.write_source_data(src_addr + beat * tb.data_bytes, data, tb.data_bytes)
    tb.write_descriptor(addr=desc_addr, src_addr=src_addr, dst_addr=dst_addr,
                        length=BEATS, next_ptr=0, priority=0, last=True,
                        channel_id=CHANNEL, interrupt=True)

    await tb.kick_off_channel(CHANNEL, desc_addr)
    idle_ok = await tb.wait_for_channel_idle(CHANNEL, timeout_us=400)
    assert idle_ok, f"channel {CHANNEL} did not reach idle; meter readback would be meaningless"
    await tb.wait_clocks('aclk', 64)  # let the window's settle-close fire

    # ---- 4. the meters counted the transfer ------------------------------
    for side in METER_SIDES:
        beats = await _rd(tb, f'{side}_PERF_BEAT_COUNT', failures)
        prod = await _rd(tb, f'{side}_PERF_PROD_CYCLES', failures)
        bursts = await _rd(tb, f'{side}_PERF_BURST_COUNT', failures)
        bytes_lo = await _rd(tb, f'{side}_PERF_BYTE_COUNT_LO', failures)
        tb.log.info(f"{side}: beats={beats} prod={prod} bursts={bursts} bytes={bytes_lo}")
        if beats != BEATS:
            failures.append(f"{side}_PERF_BEAT_COUNT = {beats}, expected {BEATS}")
        if prod != beats:
            failures.append(f"{side}_PERF_PROD_CYCLES = {prod} != beat count {beats}")
        if bursts == 0:
            failures.append(f"{side}_PERF_BURST_COUNT = 0 after a {BEATS}-beat transfer")
        if bytes_lo != BEATS * (DATA_WIDTH // 8):
            failures.append(f"{side}_PERF_BYTE_COUNT_LO = {bytes_lo}, "
                            f"expected {BEATS * (DATA_WIDTH // 8)}")

    # The descriptor port has no perf window in the lite monitor (and no
    # monitor at all here): its readbacks are tied, and must read 0.
    for reg in ('DAXMON_PERF_BEAT_COUNT', 'DAXMON_PERF_PROD_CYCLES', 'DAXMON_PERF_STATUS'):
        v = await _rd(tb, reg, failures)
        if v != 0:
            failures.append(f"{reg} = 0x{v:X}; the descriptor perf window is not built, expected 0")

    assert not failures, "MON window / bus meters on a default build:\n  " + \
        "\n  ".join(failures)
    tb.log.info("PASSED: default build answers the MON window and reads the bus meters")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_stream_top_mon_window_default(request, test_level):
    """Default (monitors-off) build: MON window readable, bus meters count."""
    module, repo_root_path, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/top',
        'rtl_stream_macro': '../../../../rtl/macro',
        'rtl_stream_fub': '../../../../rtl/fub',
        'rtl_amba': '../../../../../rtl/amba',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_path,
        filelist_path='projects/components/dma-ip/stream/rtl/filelists/top/stream_top_ch8.f')

    dut_name = "stream_top_ch8"
    rtl_parameters = {
        'NUM_CHANNELS': NUM_CHANNELS, 'DATA_WIDTH': DATA_WIDTH, 'ADDR_WIDTH': 64,
        'SRAM_DEPTH': 4096, 'APB_ADDR_WIDTH': 13, 'APB_DATA_WIDTH': 32,
        # The point of the test: monitors OFF and USE_MON_REGS NOT passed, so
        # the default is what gets exercised.
        'USE_AXI_MONITORS': 0, 'CDC_ENABLE': 0,
    }

    test_name = f"test_stream_top_mon_window_default_{test_level}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        testcase="cocotb_test_mon_window_default_readable",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env={
            **level_env(test_level),
            'DUT': dut_name,
            'NUM_CHANNELS': str(NUM_CHANNELS),
            'DATA_WIDTH': str(DATA_WIDTH),
            'APB_ADDR_WIDTH': '13',
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
            'RANDOM_SEED': STREAM_TEST_SEED,
            'COCOTB_RANDOM_SEED': STREAM_TEST_SEED,
        },
        keep_files=True,
        compile_args=["-Wno-fatal", "-Werror-MULTIDRIVEN", FIELD_COMBO_VLT, "--timescale", "1ns/1ps"],
        simulator='verilator',
    )
