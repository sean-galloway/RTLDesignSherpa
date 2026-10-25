#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Monbus-group coverage for stream_top_ch8 (USE_AXI_MONITORS=1).
#
# stream_top_ch8 contains a monbus_axil4_group_1wr (u_monbus_axil_group) that
# the existing stream_top tests never exercise (they build with monitors off
# and only sniff the raw pre-group mon bus). This test enables the AXI monitors
# via CSR, drives real descriptor transfers, and attaches the shared
# MonbusGroupHarness to the group -- the same collateral used by the bridge +
# val/amba monbus-group tests. Two paths are covered:
#   Phase A -- master-write (trace) path: completion packets stream out
#              m_axil_mon_* and decode as AXI completions (24-byte records,
#              beat order {tag,ts}, pkt[127:64], pkt[63:0] per the monitor
#              package spec).
#   Phase B -- error window + stream_irq (stream TASK-019, the write-only group):
#              completion packets are routed to the error path via
#              ERR_CFG.ERR_SELECT and land in memory as raw 3-beat records in
#              the error window (MON_GROUP_ERR_BASE/LIMIT), over the same
#              master-write port as the trace. stream_irq pulses once per
#              whole record landed and MON_ERR_REC_COUNT / err_rec_count count
#              them; the records read back out of the captured writes must
#              decode as AXI completions, and none of them may appear in the
#              trace window. There is no slave-read port any more.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.dma_ip.stream.dv.tbclasses.stream_core_tb import StreamCoreTB
from TBClasses.monbus import PktType
from TBClasses.scoreboards.monbus_group import (
    MonbusGroupHarness, BeatLayout, BeatOrder,
)
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

# Stream monitor CSRs referenced BY NAME. Addresses come only from
# stream_regmap.py via tb.write_reg() / tb.read_reg() (RegisterMap by-name
# access) -- so relocating the monitor block (e.g. 0x1000 -> elsewhere) needs
# only a stream_regmap.py regen, no changes to this test.
#
# Enable bits: MON_EN[0], ERR_EN[1], COMPL_EN[2] -> 0x7 turns on the monitor +
# error + completion reporting (COMPRESS_EN is a higher bit, left 0 = raw
# 3-beat records).
MON_ENABLE_REGS = ('DAXMON_ENABLE', 'RDMON_ENABLE', 'WRMON_ENABLE')
MON_EN_VALUE  = 0x7
# Per-monitor packet-drop mask (PKT_MASK) resets to 0xFFFF (drop everything);
# clear to 0 so monitor packets actually flow into the group.
MON_PKT_MASK_REGS = ('DAXMON_PKT_MASK', 'RDMON_PKT_MASK', 'WRMON_PKT_MASK')
# Per-monitor ERR_CFG (stream_regs.rdl): ERR_SELECT[3:0] is a bitmask indexed
# by packet_type selecting which types divert to the error window (bit0=Error,
# bit1=Completion, ...); ERR_MASK[15:8] reset 0xFF event-masks (drops) error
# packets. We route COMPLETIONS to the error window (ERR_SELECT=0x2): every
# transfer emits completion packets deterministically, the per-protocol
# completion masks reset to 0 (not dropped), and ERR_MASK=0xFF keeps the
# incidental descriptor SLVERR errors out -- so the error window fills cleanly
# with completions, which drives stream_irq (one irq_out pulse per record landed).
MON_ERR_CFG_REGS = ('DAXMON_ERR_CFG', 'RDMON_ERR_CFG', 'WRMON_ERR_CFG')
ERR_CFG_ROUTE_COMPL = 0xFF02   # ERR_SELECT=0x2 (compl->error window), ERR_MASK=0xFF
ERR_CFG_NONE        = 0xFF00   # ERR_SELECT=0 (nothing to the error window)

# Monbus-group flush window (top-level cfg_mon_* inputs on stream_top_ch8).
MON_BASE  = 0x0000_1000
MON_LIMIT = 0x0000_5000 - 1
MON_WMARK = 3           # one raw record = 3 beats -> flush eagerly
# The error window: a separate region of the same capture memory, 4 KB = 170
# whole records (the writer wraps to base past the last whole record).
MON_ERR_BASE  = 0x0001_0000
MON_ERR_LIMIT = 0x0001_1000 - 1
MON_ERR_WMARK = 3       # flush every record (the register's reset value)


@cocotb.test(timeout_time=2000, timeout_unit="us")
async def cocotb_test_stream_top_monbus(dut):
    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '64'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    rd_xfer_beats = int(os.environ.get('RD_XFER_BEATS', '8'))
    wr_xfer_beats = int(os.environ.get('WR_XFER_BEATS', '8'))
    transfer_size = int(os.environ.get('TRANSFER_SIZE', '16'))   # beats

    tb = StreamCoreTB(
        dut=dut, num_channels=num_channels, addr_width=64,
        data_width=data_width, axi_id_width=8, fifo_depth=fifo_depth,
        apb_addr_width=13, apb_data_width=32,
    )
    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats,
                                    wr_xfer_beats=wr_xfer_beats)
    await tb.init_apb4_master()
    await tb.enable_global()
    await tb.enable_channel_mask((1 << num_channels) - 1)
    await tb.configure_transfer_beats(rd_xfer_beats=rd_xfer_beats,
                                      wr_xfer_beats=wr_xfer_beats)
    await tb.configure_descriptor_address_range()

    # Size the scheduler write-completion timeout to the workload (the reg default
    # of 1000 cyc is too tight for multi-channel transfers sharing one write
    # engine). Programmed via APB since the top's timeout register is reg-driven.
    await tb.program_scheduler_timeout(
        num_channels=num_channels,
        max_xfer_beats=256,  # STREAM architectural max transfer (beats)
        profile=os.environ.get('TIMING_PROFILE', 'fixed'),
    )

    # Enable the three AXI monitors (monitor+error+completion) and clear their
    # packet-drop masks so clean traffic emits completion packets that stream
    # out the group's master-write (trace) path.
    for reg in MON_ENABLE_REGS:
        await tb.write_reg(reg, MON_EN_VALUE)
    for reg in MON_PKT_MASK_REGS:
        await tb.write_reg(reg, 0x0)

    # Program the group flush window via the INTERNAL MON CSRs (no longer
    # top-level cfg_mon_* ports): base/limit set the master-write window and
    # the watermark controls flush eagerness.
    await tb.write_reg('MON_GROUP_BASE_ADDR',       MON_BASE)
    await tb.write_reg('MON_GROUP_LIMIT_ADDR',      MON_LIMIT)
    await tb.write_reg('MON_GROUP_FLUSH_WATERMARK', MON_WMARK)
    await tb.write_reg('MON_GROUP_ERR_BASE_ADDR',       MON_ERR_BASE)
    await tb.write_reg('MON_GROUP_ERR_LIMIT_ADDR',      MON_ERR_LIMIT)
    await tb.write_reg('MON_GROUP_ERR_FLUSH_WATERMARK', MON_ERR_WMARK)
    await ClockCycles(dut.aclk, 5)

    # Attach the shared harness to the stream monbus group and consume the
    # master-write trace (top-level m_axil_mon_* ports). The fifo-count probes
    # need the group instance node, which lives inside a generate block that
    # may not be reachable from cocotb -- resolve it best-effort; the trace
    # decode (the core check) uses only top-level ports either way.
    group_node = None
    for path in ("g_monbus_axil",):
        try:
            group_node = getattr(dut, path).u_monbus_axil_group
            break
        except AttributeError:
            continue
    if group_node is None:
        tb.log.info("group instance not reachable; fifo-count probes disabled")
    mon = MonbusGroupHarness(
        dut, dut.aclk,
        # The write-only group has no drain port: error records land in the
        # error window through the one 64-bit master-write port (m_axil_mon_*)
        # and are lifted out of the captured writes by parse_err_records().
        drain_proto=None, trace_proto="axil",
        drain_prefix="", trace_prefix="m_axil_mon_",
        group_node=group_node,
        irq_sig=dut.stream_irq,
        err_window=(MON_ERR_BASE, MON_ERR_LIMIT),
        # Per docs/markdown/rtl-amba/includes/ocelus_package_spec.md both
        # windows carry raw records as beat0={tag,source_ts[59:0]},
        # beat1=packet[127:64], beat2=packet[63:0] -- TS_HI_LO.
        layout_trace=BeatLayout(order=BeatOrder.TS_HI_LO),
        log=tb.log,
    )
    async def drive_transfer(ch):
        """One descriptor transfer on channel ch -> desc/rd/wr AXI activity.
        Per-channel strides stay inside the data memory models (4 MB at
        DATA_WIDTH=64) and the configured 64 KB descriptor window."""
        src = tb.src_mem_base + (ch * 0x10000)
        dst = tb.dst_mem_base + (ch * 0x10000)
        desc_addr = tb.desc_mem_base + (ch * 0x1000)
        for beat in range(transfer_size):
            word = int.from_bytes(bytes([beat & 0xFF] * tb.data_bytes), 'little')
            tb.write_source_data(src + beat * tb.data_bytes, word, tb.data_bytes)
        tb.write_descriptor(addr=desc_addr, src_addr=src, dst_addr=dst,
                            length=transfer_size, next_ptr=0, priority=0,
                            last=True, interrupt=True)
        await tb.kick_off_channel(ch, desc_addr)
        await tb.wait_for_channel_idle(ch, timeout_us=400)
        assert tb.verify_transfer(src, dst, transfer_size), f"ch{ch} data mismatch"

    def err_fifo_beats():
        """Error writer FIFO occupancy in BEATS (three per record) via the
        top-level internal net -- the group instance node may not be
        reachable from cocotb."""
        try:
            return int(dut.mon_err_fifo_count.value)
        except (AttributeError, ValueError):
            return None

    def err_rec_count():
        """The group's free-running count of whole error records landed."""
        try:
            return int(dut.mon_err_rec_count.value)
        except (AttributeError, ValueError):
            return None

    def write_fifo_beats():
        try:
            return int(dut.mon_write_fifo_count.value)
        except (AttributeError, ValueError):
            return None

    async def settle_writers(max_rounds: int = 400):
        """Wait until both writers' FIFOs are empty and no new beat has been
        captured for 100 cycles."""
        last = -1
        for _ in range(max_rounds):
            await ClockCycles(dut.aclk, 100)
            n = len(mon.trace_beats)
            if (err_fifo_beats() or 0) == 0 and (write_fifo_beats() or 0) == 0 and n == last:
                return
            last = n

    # ----- Phase A: trace path (completions stream out m_axil_mon_*) -----
    tb.log.info("=== Phase A: monbus group trace path (completions) ===")
    for reg in MON_ERR_CFG_REGS:
        await tb.write_reg(reg, ERR_CFG_NONE)   # nothing routed to the error window
    mon.start_trace_consumer()
    await drive_transfer(0)
    await ClockCycles(dut.aclk, 4000)
    # The trace writer flushes on its own; wait until it has nothing left and
    # the captured beat count stands still, so Phase B does not inherit the
    # tail of this phase's records. The consumer keeps running across phases.
    await settle_writers()
    pkts = mon.parse_trace_records()
    st = mon.get_stats()
    tb.log.info(f"[stream-monbus] trace beats={st.trace_beats} pkts={len(pkts)} "
                f"types={sorted({p.get_packet_type_name() for p in pkts})} "
                f"units={sorted({p.unit_id for p in pkts})} "
                f"protocols={sorted({int(p.protocol) for p in pkts})}")
    assert len(pkts) > 0, "no monbus records flushed from the stream group trace path"
    assert len(pkts) == st.trace_beats // 3, "trace beats did not decode cleanly"
    assert any(p.packet_type == PktType.PktTypeCompletion for p in pkts), (
        f"no completion packets; got {sorted({p.get_packet_type_name() for p in pkts})}")
    tb.log.info("Phase A: trace path verified")

    # ----- Phase B: error window + IRQ (completions routed to the error path) -----
    # Route completion packets to the error path (ERR_SELECT=0x2). The group
    # writes each as a raw 3-beat record into the error window, pulses
    # stream_irq once per whole record landed (all three B responses back)
    # and counts it in err_rec_count / MON_ERR_REC_COUNT. The records come
    # back out of the captured writes and must decode as AXI completions;
    # the trace window must hold none of them.
    tb.log.info("=== Phase B: error window + stream_irq ===")
    for reg in MON_ERR_CFG_REGS:
        await tb.write_reg(reg, ERR_CFG_ROUTE_COMPL)   # completions -> error window
    mon.clear()
    mon.start_irq_watch()
    await drive_transfer(1)
    # Let the error writer land every record (its FIFO drains to memory on
    # its own; the flush watermark is one record) and the trace writer finish.
    await settle_writers()
    mon.stop_trace_consumer()
    mon.stop_irq_watch()
    err_pkts = mon.parse_err_records()
    trace_pkts = mon.parse_trace_records()
    st = mon.get_stats()
    landed = err_rec_count()
    irq_live = int(dut.stream_irq.value)
    tb.log.info(f"[stream-monbus] error-window records={len(err_pkts)} "
                f"err_rec_count={landed} irq_pulses={st.irq_rising_edges} "
                f"irq_first_cycle={mon.irq_first_cycle} irq_live={irq_live} "
                f"trace-window records={len(trace_pkts)} "
                f"err_fifo_beats_left={err_fifo_beats()} "
                f"types={sorted({p.get_packet_type_name() for p in err_pkts})} "
                f"protocols={sorted({int(p.protocol) for p in err_pkts})}")
    assert len(err_pkts) >= 1, "no records landed in the error window"
    assert all(p.packet_type == PktType.PktTypeCompletion for p in err_pkts), (
        f"non-completion in the error window: {sorted({p.get_packet_type_name() for p in err_pkts})}")
    # The per-monitor ERR_SELECT masks govern the group's AXI slot, so every
    # AXI-protocol completion must be in the error window; the schedulers' and
    # descriptor engines' own completions carry PROTOCOL_CORE, which no register
    # routes, and stay in the trace window by design.
    axi = 0   # ocelus_common_pkg PROTOCOL_AXI
    assert all(int(p.protocol) == axi for p in err_pkts), (
        f"non-AXI packet in the error window: protocols {sorted({int(p.protocol) for p in err_pkts})}")
    assert not any(p.packet_type == PktType.PktTypeCompletion and int(p.protocol) == axi for p in trace_pkts), (
        "an AXI completion routed to the error path also appeared in the trace window")
    assert mon.irq_asserted, "stream_irq never pulsed with completions routed to the error window"
    assert st.irq_rising_edges == len(err_pkts), (
        f"stream_irq pulsed {st.irq_rising_edges} times for {len(err_pkts)} records (one pulse per record)")
    assert landed is None or landed == len(err_pkts) % 0x10000, (
        f"err_rec_count {landed} != {len(err_pkts)} records in the window")
    assert irq_live == 0, "stream_irq is a pulse per record; it must be low once the records have landed"
    assert (err_fifo_beats() or 0) == 0, "error writer FIFO did not drain to memory"
    # Every error-window beat sits on an 8-byte step inside the window, in
    # write order, wrapping to base past the last whole record.
    err_beats = [a for (a, _d) in mon.trace_beats if MON_ERR_BASE <= a <= MON_ERR_LIMIT]
    window_recs = ((MON_ERR_LIMIT + 1 - MON_ERR_BASE) // 8) // 3
    for k, addr in enumerate(err_beats):
        rec, slot = divmod(k, 3)
        expected = MON_ERR_BASE + ((rec % window_recs) * 3 + slot) * 8
        assert addr == expected, f"error-window beat {k}: addr 0x{addr:08x}, expected 0x{expected:08x}"
    tb.log.info("=== stream_top monbus-group trace + error-window/IRQ paths verified ===")


def _monbus_timing_profiles():
    """Modest AXI timing-profile sweep for the monbus-group top test
    (assertion-heavy / slow, so kept small). 'fixed' is the baseline."""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return ['fixed']
    if reg == 'FUNC':
        return ['fixed', 'mixed']
    return ['fixed', 'mixed', 'slow_producer']


@pytest.mark.parametrize("timing_profile", _monbus_timing_profiles())
def test_stream_top_monbus(request, timing_profile, test_level):
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/stream_top',
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })
    dut_name = "stream_top_ch8"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/dma-ip/stream/rtl/filelists/top/stream_top_ch8.f')

    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '64'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': 64,
        'SRAM_DEPTH': fifo_depth,
        'APB_ADDR_WIDTH': 13,    # 8KB space so monitor block @ 0x1000+ is addressable
        'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': 1,   # enable the monbus group under test
        'CDC_ENABLE': 0,
    }

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    test_name = f"test_{dut_name}_monbus_{timing_profile}" + (f"_{worker_id}" if worker_id else "")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        # Per-cell depth. The grid above is already REG_LEVEL-selected by
        # _monbus_timing_profiles(); this is the other half of the contract.
        'TEST_LEVEL': test_level,
        'NUM_CHANNELS': str(num_channels), 'DATA_WIDTH': str(data_width),
        'FIFO_DEPTH': str(fifo_depth), 'DUT': dut_name, 'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'TIMING_PROFILE': timing_profile,
    }
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    compile_args = ["-Wno-fatal", "-Werror-MULTIDRIVEN", "--timescale", "1ns/1ps",
                    "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
                    "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN",
                    FIELD_COMBO_VLT,
                    # Monitor transaction tables do delayed array assignment in
                    # per-slot loops; Verilator must unroll them (BLKLOOPINIT) or
                    # a clean build fails. Matches the AMBA-guide sim note.
                    "--unroll-count", "4096", "--unroll-stmts", "20000"]
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')
        compile_args = ["--trace", "--trace-structs", "--trace-depth", "99"] + compile_args
    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    from cocotb_test.simulator import run
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_stream_top_monbus",
        parameters=rtl_parameters,
        compile_args=compile_args,
        extra_env=extra_env,
        sim_build=sim_build,
        waves=enable_waves,
        keep_files=True,
    )
