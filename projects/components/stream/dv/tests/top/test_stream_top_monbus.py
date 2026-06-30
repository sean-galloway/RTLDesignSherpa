#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Monbus-group coverage for stream_top_ch8 (USE_AXI_MONITORS=1).
#
# stream_top_ch8 contains a monbus_axil_axil_group (u_monbus_axil_group) that
# the existing stream_top tests never exercise (they build with monitors off
# and only sniff the raw pre-group mon bus). This test enables the AXI monitors
# via CSR, drives real descriptor transfers, and attaches the shared
# MonbusGroupHarness to the group -- the same collateral used by the bridge +
# val/amba monbus-group tests. Two paths are covered:
#   Phase A -- master-write (trace) path: completion packets stream out
#              m_axil_mon_* and decode as AXI completions (24-byte records,
#              beat order {tag,ts}, pkt[127:64], pkt[63:0] per the monitor
#              package spec).
#   Phase B -- err FIFO + stream_irq: completion packets are routed to the err
#              FIFO via ERR_CFG.ERR_SELECT; the FIFO filling drives stream_irq,
#              and draining its records over the 32-bit s_axil_err_* port (the
#              group's S_AXIL_DATA_WIDTH=32 2:1 read serializer presents each
#              64-bit slice as two beats) clears the interrupt. The drained
#              packets must still decode as AXI completions, proving the 32-bit
#              drain preserves the full 128-bit packet.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB
from TBClasses.monbus import PktType
from TBClasses.scoreboards.monbus_group import (
    MonbusGroupHarness, BeatLayout, BeatOrder,
)

# Stream monitor-enable CSRs (stream_regs.rdl). Enable bits: MON_EN[0],
# ERR_EN[1], COMPL_EN[2] -> 0x7 turns on the monitor + error + completion
# reporting (COMPRESS_EN is a higher bit, left 0 = raw 3-beat records).
DAXMON_ENABLE = 0x240   # descriptor-fetch AXI monitor
RDMON_ENABLE  = 0x260   # data-read engine monitor
WRMON_ENABLE  = 0x280   # data-write engine monitor
MON_EN_VALUE  = 0x7
# Per-monitor packet-drop mask (PKT_MASK) resets to 0xFFFF (drop everything);
# clear to 0 so monitor packets actually flow into the group.
DAXMON_PKT_MASK = 0x24C
RDMON_PKT_MASK  = 0x26C
WRMON_PKT_MASK  = 0x28C
# Per-monitor ERR_CFG (stream_regs.rdl): ERR_SELECT[3:0] is a bitmask indexed
# by packet_type selecting which types divert to the err FIFO (bit0=Error,
# bit1=Completion, ...); ERR_MASK[15:8] reset 0xFF event-masks (drops) error
# packets. We route COMPLETIONS to the err FIFO (ERR_SELECT=0x2): every
# transfer emits completion packets deterministically, the per-protocol
# completion masks reset to 0 (not dropped), and ERR_MASK=0xFF keeps the
# incidental descriptor SLVERR errors out -- so the err FIFO fills cleanly
# with completions, which drives stream_irq (irq_out = !err_fifo_empty).
DAXMON_ERR_CFG = 0x250
RDMON_ERR_CFG  = 0x270
WRMON_ERR_CFG  = 0x290
ERR_CFG_ROUTE_COMPL = 0xFF02   # ERR_SELECT=0x2 (compl->err FIFO), ERR_MASK=0xFF
ERR_CFG_NONE        = 0xFF00   # ERR_SELECT=0 (nothing to err FIFO)
MON_FIFO_COUNT = 0x184

# Monbus-group flush window (top-level cfg_mon_* inputs on stream_top_ch8).
MON_BASE  = 0x0000_1000
MON_LIMIT = 0x0000_5000 - 1
MON_WMARK = 3           # one raw record = 3 beats -> flush eagerly


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
        apb_addr_width=12, apb_data_width=32,
    )
    await tb.setup_clocks_and_reset(rd_xfer_beats=rd_xfer_beats,
                                    wr_xfer_beats=wr_xfer_beats)
    await tb.init_apb_master()
    await tb.enable_global()
    await tb.enable_channel_mask((1 << num_channels) - 1)
    await tb.configure_transfer_beats(rd_xfer_beats=rd_xfer_beats,
                                      wr_xfer_beats=wr_xfer_beats)
    await tb.configure_descriptor_address_range()

    # Enable the three AXI monitors (monitor+error+completion) and clear their
    # packet-drop masks so clean traffic emits completion packets that stream
    # out the group's master-write (trace) path.
    for reg in (DAXMON_ENABLE, RDMON_ENABLE, WRMON_ENABLE):
        await tb.write_apb_register(reg, MON_EN_VALUE)
    for reg in (DAXMON_PKT_MASK, RDMON_PKT_MASK, WRMON_PKT_MASK):
        await tb.write_apb_register(reg, 0x0)

    # Program the group flush window (top-level inputs) so the master-write
    # path actually flushes (default 0/0 window stalls the writer).
    dut.cfg_mon_base_addr.value = MON_BASE
    dut.cfg_mon_limit_addr.value = MON_LIMIT
    dut.cfg_mon_flush_watermark.value = MON_WMARK
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
        drain_proto="axil", trace_proto="axil",
        drain_prefix="s_axil_err_", trace_prefix="m_axil_mon_",
        # stream_top_ch8 wires the group with S_AXIL_DATA_WIDTH=32: the err
        # drain (s_axil_err_*) is a 32-bit AXIL port whose 2:1 read serializer
        # presents each 64-bit record slice as two beats (6 beats/record). The
        # trace (m_axil_mon_*) stays 64-bit.
        drain_data_width=32,
        group_node=group_node,
        irq_sig=dut.stream_irq,
        # Per docs/markdown/RTLAmba/includes/monitor_package_spec.md the group
        # emits BOTH the bulk-trace (m_mon_axil) AND the single-record drain
        # (s_mon_axil) as: beat0={tag,source_ts[59:0]}, beat1=packet[127:64],
        # beat2=packet[63:0] -- i.e. TS_HI_LO on both ports.
        layout_drain=BeatLayout(order=BeatOrder.TS_HI_LO),
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

    def err_fifo_records():
        """Err-FIFO occupancy in RECORDS (group_core err_fifo_count is records,
        not beats) via the top-level internal net -- the group instance node
        isn't reachable from cocotb."""
        try:
            return int(dut.mon_err_fifo_count.value)
        except (AttributeError, ValueError):
            return None

    # ----- Phase A: trace path (completions stream out m_axil_mon_*) -----
    tb.log.info("=== Phase A: monbus group trace path (completions) ===")
    for reg in (DAXMON_ERR_CFG, RDMON_ERR_CFG, WRMON_ERR_CFG):
        await tb.write_apb_register(reg, ERR_CFG_NONE)   # nothing routed to err FIFO
    mon.start_trace_consumer()
    await drive_transfer(0)
    await ClockCycles(dut.aclk, 4000)
    mon.stop_trace_consumer()
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

    # ----- Phase B: err FIFO + IRQ (completions routed to the err FIFO) -----
    # Route completion packets to the err FIFO (ERR_SELECT=0x2). The FIFO
    # filling drives stream_irq (irq_out = !err_fifo_empty); draining its
    # records over the 32-bit s_axil_err_* port (2:1 read serializer ->
    # 6 beats/record, recombined by the harness) clears the interrupt and
    # the drained packets must decode back as AXI completions -- proving the
    # 32-bit drain preserves the full 128-bit packet (a naive 32-bit truncation
    # would drop packet_type at bit 127).
    tb.log.info("=== Phase B: err FIFO + stream_irq ===")
    for reg in (DAXMON_ERR_CFG, RDMON_ERR_CFG, WRMON_ERR_CFG):
        await tb.write_apb_register(reg, ERR_CFG_ROUTE_COMPL)   # completions -> err FIFO
    mon.clear()
    mon.start_irq_watch()
    await drive_transfer(1)
    await ClockCycles(dut.aclk, 50)

    records = err_fifo_records()
    irq_live = int(dut.stream_irq.value)
    tb.log.info(f"[stream-monbus] err FIFO records={records} "
                f"stream_irq={irq_live} irq_first_cycle={mon.irq_first_cycle}")
    assert mon.irq_asserted, "stream_irq never asserted with completions routed to err FIFO"
    assert records and records > 0, "err FIFO empty despite IRQ"

    # Drain every record over the 32-bit port, then confirm the IRQ de-asserts
    # now that the err FIFO is empty.
    drained = await mon.drain_records(records)
    await ClockCycles(dut.aclk, 20)
    irq_after = int(dut.stream_irq.value)
    mon.stop_irq_watch()
    tb.log.info(f"[stream-monbus] err-drained pkts={len(drained)} "
                f"types={sorted({p.get_packet_type_name() for p in drained})} "
                f"protocols={sorted({int(p.protocol) for p in drained})} "
                f"irq_after_drain={irq_after} final_err_records={err_fifo_records()}")
    assert len(drained) >= 1, "no records drained from the err FIFO"
    assert all(p.packet_type == PktType.PktTypeCompletion for p in drained), (
        f"non-completion in err FIFO: {sorted({p.get_packet_type_name() for p in drained})}")
    assert irq_after == 0, "stream_irq did not clear after draining the err FIFO"
    mon.stop_fifo_monitor()
    tb.log.info("=== stream_top monbus-group trace + err-FIFO/IRQ paths verified ===")


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
def test_stream_top_monbus(request, timing_profile):
    module, repo_root_, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_top': '../../../../rtl/stream_top',
        'rtl_stream_macro': '../../../../rtl/stream_macro',
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_amba': '../../../../../rtl/amba',
    })
    dut_name = "stream_top_ch8"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/stream/rtl/filelists/top/stream_top_ch8.f')
    # stream_top_ch8.f omits axil4_slave_rd.sv (it normally comes from the
    # parent stream_char_harness.f). The monbus group's err-FIFO read leaf
    # needs it when building stream_top_ch8 standalone with USE_AXI_MONITORS=1.
    verilog_sources = list(verilog_sources) + [
        os.path.join(repo_root_, 'rtl/amba/axil4/axil4_slave_rd.sv')]

    num_channels = int(os.environ.get('NUM_CHANNELS', '8'))
    data_width = int(os.environ.get('DATA_WIDTH', '64'))
    fifo_depth = int(os.environ.get('FIFO_DEPTH', '512'))
    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': data_width,
        'ADDR_WIDTH': 64,
        'SRAM_DEPTH': fifo_depth,
        'APB_ADDR_WIDTH': 12,
        'APB_DATA_WIDTH': 32,
        'USE_AXI_MONITORS': 1,   # enable the monbus group under test
        'CDC_ENABLE': 0,
    }

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    test_name = f"test_{dut_name}_monbus_{timing_profile}" + (f"_{worker_id}" if worker_id else "")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'NUM_CHANNELS': str(num_channels), 'DATA_WIDTH': str(data_width),
        'FIFO_DEPTH': str(fifo_depth), 'DUT': dut_name, 'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
        'TIMING_PROFILE': timing_profile,
    }
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    compile_args = ["-Wno-fatal", "--timescale", "1ns/1ps",
                    "-Wno-WIDTH", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
                    "-Wno-SELRANGE", "-Wno-UNUSEDSIGNAL", "-Wno-UNDRIVEN",
                    "-Wno-MULTIDRIVEN"]
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
