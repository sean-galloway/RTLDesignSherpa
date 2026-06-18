#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Monbus-group coverage for stream_top_ch8 (USE_AXI_MONITORS=1).
#
# stream_top_ch8 contains a monbus_axil_axil_group (u_monbus_axil_group) that
# the existing stream_top tests never exercise (they build with monitors off
# and only sniff the raw pre-group mon bus). This test enables the AXI monitors
# via CSR, drives a real descriptor transfer so the desc/rd/wr monitors emit
# completion packets, and attaches the shared MonbusGroupHarness to the group's
# master-write (trace) port -- the same collateral used by the bridge + val/amba
# monbus-group tests. It proves the stream monbus group flushes records that
# decode as AXI completion packets.

import os
import sys

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from projects.components.stream.dv.tbclasses.stream_core_tb import StreamCoreTB
from TBClasses.monbus import PktType, ProtocolType
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

# Monbus-group flush window (top-level cfg_mon_* inputs on stream_top_ch8).
MON_BASE  = 0x0000_1000
MON_LIMIT = 0x0000_5000 - 1
MON_WMARK = 3           # one raw record = 3 beats -> flush eagerly


@cocotb.test(timeout_time=2000, timeout_unit="us")
async def cocotb_test_stream_top_monbus(dut):
    num_channels = int(os.environ.get('NUM_CHANNELS', '2'))
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
        group_node=group_node,
        irq_sig=dut.stream_irq,
        layout_drain=BeatLayout(order=BeatOrder.LO_HI_TS),
        layout_trace=BeatLayout(order=BeatOrder.LO_HI_TS),
        log=tb.log,
    )
    mon.start_fifo_monitor()
    mon.start_trace_consumer()

    # Drive one descriptor transfer on channel 0 -> desc/rd/wr AXI activity.
    channel = 0
    src = tb.src_mem_base + (channel * 0x400000)
    dst = tb.dst_mem_base + (channel * 0x400000)
    desc_addr = tb.desc_mem_base + (channel * 0x10000)
    for beat in range(transfer_size):
        pat = (beat & 0xFF)
        word = int.from_bytes(bytes([pat] * tb.data_bytes), 'little')
        tb.write_source_data(src + beat * tb.data_bytes, word, tb.data_bytes)
    tb.write_descriptor(addr=desc_addr, src_addr=src, dst_addr=dst,
                        length=transfer_size, next_ptr=0, priority=0,
                        last=True, interrupt=True)
    await tb.kick_off_channel(channel, desc_addr)
    await tb.wait_for_channel_idle(channel, timeout_us=400)
    assert tb.verify_transfer(src, dst, transfer_size), "stream data transfer mismatch"

    # Let the monbus group flush the buffered records out the trace path.
    await ClockCycles(dut.aclk, 4000)
    mon.stop_trace_consumer()
    mon.stop_fifo_monitor()
    pkts = mon.parse_trace_records()
    st = mon.get_stats()
    tb.log.info(f"[stream-monbus] trace_beats={st.trace_beats} pkts={len(pkts)} "
                f"max_wr={st.max_write_fifo_count} "
                f"types={sorted({p.get_packet_type_name() for p in pkts})} "
                f"units={sorted({p.unit_id for p in pkts})}")

    # stream monitors reuse protocol slots (desc=AXI, rd=AXIS, wr=CORE), so the
    # captured packets carry mixed protocol ids -- record them rather than
    # requiring one protocol. The proof is that the group's trace path flushes
    # records that decode cleanly as completion packets.
    tb.log.info(f"[stream-monbus] protocols seen: {sorted({int(p.protocol) for p in pkts})}")
    assert len(pkts) > 0, "no monbus records flushed from the stream group trace path"
    assert len(pkts) == st.trace_beats // 3, "trace beats did not decode cleanly"
    assert any(p.packet_type == PktType.PktTypeCompletion for p in pkts), (
        f"no completion packets; got {sorted({p.get_packet_type_name() for p in pkts})}")
    tb.log.info("=== stream_top monbus-group trace path verified ===")


def test_stream_top_monbus(request):
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

    num_channels = int(os.environ.get('NUM_CHANNELS', '2'))
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
    test_name = f"test_{dut_name}_monbus" + (f"_{worker_id}" if worker_id else "")
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        'NUM_CHANNELS': str(num_channels), 'DATA_WIDTH': str(data_width),
        'FIFO_DEPTH': str(fifo_depth), 'DUT': dut_name, 'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO', 'COCOTB_RESULTS_FILE': results_path,
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
