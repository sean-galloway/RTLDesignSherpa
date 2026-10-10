# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean gallow
#
# Module: test_stream_tally_group_chain
# Purpose: integration test of the board record path:
#          monbus_axil4_axil4_group -> stream_tally_arbiter -> monbus_tally_axil
#
# Documentation: projects/fpga-systems/Genesys2/dma-ip/stream/rtl/stream_tally_arbiter.sv
# Subsystem: tests
#
# Author: sean galloway

"""Board record-path integration test (amba BUG-039).

The exact silicon datapath an observer record travels on the Genesys 2 obs
build: the observer's monbus group (AXIL master write, MAX_BURST_BEATS=1),
through the record-ingest arbiter (observer direct + idle bridge), into the
tally's rec_* port.  On the 2026-10-09 board bring-up of the pipelined
write FSM this chain delivered ZERO records while the observer write FIFO
sat full (96/96) -- this test exists to make that failure sim-reproducible
before any further board run.

Asserts the tally receives every offered beat exactly once and the records
reassemble (single producer, so consecutive triples are records).
"""

import os
import random

import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

BYTES_PER_RECORD = 3


def make_record(i):
    # monitor_packet_t: [127:124] pkt_type=1 (completion), [87:72] agent=0x10,
    # [63:0] data.  Beat layout out of the raw expander:
    #   beat0 = {tag, ts}   beat1 = packet[127:64]   beat2 = packet[63:0]
    pkt = ((1 & 0xF) << 124) | ((0x10 & 0xFFFF) << 72) \
        | ((0xBEEF0000 + i) & ((1 << 64) - 1))
    return (0x1000 + i, pkt)


class ChainTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut

    async def assert_reset(self):
        self.dut.axi_aresetn.value = 0

    async def deassert_reset(self):
        self.dut.axi_aresetn.value = 1

    async def setup(self):
        await self.start_clock('aclk', 10, 'ns')
        d = self.dut
        d.monbus_valid.value = 0
        d.monbus_packet.value = 0
        d.monbus_timestamp.value = 0
        d.cfg_base_addr.value = 0x0004_0000
        d.cfg_limit_addr.value = 0x0005_0000 - 1
        d.cfg_flush_watermark.value = 0          # flush as soon as 1 record lands
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)

    async def send_record(self, pkt: int, ts: int):
        d = self.dut
        d.monbus_packet.value = pkt
        d.monbus_timestamp.value = ts
        d.monbus_valid.value = 1
        while True:
            await ReadOnly()
            if int(d.monbus_ready.value) == 1:
                break
            await RisingEdge(d.aclk)
        await RisingEdge(d.aclk)
        d.monbus_valid.value = 0


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def group_chain_drains(dut):
    tb = ChainTB(dut)
    await tb.setup()

    n = 40
    golden = [make_record(i) for i in range(n)]
    if os.environ.get("CHAIN_PROBE"):
        core = dut.u_group.u_core
        async def _p():
            for cyc in range(20000):
                await ReadOnly()
                print(f"CHAIN cyc={cyc:3d} win={int(core.r_win_beats.value)} "
                      f"total={int(core.r_epoch_total.value)} "
                      f"cov={int(core.r_aw_cov_beats.value)} "
                      f"unsent={int(core.r_w_unsent_beats.value)} "
                      f"bsub={int(core.r_b_subs.value)} "
                      f"rem={int(core.r_w_rem_in_sub.value)} "
                      f"oscnt={int(core.r_os_count.value)} "
                      f"fifocnt={int(core.write_fifo_beat_count.value)} "
                      f"m_awv={int(dut.u_group.m_axil_awvalid.value)} "
                      f"m_awr={int(dut.u_group.m_axil_awready.value)} "
                      f"m_wv={int(dut.u_group.m_axil_wvalid.value)} "
                      f"m_wr={int(dut.u_group.m_axil_wready.value)} "
                      f"m_wd={int(dut.u_group.m_axil_wdata.value):#x} "
                      f"m_bv={int(dut.u_group.m_axil_bvalid.value)} "
                      f"m_br={int(dut.u_group.m_axil_bready.value)} "
                      f"arb_gr={int(dut.u_arb.r_gr_obs.value)} "
                      f"arb_taken={int(dut.u_arb.r_aw_taken.value)} "
                      f"arb_busy={int(dut.u_arb.r_busy.value)} "
                      f"t_wv={int(dut.u_arb.t_wvalid.value)} "
                      f"t_wr={int(dut.u_arb.t_wready.value)} "
                      f"t_wd={int(dut.u_arb.t_wdata.value):#x} "
                      f"t_bv={int(dut.u_arb.t_bvalid.value)} "
                      f"t_br={int(dut.u_arb.t_bready.value)} "
                      f"pend={int(dut.u_tally.r_b_pending.value)} "
                      f"beat={int(dut.u_tally.r_beat.value)} "
                      f"awskid_cnt={int(dut.u_group.u_axil_wr.aw_channel.count.value)} "
                      f"awskid_v={int(dut.u_group.u_axil_wr.aw_channel.rd_valid.value)} "
                      f"awskid_rdy={int(dut.u_group.u_axil_wr.aw_channel.wr_ready.value)}")
                await RisingEdge(dut.aclk)
        cocotb.start_soon(_p())
    # send in a burst coroutine so the group FIFO backs up like the board
    async def _send_all():
        for ts, pkt in golden:
            await tb.send_record(pkt, ts)
    sender = cocotb.start_soon(_send_all())

    beats = []
    while len(beats) < n * BYTES_PER_RECORD:
        await ReadOnly()
        bv = int(dut.u_arb.t_wvalid.value) and int(dut.u_arb.t_wready.value)
        bd = int(dut.u_arb.t_wdata.value)
        full = int(dut.u_group.write_fifo_full.value)
        await RisingEdge(dut.aclk)
        if bv:
            beats.append(bd)
        # the board-stall signature: FIFO full yet nothing ever drains
        assert not (full == 1 and not beats and
                    int(dut.u_group.write_fifo_count.value) >= 96), \
            "board stall reproduced: write FIFO full, zero beats delivered"
    await sender
    await tb.wait_clocks('aclk', 30)

    exp = []
    for ts, pkt in golden:
        exp.extend([ts & ((1 << 64) - 1), (pkt >> 64) & ((1 << 64) - 1),
                    pkt & ((1 << 64) - 1)])
    tb.log.info(f"[chain] delivered {len(beats)} beats, expected {len(exp)}")
    assert beats == exp, (
        f"tally beats {[hex(b) for b in beats]} != golden {[hex(b) for b in exp]}"
        f" -- board record path loses or duplicates beats")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def group_chain_sustained_rate(dut):
    """Continuous-drain rate check (amba BUG-039 forward work).

    Offer one record every 8 cycles (3 beats / 8 cycles = 0.375 beats/cycle,
    below the record path's 0.5 beats/cycle arbiter ceiling) and require the
    chain to keep up within a wall-cycle bound.  The drain-cycle writer
    quiesces at every flush boundary (every B credited + 5-cycle geometry
    re-settle before the next commit), costing ~12-13 cycles per single
    record at watermark 0 -- it falls behind and the bound trips.  A
    continuous (FSM-free) writer streams back-to-back and passes.
    """
    tb = ChainTB(dut)
    await tb.setup()

    n = 60
    offer_period = 8     # cycles per record -> 0.375 beats/cycle offered
    cap = n * offer_period + 120
    golden = [make_record(i) for i in range(n)]

    async def _send_all():
        for ts, pkt in golden:
            await tb.send_record(pkt, ts)
            await tb.wait_clocks('aclk', offer_period - 1)
    sender = cocotb.start_soon(_send_all())

    beats = []
    cycles = 0
    while len(beats) < n * BYTES_PER_RECORD and cycles < cap:
        await ReadOnly()
        bv = int(dut.u_arb.t_wvalid.value) and int(dut.u_arb.t_wready.value)
        bd = int(dut.u_arb.t_wdata.value)
        await RisingEdge(dut.aclk)
        cycles += 1
        if bv:
            beats.append(bd)
    await sender

    assert len(beats) == n * BYTES_PER_RECORD, (
        f"record path fell behind the offered rate: only {len(beats)}/"
        f"{n * BYTES_PER_RECORD} beats at the tally after {cycles} cycles "
        f"(offered one record every {offer_period} cycles, bound {cap}) -- "
        f"the writer quiesces between flush cycles instead of streaming")

    exp = []
    for ts, pkt in golden:
        exp.extend([ts & ((1 << 64) - 1), (pkt >> 64) & ((1 << 64) - 1),
                    pkt & ((1 << 64) - 1)])
    assert beats == exp, (
        f"tally beats {[hex(b) for b in beats]} != golden {[hex(b) for b in exp]}"
        f" -- board record path loses or duplicates beats")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def test_stream_tally_group_chain(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_axil4':    'rtl/amba/axil4/',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
        'rtl_includes': 'rtl/amba/includes',
    })

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    dut_name = "stream_tally_group_chain_dut"
    test_name = f"test_{worker_id}_{dut_name}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    wrapper = os.path.join(sim_build, f"{dut_name}.sv")
    with open(wrapper, "w") as f:
        f.write("""// Auto-generated DUT wrapper for test_stream_tally_group_chain.
`timescale 1ns / 1ps
module stream_tally_group_chain_dut (
    input logic aclk, axi_aresetn,
    input  logic        monbus_valid,
    output logic        monbus_ready,
    input  logic [127:0] monbus_packet,
    input  logic [63:0] monbus_timestamp,
    input  logic [31:0] cfg_base_addr,
    input  logic [31:0] cfg_limit_addr,
    input  logic [15:0] cfg_flush_watermark
);
    logic [31:0] m_awaddr; logic [2:0] m_awprot;
    logic m_awvalid, m_awready;
    logic [63:0] m_wdata; logic [7:0] m_wstrb;
    logic m_wvalid, m_wready;
    logic [1:0] m_bresp; logic m_bvalid, m_bready;

    logic [31:0] t_awaddr; logic [2:0] t_awprot;
    logic t_awvalid, t_awready;
    logic [63:0] t_wdata; logic [7:0] t_wstrb;
    logic t_wvalid, t_wready;
    logic [1:0] t_bresp; logic t_bvalid, t_bready;

    logic [63:0] mon_time_out;
    logic irq_out, err_fifo_full, write_fifo_full;
    logic [15:0] err_fifo_count, write_fifo_count;
    logic [31:0] comp_t1a, comp_t1b, comp_t1c, comp_t0, comp_miss,
                 comp_dovf, comp_eovf, comp_edovf;

    monbus_axil4_axil4_group #(
        .FIFO_DEPTH_ERR(64), .FIFO_DEPTH_WRITE(96), .ADDR_WIDTH(32),
        .FLUSH_TIMEOUT_CYCLES(64), .USE_COMPRESSION(0)
    ) u_group (
        .axi_aclk(aclk), .axi_aresetn(axi_aresetn),
        .cam_clear(1'b0),
        .monbus_valid(monbus_valid), .monbus_ready(monbus_ready),
        .monbus_packet(monbus_packet), .monbus_timestamp(monbus_timestamp),
        .mon_time_out(mon_time_out),
        .s_axil_arvalid(1'b0), .s_axil_arready(),
        .s_axil_araddr(32'd0), .s_axil_arprot(3'd0),
        .s_axil_rvalid(), .s_axil_rready(1'b0),
        .s_axil_rdata(), .s_axil_rresp(),
        .m_axil_awvalid(m_awvalid), .m_axil_awready(m_awready),
        .m_axil_awaddr(m_awaddr), .m_axil_awprot(m_awprot),
        .m_axil_wvalid(m_wvalid), .m_axil_wready(m_wready),
        .m_axil_wdata(m_wdata), .m_axil_wstrb(m_wstrb),
        .m_axil_bresp(m_bresp), .m_axil_bvalid(m_bvalid),
        .m_axil_bready(m_bready),
        .irq_out(irq_out),
        .cfg_base_addr(cfg_base_addr), .cfg_limit_addr(cfg_limit_addr),
        .cfg_flush_watermark(cfg_flush_watermark),
        .cfg_compress_en(1'b0),
        .cfg_axi_pkt_mask(16'd0), .cfg_axi_err_select(16'd0),
        .cfg_axi_error_mask(16'd0), .cfg_axi_timeout_mask(16'd0),
        .cfg_axi_compl_mask(16'd0), .cfg_axi_thresh_mask(16'd0),
        .cfg_axi_perf_mask(16'd0), .cfg_axi_addr_mask(16'd0),
        .cfg_axi_debug_mask(16'd0),
        .cfg_axis_pkt_mask(16'd0), .cfg_axis_err_select(16'd0),
        .cfg_axis_error_mask(16'd0), .cfg_axis_timeout_mask(16'd0),
        .cfg_axis_compl_mask(16'd0), .cfg_axis_credit_mask(16'd0),
        .cfg_axis_channel_mask(16'd0), .cfg_axis_stream_mask(16'd0),
        .cfg_core_pkt_mask(16'd0), .cfg_core_err_select(16'd0),
        .cfg_core_error_mask(16'd0), .cfg_core_timeout_mask(16'd0),
        .cfg_core_compl_mask(16'd0), .cfg_core_thresh_mask(16'd0),
        .cfg_core_perf_mask(16'd0), .cfg_core_debug_mask(16'd0),
        .err_fifo_full(err_fifo_full), .write_fifo_full(write_fifo_full),
        .err_fifo_count(err_fifo_count), .write_fifo_count(write_fifo_count),
        .mon_compressor_stat_tier1_a(comp_t1a),
        .mon_compressor_stat_tier1_b(comp_t1b),
        .mon_compressor_stat_tier1_c(comp_t1c),
        .mon_compressor_stat_tier0(comp_t0),
        .mon_compressor_stat_cam_miss(comp_miss),
        .mon_compressor_stat_delta_ts_ovf(comp_dovf),
        .mon_compressor_stat_event_data_ovf(comp_eovf),
        .mon_compressor_stat_ed_delta_ovf(comp_edovf)
    );

    stream_tally_arbiter #(.ADDR_WIDTH(32), .DATA_WIDTH(64)) u_arb (
        .aclk(aclk), .aresetn(axi_aresetn),
        .obs_awaddr(m_awaddr), .obs_awprot(m_awprot),
        .obs_awvalid(m_awvalid), .obs_awready(m_awready),
        .obs_wdata(m_wdata), .obs_wstrb(m_wstrb),
        .obs_wvalid(m_wvalid), .obs_wready(m_wready),
        .obs_bresp(m_bresp), .obs_bvalid(m_bvalid), .obs_bready(m_bready),
        .br_awaddr(32'd0), .br_awprot(3'd0),
        .br_awvalid(1'b0), .br_awready(),
        .br_wdata(64'd0), .br_wstrb(8'd0),
        .br_wvalid(1'b0), .br_wready(),
        .br_bresp(), .br_bvalid(), .br_bready(1'b0),
        .t_awaddr(t_awaddr), .t_awprot(t_awprot),
        .t_awvalid(t_awvalid), .t_awready(t_awready),
        .t_wdata(t_wdata), .t_wstrb(t_wstrb),
        .t_wvalid(t_wvalid), .t_wready(t_wready),
        .t_bresp(t_bresp), .t_bvalid(t_bvalid), .t_bready(t_bready)
    );

    monbus_tally_axil #(
        .ADDR_WIDTH(32), .DATA_WIDTH(64),
        .TALLY_ADDR_BITS(4), .N_PROFILE(8)
    ) u_tally (
        .aclk(aclk), .aresetn(axi_aresetn),
        .rec_awaddr(t_awaddr), .rec_awprot(t_awprot),
        .rec_awvalid(t_awvalid), .rec_awready(t_awready),
        .rec_wdata(t_wdata), .rec_wstrb(t_wstrb),
        .rec_wvalid(t_wvalid), .rec_wready(t_wready),
        .rec_bresp(t_bresp), .rec_bvalid(t_bvalid), .rec_bready(t_bready),
        .cnt_araddr(32'd0), .cnt_arprot(3'd0),
        .cnt_arvalid(1'b0), .cnt_arready(),
        .cnt_rdata(), .cnt_rresp(), .cnt_rvalid(), .cnt_rready(1'b0),
        .cfgw_awaddr(32'd0), .cfgw_awprot(3'd0),
        .cfgw_awvalid(1'b0), .cfgw_awready(),
        .cfgw_wdata(64'd0), .cfgw_wstrb(8'd0),
        .cfgw_wvalid(1'b0), .cfgw_wready(),
        .cfgw_bresp(), .cfgw_bvalid(), .cfgw_bready(1'b0),
        .cfgr_araddr(32'd0), .cfgr_arprot(3'd0),
        .cfgr_arvalid(1'b0), .cfgr_arready(),
        .cfgr_rdata(), .cfgr_rresp(), .cfgr_rvalid(), .cfgr_rready(1'b0),
        .tally_freeze(1'b0), .tally_flush(1'b0), .tally_flush_busy(),
        .tally_clear(1'b0)
    );
endmodule
""")

    verilog_sources = [
        os.path.join(repo_root,
                     "projects/fpga-systems/Genesys2/dma-ip/stream/rtl/"
                     "stream_tally_arbiter.sv"),
        wrapper,
    ]
    group_src, group_incs = get_sources_from_filelist(
        repo_root=repo_root, module='monbus_axil4_axil4_group')
    tally_src, _ = get_sources_from_filelist(
        repo_root=repo_root, module='monbus_pkt_tally')
    tally_src += [
        os.path.join(repo_root, p) for p in (
            "rtl/amba/includes/monitor_common_pkg.sv",
            "projects/components/utility-ip/misc/rtl/regs/generated/rtl/tally_regs_top_pkg.sv",
            "projects/components/utility-ip/misc/rtl/regs/generated/rtl/tally_regs_top.sv",
            "projects/components/utility-ip/misc/rtl/monbus_tally_axil.sv",
        )]
    seen = set(verilog_sources)
    for s in group_src + tally_src:
        if s not in seen:
            seen.add(s)
            verilog_sources.append(s)
    includes = group_incs

    extra_env = {
        'DUT':                 dut_name,
        'LOG_PATH':            log_path,
        'COCOTB_LOG_LEVEL':    'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name}.xml'),
        'SEED':                os.environ.get('SEED', str(random.randint(0, 100000))),
    }

    compile_args = [
        '+define+SIMULATION',
        '--trace-fst', '--trace-structs',
        '-Wno-DECLFILENAME', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC',
        '-Wno-UNUSEDPARAM', '-Wno-TIMESCALEMOD', '-Wno-UNUSEDSIGNAL',
        '-Wno-MULTIDRIVEN',
    ]

    create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=enable_waves,
        keep_files=True,
        compile_args=compile_args,
    )
