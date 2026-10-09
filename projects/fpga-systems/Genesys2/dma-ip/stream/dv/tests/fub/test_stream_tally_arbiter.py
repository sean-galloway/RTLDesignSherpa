# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_stream_tally_arbiter
# Purpose: unit test for the stream harness's record-ingest arbiter
#
# Documentation: projects/fpga-systems/Genesys2/dma-ip/stream/rtl/stream_tally_arbiter.sv
# Subsystem: tests
#
# Author: sean galloway

"""Unit test for stream_tally_arbiter against the REAL monbus_tally_axil.

Board history (amba BUG-039, 2026-10-09): this arbiter first shipped
ungated on the valid side, and the tally's rec port (awready=1, beats 0/1
wready=1) phantom-consumed beats waiting in the observer's leaf skid during
the idle cycle between transfers -- the skid did not pop, and the tally
delivered the SAME beat again under the next grant (record reassembly
captured as packet.hi == packet.lo, then every following record shifted).
A grant-gated mux fixed the phantom but the granted path then stalled on the
board (observer write FIFO 96/96 full, zero records counted).  This test
reproduces the exact silicon chain -- a PIPELINED master presenting AW
continuously and W beats back-to-back (what the monbus group write FSM now
does), through the arbiter, into the real tally -- and asserts:

  * every offered beat is delivered to the tally EXACTLY ONCE, in order
    (a duplicated beat desyncs the tally's mod-3 record reassembler);
  * the master fully drains (the board stall signature is beats stuck in
    the master forever);
  * bridge-side transfers interleave without corrupting either stream.

The test fails on both historical defects and passes on the fixed arbiter.
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
AW = 32
DW = 64


def make_record(i):
    ts = 0x1000 + i
    hi = (0xDEAD0000 + i * 2) & ((1 << 64) - 1)
    lo = (0xBEEF0000 + i * 2 + 1) & ((1 << 64) - 1)
    return [ts, hi, lo]


class ArbiterTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup(self):
        await self.start_clock('aclk', 10, 'ns')
        for sig, val in (
            ('obs_awaddr', 0), ('obs_awprot', 0), ('obs_awvalid', 0),
            ('obs_wdata', 0), ('obs_wstrb', 0), ('obs_wvalid', 0),
            ('obs_bready', 1),
            ('br_awaddr', 0), ('br_awprot', 0), ('br_awvalid', 0),
            ('br_wdata', 0), ('br_wstrb', 0), ('br_wvalid', 0),
            ('br_bready', 1),
        ):
            getattr(self.dut, sig).value = val
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)


async def _drive_master(dut, prefix, records, start_delay=0):
    """PIPELINED AXIL master: one AW per W beat (MAX_BURST_BEATS=1, exactly
    what the monbus group + leaf skids present): awvalid and wvalid both
    held whenever there is something to send, bready held.  Models the
    group+leaf: the AW for beat k+1 is presented while beat k drains."""
    beats = []
    for rec in records:
        beats.extend(rec)
    total = len(beats)
    aw_sent = 0
    w_sent = 0
    b_seen = 0
    for _ in range(start_delay):
        await RisingEdge(dut.aclk)
    while b_seen < total or w_sent < total:
        await ReadOnly()
        aw_rdy = int(getattr(dut, f"{prefix}_awready").value)
        w_rdy = int(getattr(dut, f"{prefix}_wready").value)
        b_v = int(getattr(dut, f"{prefix}_bvalid").value)
        await RisingEdge(dut.aclk)
        if b_v:
            b_seen += 1
        if aw_sent < total:
            getattr(dut, f"{prefix}_awvalid").value = 1
            getattr(dut, f"{prefix}_awaddr").value = 0x40000 + aw_sent * 8
            if aw_rdy:
                aw_sent += 1
        else:
            getattr(dut, f"{prefix}_awvalid").value = 0
        if w_sent < total:
            getattr(dut, f"{prefix}_wvalid").value = 1
            getattr(dut, f"{prefix}_wstrb").value = (1 << (DW // 8)) - 1
            getattr(dut, f"{prefix}_wdata").value = beats[w_sent]
            if w_rdy:
                w_sent += 1
        else:
            getattr(dut, f"{prefix}_wvalid").value = 0
    getattr(dut, f"{prefix}_awvalid").value = 0
    getattr(dut, f"{prefix}_wvalid").value = 0


class TallyTap:
    """Watches the tally's rec_* beat handshakes (exactly-once delivery)."""

    def __init__(self, dut):
        self.dut = dut
        self.beats = []

    async def run(self):
        arb = self.dut.u_arb
        while True:
            await ReadOnly()
            v = int(arb.t_wvalid.value) and int(arb.t_wready.value)
            d = int(arb.t_wdata.value)
            await RisingEdge(self.dut.aclk)
            if v:
                self.beats.append(d)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def arbiter_pipelined_obs_only(dut):
    """Board repro: pipelined observer, idle bridge, real tally."""
    tb = ArbiterTB(dut)
    await tb.setup()
    tap = TallyTap(dut)
    cocotb.start_soon(tap.run())
    if os.environ.get("ARB_PROBE"):
        arb = dut.u_arb
        async def _p():
            for cyc in range(2000):
                await ReadOnly()
                print(f"ARB cyc={cyc:3d} gr_obs={int(arb.r_gr_obs.value)} "
                      f"gr_br={int(arb.r_gr_bridge.value)} busy={int(arb.r_busy.value)} "
                      f"obs_awv={int(dut.obs_awvalid.value)} obs_awr={int(dut.obs_awready.value)} "
                      f"obs_wv={int(dut.obs_wvalid.value)} obs_wr={int(dut.obs_wready.value)} "
                      f"t_wv={int(dut.u_arb.t_wvalid.value)} t_wr={int(dut.u_arb.t_wready.value)} "
                      f"t_bv={int(dut.u_arb.t_bvalid.value)} t_br={int(dut.u_arb.t_bready.value)} "
                      f"obs_bv={int(dut.obs_bvalid.value)} bqcnt={int(arb.r_bq_cnt.value)} "
                      f"bqrd={int(arb.r_bq_rd.value)} bqwr={int(arb.r_bq_wr.value)} "
                      f"pend={int(dut.u_tally.r_b_pending.value)} "
                      f"beat={int(dut.u_tally.r_beat.value)} in_ready={int(dut.u_tally.w_tally_in_ready.value)})")
                await RisingEdge(dut.aclk)
        cocotb.start_soon(_p())

    n = 40
    golden = [tuple(make_record(i)) for i in range(n)]
    driver = cocotb.start_soon(_drive_master(dut, "obs", golden))
    await driver
    await tb.wait_clocks('aclk', 50)

    got = tap.beats
    tb.log.info(f"[arbiter] delivered {len(got)} beats, expected {n * BYTES_PER_RECORD}")
    assert len(got) == n * BYTES_PER_RECORD, (
        f"tally received {len(got)} beats from {n * BYTES_PER_RECORD} offered -- "
        f"beats lost or duplicated (board signature: hi==lo records "
        f"or a stuck master)")
    # single master -> consecutive beat triples reassemble into records
    for i in range(n):
        rec = got[i * 3:(i + 1) * 3]
        assert rec == list(golden[i]), (
            f"record {i}: beats {[hex(b) for b in rec]} != golden "
            f"{[hex(b) for b in golden[i]]} -- beat duplicated or misaligned")


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def arbiter_interleaved_bridge(dut):
    """Both masters stream concurrently; each record stream must stay exact."""
    tb = ArbiterTB(dut)
    await tb.setup()
    tap = TallyTap(dut)
    cocotb.start_soon(tap.run())

    rng = random.Random(7)
    obs_golden = [tuple(make_record(i)) for i in range(20)]
    br_golden = [[0x5000 + i, 0xA5A50000 + i, 0x5A5A0000 + i] for i in range(8)]
    obs_drv = cocotb.start_soon(_drive_master(dut, "obs", obs_golden))
    br_drv = cocotb.start_soon(_drive_master(dut, "br", br_golden,
                                             start_delay=rng.randint(1, 5)))
    await obs_drv
    await br_drv
    await tb.wait_clocks('aclk', 50)

    got = tap.beats
    all_golden = [b for rec in obs_golden + br_golden for b in rec]
    tb.log.info(f"[arbiter interleave] delivered {len(got)} beats, "
                f"expected {len(all_golden)}")
    # Two masters sharing one rec port interleave at the BEAT level (the
    # tally's mod-3 reassembly is only meaningful per master; the harness
    # only ever runs one producer at a time).  The arbiter's contract:
    # every beat from both masters is delivered EXACTLY ONCE -- no loss, no
    # duplication (the phantom-beat defect would show up here as extras).
    assert len(got) == len(all_golden), (
        f"tally received {len(got)} beats from {len(all_golden)} offered -- "
        f"lost or duplicated across the arbiter")
    assert sorted(got) == sorted(all_golden), (
        "delivered beat set != golden beat set -- a beat was corrupted, "
        "duplicated, or lost across the arbiter")


# ----------------------------------------------------------------------------
# Pytest wrapper
# ----------------------------------------------------------------------------
def test_stream_tally_arbiter(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_monitor':  'rtl/amba/monitor',
        'rtl_axil4':    'rtl/amba/axil4/',
        'rtl_gaxi':     'rtl/amba/gaxi',
        'rtl_common':   'rtl/common',
        'rtl_includes': 'rtl/amba/includes',
    })

    # The DUT wrapper: arbiter + real tally, wired like the harness s4/s6.
    # Generated into the sim build dir so the tree stays clean.
    wrapper = os.path.join(sim_build_path(tests_dir,
                                          f"test_{os.environ.get('PYTEST_XDIST_WORKER', 'gw0')}"
                                          f"_stream_tally_arbiter_dut_build"),
                           "stream_tally_arbiter_dut.sv")
    dut_name = "stream_tally_arbiter_dut"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    test_name = f"test_{worker_id}_{dut_name}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    n_profile = 8
    tally_addr_bits = 4  # clog2(N_PROFILE+1)
    os.makedirs(os.path.dirname(wrapper), exist_ok=True)
    with open(wrapper, "w") as f:
        f.write(f"""// Auto-generated DUT wrapper for test_stream_tally_arbiter.
`timescale 1ns / 1ps
module stream_tally_arbiter_dut (
    input logic aclk, aresetn,
    input  logic [31:0] obs_awaddr, input logic [2:0] obs_awprot,
    input  logic obs_awvalid, output logic obs_awready,
    input  logic [63:0] obs_wdata, input logic [7:0] obs_wstrb,
    input  logic obs_wvalid, output logic obs_wready,
    output logic [1:0] obs_bresp, output logic obs_bvalid,
    input  logic obs_bready,
    input  logic [31:0] br_awaddr, input logic [2:0] br_awprot,
    input  logic br_awvalid, output logic br_awready,
    input  logic [63:0] br_wdata, input logic [7:0] br_wstrb,
    input  logic br_wvalid, output logic br_wready,
    output logic [1:0] br_bresp, output logic br_bvalid,
    input  logic br_bready
);
    logic [31:0] t_awaddr; logic [2:0] t_awprot;
    logic t_awvalid, t_awready;
    logic [63:0] t_wdata; logic [7:0] t_wstrb;
    logic t_wvalid, t_wready;
    logic [1:0] t_bresp; logic t_bvalid, t_bready;

    stream_tally_arbiter #(.ADDR_WIDTH(32), .DATA_WIDTH(64)) u_arb (
        .aclk(aclk), .aresetn(aresetn),
        .obs_awaddr(obs_awaddr), .obs_awprot(obs_awprot),
        .obs_awvalid(obs_awvalid), .obs_awready(obs_awready),
        .obs_wdata(obs_wdata), .obs_wstrb(obs_wstrb),
        .obs_wvalid(obs_wvalid), .obs_wready(obs_wready),
        .obs_bresp(obs_bresp), .obs_bvalid(obs_bvalid),
        .obs_bready(obs_bready),
        .br_awaddr(br_awaddr), .br_awprot(br_awprot),
        .br_awvalid(br_awvalid), .br_awready(br_awready),
        .br_wdata(br_wdata), .br_wstrb(br_wstrb),
        .br_wvalid(br_wvalid), .br_wready(br_wready),
        .br_bresp(br_bresp), .br_bvalid(br_bvalid), .br_bready(br_bready),
        .t_awaddr(t_awaddr), .t_awprot(t_awprot),
        .t_awvalid(t_awvalid), .t_awready(t_awready),
        .t_wdata(t_wdata), .t_wstrb(t_wstrb),
        .t_wvalid(t_wvalid), .t_wready(t_wready),
        .t_bresp(t_bresp), .t_bvalid(t_bvalid), .t_bready(t_bready)
    );

    monbus_tally_axil #(
        .ADDR_WIDTH(32), .DATA_WIDTH(64),
        .TALLY_ADDR_BITS({tally_addr_bits}), .N_PROFILE({n_profile})
    ) u_tally (
        .aclk(aclk), .aresetn(aresetn),
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
    tally_src, _ = get_sources_from_filelist(
        repo_root=repo_root, module='monbus_pkt_tally')
    tally_src += [
        os.path.join(repo_root, p) for p in (
            "rtl/amba/includes/monitor_common_pkg.sv",
            "projects/components/utility-ip/misc/rtl/regs/generated/rtl/tally_regs_top_pkg.sv",
            "projects/components/utility-ip/misc/rtl/regs/generated/rtl/tally_regs_top.sv",
            "projects/components/utility-ip/misc/rtl/monbus_tally_axil.sv",
        )]
    amba_deps, amba_incs = get_sources_from_filelist(
        repo_root=repo_root, module='axil4_master_wr')
    verilog_sources += [s for s in (tally_src + amba_deps)
                        if s not in verilog_sources]
    includes = amba_incs

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
