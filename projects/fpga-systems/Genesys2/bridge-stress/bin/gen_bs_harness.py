#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the bridge stress harness for one DUT bridge TOML.

The harness is everything around the device under test: the UART host link
and configuration bridge, the control regblock, and one stress master per
DUT master port and one stress slave per DUT slave port, each the protocol
shell matching that port and each with its own regblock in its own clock.
It is generated, not hand-written, because it is a pure function of the
DUT's port list -- and the phase 2/3 builds (AXI3/AXI5, AXI-Lite, APB, WB4)
are new TOMLs through this same script, not new harnesses.

    python3 bin/gen_bs_harness.py rtl/bridges/configs/bridge_bs_axi4.toml

writes rtl/generated/bs_harness_<dut>/bs_harness_<dut>.sv and
rtl/generated/filelists/bs_harness_<dut>.f. Clock domains: a port with
`cdc = true` runs on cclk, everything else on aclk (the DUT's clock).
"""
from __future__ import annotations

import argparse
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import List

AREA = Path(__file__).resolve().parent.parent
MAX_PORTS = 8          # configuration windows bridge_bs_cfg carries per side
PROTO_CODE = {'axi4': 0, 'axi3': 1, 'axi5': 2, 'axil': 3, 'axil5': 4,
              'apb': 5, 'apb5': 6, 'wb4': 7}

AR = [('arid', 'IW'), ('araddr', '32'), ('arlen', '8'), ('arsize', '3'),
      ('arburst', '2'), ('arlock', '1'), ('arcache', '4'), ('arprot', '3'),
      ('arqos', '4'), ('arregion', '4'), ('aruser', 'UW'),
      ('arvalid', '1'), ('arready', '1')]
R = [('rid', 'IW'), ('rdata', 'DW'), ('rresp', '2'), ('rlast', '1'),
     ('ruser', 'UW'), ('rvalid', '1'), ('rready', '1')]
AW = [(n.replace('ar', 'aw', 1), w) for n, w in AR]
W = [('wdata', 'DW'), ('wstrb', 'SW'), ('wlast', '1'), ('wuser', 'UW'),
     ('wvalid', '1'), ('wready', '1')]
B = [('bid', 'IW'), ('bresp', '2'), ('buser', 'UW'), ('bvalid', '1'), ('bready', '1')]

# AXI3: 4-bit AxLEN, 2-bit AxLOCK, WID, no AxQOS / AxREGION
AR3 = [(n, {'arlen': '4', 'arlock': '2'}.get(n, w)) for n, w in AR
       if n not in ('arqos', 'arregion')]
AW3 = [(n.replace('ar', 'aw', 1), w) for n, w in AR3]
W3 = [('wid', 'IW')] + W

# protocol -> (AW, W, B, AR, R); the stress shells are <protocol>_{master,slave}_stress
CHANNELS = {'axi4': (AW, W, B, AR, R), 'axi3': (AW3, W3, B, AR3, R)}


@dataclass
class Port:
    name: str
    prefix: str
    protocol: str
    channels: str
    dw: int
    iw: int
    uw: int
    cdc: bool
    base: int = 0
    size: int = 0

    @property
    def rd(self) -> bool:
        return self.channels in ('rd', 'rw')

    @property
    def wr(self) -> bool:
        return self.channels in ('wr', 'rw')

    @property
    def clk(self) -> str:
        return 'cclk' if self.cdc else 'aclk'

    @property
    def rst(self) -> str:
        return 'cresetn' if self.cdc else 'aresetn'

    @property
    def chans(self):
        return CHANNELS[self.protocol]

    def all_sigs(self) -> List[tuple]:
        aw, w, b, ar, r = self.chans
        return aw + w + b + ar + r

    def sigs(self) -> List[tuple]:
        aw, w, b, ar, r = self.chans
        out = []
        if self.wr:
            out += aw + w + b
        if self.rd:
            out += ar + r
        return out


def load(toml: Path):
    cfg = tomllib.loads(toml.read_text())['bridge']
    ms, ss = [], []
    for m in cfg['masters']:
        ms.append(Port(m['name'], m['prefix'], m.get('protocol', 'axi4'),
                       m.get('channels', 'rw'), m['data_width'], m.get('id_width', 0),
                       max(1, m.get('user_width', 1)), bool(m.get('cdc', False))))
    for s in cfg['slaves']:
        ss.append(Port(s['name'], s['prefix'], s.get('protocol', 'axi4'),
                       s.get('channels', 'rw'), s['data_width'], s.get('id_width', 0),
                       max(1, s.get('user_width', 1)), bool(s.get('cdc', False)),
                       int(s['base_addr'], 0), int(s['addr_range'], 0)))
    for p in ms + ss:
        if p.protocol not in CHANNELS:
            sys.exit(f'{p.name}: protocol {p.protocol!r} has no stress shell yet '
                     f'(have {sorted(CHANNELS)})')
    if len(ms) > MAX_PORTS or len(ss) > MAX_PORTS:
        sys.exit(f'at most {MAX_PORTS} masters and {MAX_PORTS} slaves')
    return cfg['name'], ms, ss


def width(w: str, p: Port) -> str:
    v = {'IW': p.iw, 'DW': p.dw, 'SW': p.dw // 8, 'UW': p.uw}.get(w)
    n = int(w) if v is None else v
    return '' if n == 1 else f'[{n - 1}:0]'


def cpuif_addr_msb(regblock: str) -> int:
    """MSB of a generated regblock's s_cpuif_addr: read from the regblock
    itself, because it grows with the register map (a hard-coded width
    silently aliases the registers past it onto the first ones)."""
    import re
    src = (AREA / 'rtl/regs/generated/rtl' / f'{regblock}.sv').read_text()
    m = re.search(r'input\s+wire\s+\[(\d+):0\]\s+s_cpuif_addr', src)
    if not m:
        sys.exit(f'{regblock}: no s_cpuif_addr port (regenerate the regblocks first)')
    return int(m.group(1))


def gen(dut: str, ms: List[Port], ss: List[Port], variant: int) -> str:
    L: List[str] = []
    ctl_msb = cpuif_addr_msb('bstress_ctl_regs')
    a = L.append
    nm, ns = len(ms), len(ss)
    a(f"""// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Generated by: projects/fpga-systems/Genesys2/bridge-stress/bin/gen_bs_harness.py
// From:         rtl/bridges/configs/{dut}.toml
// DO NOT EDIT -- regenerate (bin/regen.sh).
//
// Module: bs_harness_{dut}
// Purpose: The bridge stress harness around {dut}: UART host link,
//          configuration bridge, control regblock, one stress master per DUT
//          master port and one stress slave per DUT slave port.
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
//==============================================================================
// Clocks: aclk is the DUT's clock and the configuration clock; cclk is the
// clock of every port the TOML marks cdc. GO / STOP reach cclk through
// sync_pulse, the data seed (static while a run is live) through
// cdc_synchronizer, and the per-block done / error bits come back the same
// way. Each block's registers live in its own clock (bstress_*_csr).
//==============================================================================

`timescale 1ns / 1ps

module bs_harness_{dut}
    import axi_stress_pkg::*;
#(
    parameter int CLKS_PER_BIT = 868     // 100 MHz / 115200
) (
    input  logic aclk,
    input  logic aresetn,
    input  logic cclk,
    input  logic cresetn,

    input  logic i_uart_rx,
    output logic o_uart_tx,

    output logic o_all_done,
    output logic o_any_err,
    output logic o_busy
);

    localparam int NM = {nm};
    localparam int NS = {ns};
""")

    # ---------------------------------------------------------------- host
    a("""    // =========================================================================
    // Host link: UART -> AXI4-Lite -> bridge_bs_cfg -> one APB window per block
    // =========================================================================
    logic [31:0] host_axi_awaddr, host_axi_wdata, host_axi_araddr, host_axi_rdata;
    logic [2:0]  host_axi_awprot, host_axi_arprot;
    logic [3:0]  host_axi_wstrb;
    logic [1:0]  host_axi_bresp, host_axi_rresp;
    logic        host_axi_awvalid, host_axi_awready, host_axi_wvalid, host_axi_wready;
    logic        host_axi_bvalid, host_axi_bready, host_axi_arvalid, host_axi_arready;
    logic        host_axi_rvalid, host_axi_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk, .aresetn,
        .i_uart_rx, .o_uart_tx,
        .m_axil_awaddr(host_axi_awaddr), .m_axil_awprot(host_axi_awprot),
        .m_axil_awvalid(host_axi_awvalid), .m_axil_awready(host_axi_awready),
        .m_axil_wdata(host_axi_wdata), .m_axil_wstrb(host_axi_wstrb),
        .m_axil_wvalid(host_axi_wvalid), .m_axil_wready(host_axi_wready),
        .m_axil_bresp(host_axi_bresp), .m_axil_bvalid(host_axi_bvalid),
        .m_axil_bready(host_axi_bready),
        .m_axil_araddr(host_axi_araddr), .m_axil_arprot(host_axi_arprot),
        .m_axil_arvalid(host_axi_arvalid), .m_axil_arready(host_axi_arready),
        .m_axil_rdata(host_axi_rdata), .m_axil_rresp(host_axi_rresp),
        .m_axil_rvalid(host_axi_rvalid), .m_axil_rready(host_axi_rready)
    );
""")
    wins = ['ctl'] + [f'mst{i}' for i in range(MAX_PORTS)] + [f'slv{i}' for i in range(MAX_PORTS)]
    for w in wins:
        a(f"    logic        {w}_apb_PSEL, {w}_apb_PENABLE, {w}_apb_PWRITE, "
          f"{w}_apb_PREADY, {w}_apb_PSLVERR;")
        a(f"    logic [31:0] {w}_apb_PADDR, {w}_apb_PWDATA, {w}_apb_PRDATA;")
        a(f"    logic [3:0]  {w}_apb_PSTRB;")
        a(f"    logic [2:0]  {w}_apb_PPROT;")
    a("    logic        cfg_unmapped_irq;")
    a("""
    bridge_bs_cfg u_cfg (
        .aclk, .aresetn,
        .host_axi_awaddr, .host_axi_awprot, .host_axi_awvalid, .host_axi_awready,
        .host_axi_wdata, .host_axi_wstrb, .host_axi_wvalid, .host_axi_wready,
        .host_axi_bresp, .host_axi_bvalid, .host_axi_bready,
        .host_axi_araddr, .host_axi_arprot, .host_axi_arvalid, .host_axi_arready,
        .host_axi_rdata, .host_axi_rresp, .host_axi_rvalid, .host_axi_rready,""")
    for w in wins:
        a(f"        .{w}_apb_PSEL, .{w}_apb_PADDR, .{w}_apb_PENABLE, .{w}_apb_PWRITE,")
        a(f"        .{w}_apb_PWDATA, .{w}_apb_PSTRB, .{w}_apb_PPROT,")
        a(f"        .{w}_apb_PRDATA, .{w}_apb_PREADY, .{w}_apb_PSLVERR,")
    a("""        .unmapped_irq   (cfg_unmapped_irq),
        /* verilator lint_off PINCONNECTEMPTY */
        .unmapped_addr  (),
        .unmapped_count (),
        /* verilator lint_on PINCONNECTEMPTY */
        .unmapped_clear (1'b0)
    );
""")
    # unused windows
    used = {f'mst{i}' for i in range(nm)} | {f'slv{i}' for i in range(ns)} | {'ctl'}
    for w in wins:
        if w not in used:
            a(f"    // {w}: no block in this build -- every access answers PSLVERR")
            a(f"    assign {w}_apb_PREADY  = 1'b1;")
            a(f"    assign {w}_apb_PSLVERR = 1'b1;")
            a(f"    assign {w}_apb_PRDATA  = 32'hDEAD_0000;")
    a(f"    wire unused_cfg = ^{{cfg_unmapped_irq, " + ", ".join(
        f"{w}_apb_PSEL, {w}_apb_PADDR, {w}_apb_PENABLE, {w}_apb_PWRITE, "
        f"{w}_apb_PWDATA, {w}_apb_PSTRB, {w}_apb_PPROT" for w in wins if w not in used)
      + "};\n" if len(used) < len(wins) else "    wire unused_cfg = cfg_unmapped_irq;\n")

    # ---------------------------------------------------------------- ctl
    a(f"""    // =========================================================================
    // Control regblock (aclk)
    // =========================================================================
    logic        ctl_req, ctl_req_is_wr, ctl_stall_wr, ctl_stall_rd;
    logic        ctl_rd_ack, ctl_rd_err, ctl_wr_ack, ctl_wr_err;
    logic [11:0] ctl_addr;
    logic [31:0] ctl_wr_data, ctl_wr_biten, ctl_rd_data;

    apb4_to_peakrdl #(.ADDR_WIDTH(12), .DATA_WIDTH(32), .PROT_WIDTH(3)) u_ctl_shim (
        .aclk, .aresetn, .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (ctl_apb_PSEL), .s_apb_PENABLE (ctl_apb_PENABLE),
        .s_apb_PREADY (ctl_apb_PREADY), .s_apb_PADDR (ctl_apb_PADDR[11:0]),
        .s_apb_PWRITE (ctl_apb_PWRITE), .s_apb_PWDATA (ctl_apb_PWDATA),
        .s_apb_PSTRB (ctl_apb_PSTRB), .s_apb_PPROT (ctl_apb_PPROT),
        .s_apb_PRDATA (ctl_apb_PRDATA), .s_apb_PSLVERR (ctl_apb_PSLVERR),
        .cpuif_req (ctl_req), .cpuif_req_is_wr (ctl_req_is_wr), .cpuif_addr (ctl_addr),
        .cpuif_wr_data (ctl_wr_data), .cpuif_wr_biten (ctl_wr_biten),
        .cpuif_req_stall_wr (ctl_stall_wr), .cpuif_req_stall_rd (ctl_stall_rd),
        .cpuif_rd_ack (ctl_rd_ack), .cpuif_rd_err (ctl_rd_err), .cpuif_rd_data (ctl_rd_data),
        .cpuif_wr_ack (ctl_wr_ack), .cpuif_wr_err (ctl_wr_err)
    );

    bstress_ctl_regs_pkg::bstress_ctl_regs__in_t  ctl_hi;
    bstress_ctl_regs_pkg::bstress_ctl_regs__out_t ctl_ho;

    bstress_ctl_regs u_ctl (
        .clk (aclk), .rst (~aresetn),
        .s_cpuif_req (ctl_req), .s_cpuif_req_is_wr (ctl_req_is_wr),
        .s_cpuif_addr (ctl_addr[{ctl_msb}:0]),
        .s_cpuif_wr_data (ctl_wr_data), .s_cpuif_wr_biten (ctl_wr_biten),
        .s_cpuif_req_stall_wr (ctl_stall_wr), .s_cpuif_req_stall_rd (ctl_stall_rd),
        .s_cpuif_rd_ack (ctl_rd_ack), .s_cpuif_rd_err (ctl_rd_err),
        .s_cpuif_rd_data (ctl_rd_data),
        .s_cpuif_wr_ack (ctl_wr_ack), .s_cpuif_wr_err (ctl_wr_err),
        .hwif_in (ctl_hi), .hwif_out (ctl_ho)
    );
    wire unused_ctl = ^{{ctl_addr[11:{ctl_msb + 1}], ctl_apb_PADDR[31:12]}};

    // GO / STOP / seed in each domain. GO and STOP are the RISING EDGES of
    // their singlepulse fields: apb4_to_peakrdl holds the cpuif request until
    // the ack, so the regblock takes each write twice and a singlepulse is two
    // cycles wide -- which toggles sync_pulse twice, and cclk then sees two
    // GOs or none. The edge is one cycle whatever the field's width.
    logic        go_a, stop_a, go_c, stop_c, r_go_q, r_stop_q;
    logic [31:0] seed_a, seed_c;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_go_q   <= 1'b0;
            r_stop_q <= 1'b0;
        end else begin
            r_go_q   <= ctl_ho.CTRL.GO.value;
            r_stop_q <= ctl_ho.CTRL.STOP.value;
        end
    end
    assign go_a   = ctl_ho.CTRL.GO.value && !r_go_q;
    assign stop_a = ctl_ho.CTRL.STOP.value && !r_stop_q;
    assign seed_a = ctl_ho.HASH_SEED.VALUE.value;

    sync_pulse u_go_c (
        .i_src_clk (aclk), .i_src_rst_n (aresetn), .i_pulse (go_a),
        .i_dst_clk (cclk), .i_dst_rst_n (cresetn), .o_pulse (go_c)
    );
    sync_pulse u_stop_c (
        .i_src_clk (aclk), .i_src_rst_n (aresetn), .i_pulse (stop_a),
        .i_dst_clk (cclk), .i_dst_rst_n (cresetn), .o_pulse (stop_c)
    );
    cdc_synchronizer #(.WIDTH(32)) u_seed_c (
        .clk (cclk), .rst_n (cresetn), .async_in (seed_a), .sync_out (seed_c)
    );

    // Per-block done / error, raw in the block's domain and synchronized to aclk
    logic [NM-1:0] mst_done_raw, mst_err_raw, mst_done, mst_err;
    logic [NS-1:0] slv_err_raw, slv_err;
""")

    # ---------------------------------------------------------------- masters
    for i, p in enumerate(ms):
        go, stop, seed = ('go_c', 'stop_c', 'seed_c') if p.cdc else ('go_a', 'stop_a', 'seed_a')
        a(f"""    // =========================================================================
    // Master {i}: {p.name} ({p.protocol}, {p.channels}, {p.dw}-bit, ID {p.iw}, {p.clk})
    // =========================================================================
    stress_mdir_cfg_t m{i}_cfg_rd, m{i}_cfg_wr;
    stress_mdir_sts_t m{i}_sts_rd, m{i}_sts_wr;
    stress_win_t      m{i}_win [8];
""")
        for n, w in p.sigs():
            a(f"    logic {width(w, p):<8} {p.prefix}{n};")
        a(f"""
    bstress_mst_csr #(
        .INDEX({i}), .PROTOCOL({PROTO_CODE[p.protocol]}), .DW({p.dw}), .IW({p.iw}),
        .DEPTH(16), .NWIN(8), .HAS_RD(1'b{int(p.rd)}), .HAS_WR(1'b{int(p.wr)})
    ) u_m{i}_csr (
        .aclk ({p.clk}), .aresetn ({p.rst}), .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (mst{i}_apb_PSEL), .s_apb_PENABLE (mst{i}_apb_PENABLE),
        .s_apb_PREADY (mst{i}_apb_PREADY), .s_apb_PADDR (mst{i}_apb_PADDR[11:0]),
        .s_apb_PWRITE (mst{i}_apb_PWRITE), .s_apb_PWDATA (mst{i}_apb_PWDATA),
        .s_apb_PSTRB (mst{i}_apb_PSTRB), .s_apb_PPROT (mst{i}_apb_PPROT),
        .s_apb_PRDATA (mst{i}_apb_PRDATA), .s_apb_PSLVERR (mst{i}_apb_PSLVERR),
        .cfg_rd (m{i}_cfg_rd), .cfg_wr (m{i}_cfg_wr), .cfg_win (m{i}_win),
        .sts_rd (m{i}_sts_rd), .sts_wr (m{i}_sts_wr)
    );
    wire unused_m{i}_paddr = ^mst{i}_apb_PADDR[31:12];

    {p.protocol}_master_stress #(
        .EN_RD(1'b{int(p.rd)}), .EN_WR(1'b{int(p.wr)}), .DEPTH(16), .NWIN(8),
        .IW({p.iw}), .DW({p.dw}), .UW({p.uw})
    ) u_m{i} (
        .aclk ({p.clk}), .aresetn ({p.rst}), .go ({go}), .stop ({stop}),
        .cfg_rd (m{i}_cfg_rd), .cfg_wr (m{i}_cfg_wr), .cfg_win (m{i}_win),
        .cfg_hash_seed ({seed}),
        .sts_rd (m{i}_sts_rd), .sts_wr (m{i}_sts_wr),""")
        conns = []
        have = {n for n, _ in p.sigs()}
        for n, _ in p.all_sigs():
            conns.append(f"        .m_axi_{n:<9} ({p.prefix + n if n in have else ''})")
        a("        /* verilator lint_off PINCONNECTEMPTY */")
        a(",\n".join(conns))
        a("        /* verilator lint_on PINCONNECTEMPTY */")
        a("    );")
        a(f"    assign mst_done_raw[{i}] = m{i}_sts_rd.done && m{i}_sts_wr.done;")
        a(f"    assign mst_err_raw[{i}]  = (|m{i}_sts_rd.err_mask) || (|m{i}_sts_wr.err_mask);\n")

    # ---------------------------------------------------------------- slaves
    for i, p in enumerate(ss):
        go, seed = ('go_c', 'seed_c') if p.cdc else ('go_a', 'seed_a')
        a(f"""    // =========================================================================
    // Slave {i}: {p.name} ({p.protocol}, {p.channels}, {p.dw}-bit, ID {p.iw}, {p.clk})
    //          window 0x{p.base:08X} + 0x{p.size:X}
    // =========================================================================
    stress_sdir_cfg_t s{i}_cfg_rd, s{i}_cfg_wr;
    stress_sdir_sts_t s{i}_sts_rd, s{i}_sts_wr;
""")
        for n, w in p.sigs():
            a(f"    logic {width(w, p):<8} {p.prefix}{n};")
        a(f"""
    bstress_slv_csr #(
        .INDEX({i}), .PROTOCOL({PROTO_CODE[p.protocol]}), .DW({p.dw}), .IW({p.iw}),
        .DEPTH(16), .HAS_RD(1'b{int(p.rd)}), .HAS_WR(1'b{int(p.wr)})
    ) u_s{i}_csr (
        .aclk ({p.clk}), .aresetn ({p.rst}), .pclk (aclk), .presetn (aresetn),
        .s_apb_PSEL (slv{i}_apb_PSEL), .s_apb_PENABLE (slv{i}_apb_PENABLE),
        .s_apb_PREADY (slv{i}_apb_PREADY), .s_apb_PADDR (slv{i}_apb_PADDR[11:0]),
        .s_apb_PWRITE (slv{i}_apb_PWRITE), .s_apb_PWDATA (slv{i}_apb_PWDATA),
        .s_apb_PSTRB (slv{i}_apb_PSTRB), .s_apb_PPROT (slv{i}_apb_PPROT),
        .s_apb_PRDATA (slv{i}_apb_PRDATA), .s_apb_PSLVERR (slv{i}_apb_PSLVERR),
        .cfg_rd (s{i}_cfg_rd), .cfg_wr (s{i}_cfg_wr),
        .sts_rd (s{i}_sts_rd), .sts_wr (s{i}_sts_wr)
    );
    wire unused_s{i}_paddr = ^slv{i}_apb_PADDR[31:12];

    {p.protocol}_slave_stress #(
        .EN_RD(1'b{int(p.rd)}), .EN_WR(1'b{int(p.wr)}), .DEPTH(16),
        .IW({p.iw}), .DW({p.dw}), .UW({p.uw})
    ) u_s{i} (
        .aclk ({p.clk}), .aresetn ({p.rst}), .clear ({go}),
        .cfg_rd (s{i}_cfg_rd), .cfg_wr (s{i}_cfg_wr), .cfg_hash_seed ({seed}),
        .sts_rd (s{i}_sts_rd), .sts_wr (s{i}_sts_wr),""")
        conns = []
        have = {n for n, _ in p.sigs()}
        aw, w, _, ar, _ = p.chans
        for n, _ in p.all_sigs():
            tie = ''
            if n not in have:
                # inputs of a missing direction idle; outputs float
                inputs = {x for x, _ in aw + w + ar} | {'bready', 'rready'}
                tie = "'0" if n in inputs else ''
            conns.append(f"        .s_axi_{n:<9} ({p.prefix + n if n in have else tie})")
        a("        /* verilator lint_off PINCONNECTEMPTY */")
        a(",\n".join(conns))
        a("        /* verilator lint_on PINCONNECTEMPTY */")
        a("    );")
        a(f"    assign slv_err_raw[{i}] = (|s{i}_sts_rd.err_mask) || (|s{i}_sts_wr.err_mask);\n")

    # ---------------------------------------------------------------- DUT
    a(f"""    // =========================================================================
    // Device under test
    // =========================================================================
    logic        dut_unmapped_irq;
    logic [31:0] dut_unmapped_addr;
    logic [7:0]  dut_unmapped_count;

    {dut} u_dut (
        .aclk, .aresetn,""")
    for p in ms + ss:
        if p.cdc:
            a(f"        .{p.name}_aclk (cclk), .{p.name}_aresetn (cresetn),")
    for p in ms + ss:
        for n, _ in p.sigs():
            a(f"        .{p.prefix}{n},")
    a("""        .unmapped_irq   (dut_unmapped_irq),
        .unmapped_addr  (dut_unmapped_addr),
        .unmapped_count (dut_unmapped_count),
        .unmapped_clear (ctl_ho.CTRL.UNMAPPED_CLEAR.value)
    );
""")

    # ---------------------------------------------------------------- roll-up
    cm = [i for i, p in enumerate(ms) if p.cdc]
    cs = [i for i, p in enumerate(ss) if p.cdc]
    a("    // ---- roll-up into aclk ----------------------------------------------------")
    for i, p in enumerate(ms):
        if p.cdc:
            a(f"    cdc_synchronizer #(.WIDTH(2)) u_m{i}_sync (.clk (aclk), .rst_n (aresetn),\n"
              f"        .async_in ({{mst_done_raw[{i}], mst_err_raw[{i}]}}), "
              f".sync_out ({{mst_done[{i}], mst_err[{i}]}}));")
        else:
            a(f"    assign mst_done[{i}] = mst_done_raw[{i}];")
            a(f"    assign mst_err[{i}]  = mst_err_raw[{i}];")
    for i, p in enumerate(ss):
        if p.cdc:
            a(f"    cdc_synchronizer #(.WIDTH(1)) u_s{i}_sync (.clk (aclk), .rst_n (aresetn),\n"
              f"        .async_in (slv_err_raw[{i}]), .sync_out (slv_err[{i}]));")
        else:
            a(f"    assign slv_err[{i}] = slv_err_raw[{i}];")
    a(f"""
    // Run timer: GO to ALL_DONE. ALL_DONE is ignored for the first 16 cycles
    // after GO -- the blocks' done flags, and the synchronized ones longer
    // still, show the previous run until GO reaches them.
    logic        r_busy;
    logic [4:0]  r_guard;
    logic [7:0]  r_go_count;
    logic [31:0] r_timer, r_cycles;
    logic        w_all_done, w_any_err;
    assign w_all_done = &mst_done;
    assign w_any_err  = (|mst_err) || (|slv_err);

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_busy   <= 1'b0;
            r_guard  <= '0;
            r_timer  <= '0;
            r_cycles <= '0;
            r_go_count <= '0;
        end else begin
            r_cycles <= r_cycles + 32'd1;
            if (go_a) r_go_count <= r_go_count + 8'd1;
            if (go_a) begin
                r_busy  <= 1'b1;
                r_guard <= 5'd16;
                r_timer <= '0;
            end else if (r_busy) begin
                r_timer <= r_timer + 32'd1;
                if (r_guard != '0)  r_guard <= r_guard - 5'd1;
                else if (w_all_done) r_busy <= 1'b0;
            end
        end
    end

    logic r_cresetn_a;
    cdc_synchronizer #(.WIDTH(1)) u_crst_sync (.clk (aclk), .rst_n (aresetn),
        .async_in (cresetn), .sync_out (r_cresetn_a));

    always_comb begin
        ctl_hi.ID.NUM_MASTERS.next = 4'(NM);
        ctl_hi.ID.NUM_SLAVES.next  = 4'(NS);
        ctl_hi.ID.VARIANT.next     = 8'd{variant};
        ctl_hi.ID.MAGIC.next       = 16'h4253;
        ctl_hi.STATUS.ALL_DONE.next  = w_all_done && !r_busy;
        ctl_hi.STATUS.ANY_ERR.next   = w_any_err;
        ctl_hi.STATUS.CLOCKS_OK.next = r_cresetn_a;
        ctl_hi.STATUS.UNMAPPED.next  = dut_unmapped_irq;
        ctl_hi.STATUS.MST_DONE.next  = 8'(mst_done);
        ctl_hi.STATUS.MST_ERR.next   = 8'(mst_err);
        ctl_hi.STATUS.SLV_ERR.next   = 8'(slv_err);
        ctl_hi.TIMER.VALUE.next          = r_timer;
        ctl_hi.UNMAPPED_COUNT.COUNT.next = dut_unmapped_count;
        ctl_hi.UNMAPPED_ADDR.VALUE.next  = dut_unmapped_addr;
        ctl_hi.CYCLES.VALUE.next         = r_cycles;
        ctl_hi.GO_COUNT.VALUE.next       = r_go_count;
    end

    assign o_all_done = w_all_done && !r_busy;
    assign o_any_err  = w_any_err;
    assign o_busy     = r_busy;

endmodule : bs_harness_{dut}
""")
    return '\n'.join(L)


def filelist(dut: str, rel: str, ms: List[Port], ss: List[Port]) -> str:
    shells = ''.join(f'-f $REPO_ROOT/rtl/amba/filelists/{proto}_{side}_stress.f\n'
                     for side, ports in (('master', ms), ('slave', ss))
                     for proto in sorted({p.protocol for p in ports}))
    return f"""# Generated by bin/gen_bs_harness.py -- DO NOT EDIT
# Compile closure of bs_harness_{dut}.
+incdir+$REPO_ROOT/rtl/amba/includes
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f
{shells}-f $REPO_ROOT/rtl/cdc/filelists/sync_pulse.f
-f $REPO_ROOT/rtl/cdc/filelists/cdc_synchronizer.f
-f $CONVERTERS_ROOT/rtl/filelists/uart_axil_bridge.f
-f $CONVERTERS_ROOT/rtl/filelists/apb4_to_peakrdl.f
-f $REPO_ROOT/{rel}/rtl/filelists/bstress_regs.f
-f $REPO_ROOT/{rel}/rtl/bridges/filelists/bridge_bs_cfg.f
-f $REPO_ROOT/{rel}/rtl/bridges/filelists/{dut}.f
$REPO_ROOT/{rel}/rtl/bstress_mst_csr.sv
$REPO_ROOT/{rel}/rtl/bstress_slv_csr.sv
$REPO_ROOT/{rel}/rtl/generated/bs_harness_{dut}/bs_harness_{dut}.sv
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('toml', type=Path)
    ap.add_argument('--variant', type=int, default=1, help='ID.VARIANT value')
    args = ap.parse_args()
    dut, ms, ss = load(args.toml)
    out = AREA / 'rtl' / 'generated' / f'bs_harness_{dut}'
    out.mkdir(parents=True, exist_ok=True)
    (out / f'bs_harness_{dut}.sv').write_text(gen(dut, ms, ss, args.variant))
    fl = AREA / 'rtl' / 'generated' / 'filelists'
    fl.mkdir(parents=True, exist_ok=True)
    repo = next(p for p in AREA.parents if (p / '.git').exists())
    (fl / f'bs_harness_{dut}.f').write_text(filelist(dut, str(AREA.relative_to(repo)), ms, ss))
    print(f'[gen_bs_harness] {out}/bs_harness_{dut}.sv  ({len(ms)} masters, {len(ss)} slaves)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
