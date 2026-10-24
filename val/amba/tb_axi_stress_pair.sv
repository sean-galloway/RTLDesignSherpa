// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_axi_stress_pair
// Purpose: Simulation harness: axi{4,3,5}_master_stress -> fault injector ->
//          axi{4,3,5}_slave_stress, back to back with no fabric between them.
//
// PROTO selects the shells: 0 = AXI4, 1 = AXI3, 2 = AXI5, 3 = AXI4-Lite,
// 4 = AXI5-Lite, 5 = APB4, 6 = APB5, 7 = WB4. The nets below are AXI4 shaped whatever the protocol (AxLEN
// 8 bits, AxLOCK 1 bit), so the Python monitor reads one set of names; with AXI3 the upper
// AxLEN bits are tied 0 and m_wid carries WID. With AXI4-Lite the fields Lite
// does not carry are tied to what every Lite transfer is: ID 0, one beat,
// bus-wide, INCR, RLAST / WLAST 1. AXI5-Lite is the same with real IDs and
// TRACE / POISON on the AXI5 nets. With APB4 / APB5 the nets are derived from the
// APB handshake (an AR and its R, or an AW, its W and its B, in the cycle
// PREADY completes the transfer), and the slave sees an offset (OFFSET_LG2).
// With WB4 an AR or AW + W is a transfer's acceptance and its R or B its
// termination, in order (an in-order queue tells a read's from a write's). AXI5 builds both shells with NSAID, TRACE,
// MPAM, MECID, POISON, UNIQUE, ATOMIC and MTE, and adds the m_*trace /
// m_*poison / m_*nsaid / m_*mpam / m_*mecid nets; they are 0 for the others.
//
// The fault injector corrupts exactly one handshake per armed fault (one bit
// of flt_arm each), so a test can show that every check the stress blocks
// claim actually fires:
//   [0] R:  flip bit 0 of every RDATA byte   -> master ERR_RD_DATA (some
//           byte of any beat is active, even an unaligned first beat's)
//   [1] R:  flip RID bit 0                   -> master ERR_RD_STRAY / LAST / DATA
//   [2] R:  drop RLAST on a last beat        -> master ERR_RD_LAST
//   [3] W:  flip WDATA bit 0                 -> slave  ERR_S_WDATA (if strobed)
//   [4] B:  flip BID bit 0                   -> master ERR_WR_STRAY / EARLY
//   [5] AR: flip ARADDR bit 31 (bit OFFSET_LG2-1 when the slave sees an
//           offset: bit 31 is not on its port)  -> slave  ERR_S_ADDR
//   [6] B:  BRESP forced to SLVERR           -> master ERR_WR_RESP
//   [7] R:  RRESP forced to SLVERR           -> master ERR_RD_RESP
//   [8] W:  flip WID bit 0 (AXI3 only)       -> slave  ERR_S_WID
//   [9] AR: flip ARTRACE    (AXI5 only)      -> slave  ERR_S_SB
//  [10] W:  flip WPOISON    (AXI5 only)      -> slave  ERR_S_SB
//  [11] R:  flip RTRACE     (AXI5 only)      -> master ERR_M_SB
//  [12] R:  flip RPOISON    (AXI5 only)      -> master ERR_M_SB
//  [13] B:  flip BTRACE     (AXI5 only)      -> master ERR_M_SB
//  [14] AW: flip AWMECID bit 0 (AXI5 only)   -> slave  ERR_S_SB
//  [15] R:  flip RIDUNQ     (AXI5 only)      -> master ERR_M_SB
//  [16] B:  flip BIDUNQ     (AXI5 only)      -> master ERR_M_SB
//  [17] AR: force ARIDUNQ on an AR whose ID has a burst outstanding on the
//           wire (AXI5 only)                 -> slave ERR_S_SB
//  [18] R:  flip bit 0 of every byte of a read-return atomic's R beat (RID
//           MSB set; AXI5 only)              -> master write side ERR_RD_DATA
//  [19] AW: an atomic's AWATOP forced to a reserved encoding (AXI5 only)
//                                            -> slave ERR_S_PROTO
//  [20] W:  flip WTAG bit 0     (AXI5 only)  -> slave  ERR_S_SB
//  [21] R:  flip RTAG bit 0 of a read's beat (AXI5 only) -> master ERR_M_SB
//  [22] B:  flip BTAGMATCH bit 0 (AXI5 only) -> master ERR_M_SB
//  [23] AR: flip ARTAGOP bit 0  (AXI5 only)  -> slave  ERR_S_SB
// flt_done shows which armed faults have been applied.
// hold_b (level) holds every B between the slave and the master: a test makes
// one burst outlast the stress master's latency counter with it.
//
// Struct widths are exported (o_w_*) so the Python packer can check its
// field layout against the RTL instead of trusting it.
//==============================================================================

`timescale 1ns / 1ps

module tb_axi_stress_pair
    import axi_stress_pkg::*;
#(
    parameter int IW    = 8,
    parameter int DW    = 64,
    parameter int DEPTH = 16,
    parameter int NWIN  = 8,
    parameter int PROTO = 0,           // 0 AXI4, 1 AXI3, 2 AXI5, 3 AXI4-Lite, 4 AXI5-Lite, 5 APB4, 6 APB5, 7 WB4
    parameter int WB_CLASSIC = 0,      // WB4: 1 = B4 standard (classic) cycles
    // The slave sees the address modulo 2^OFFSET_LG2, as a bridge hands an
    // APB slave its window offset (the slave runs in offset mode); 0 = the
    // full address.
    parameter int OFFSET_LG2 = 0
) (
    input  logic                              aclk,
    input  logic                              aresetn,

    input  logic                              go,
    input  logic                              stop,
    input  logic                              clear,
    input  logic [$bits(stress_mdir_cfg_t)-1:0]    cfg_mrd,
    input  logic [$bits(stress_mdir_cfg_t)-1:0]    cfg_mwr,
    input  logic [NWIN*$bits(stress_win_t)-1:0]    cfg_win_flat,   // window 0 in the LSBs
    input  logic [$bits(stress_sdir_cfg_t)-1:0]    cfg_srd,
    input  logic [$bits(stress_sdir_cfg_t)-1:0]    cfg_swr,
    input  logic [31:0]                       cfg_hash_seed,
    output logic [$bits(stress_mdir_sts_t)-1:0]    sts_mrd,
    output logic [$bits(stress_mdir_sts_t)-1:0]    sts_mwr,
    output logic [$bits(stress_sdir_sts_t)-1:0]    sts_srd,
    output logic [$bits(stress_sdir_sts_t)-1:0]    sts_swr,

    input  logic [23:0]                       flt_arm,     // pulse: arm a fault
    output logic [23:0]                       flt_done,
    input  logic                              hold_b,      // hold every B between slave and master

    output logic [15:0]                       o_w_win,
    output logic [15:0]                       o_w_mcfg,
    output logic [15:0]                       o_w_msts,
    output logic [15:0]                       o_w_scfg,
    output logic [15:0]                       o_w_ssts
);

    assign o_w_win  = 16'($bits(stress_win_t));
    assign o_w_mcfg = 16'($bits(stress_mdir_cfg_t));
    assign o_w_msts = 16'($bits(stress_mdir_sts_t));
    assign o_w_scfg = 16'($bits(stress_sdir_cfg_t));
    assign o_w_ssts = 16'($bits(stress_sdir_sts_t));

    stress_win_t w_win [NWIN];
    always_comb
        for (int i = 0; i < NWIN; i++)
            w_win[i] = cfg_win_flat[i*$bits(stress_win_t) +: $bits(stress_win_t)];

    stress_mdir_sts_t w_sts_mrd, w_sts_mwr;
    stress_sdir_sts_t w_sts_srd, w_sts_swr;
    assign sts_mrd = w_sts_mrd;
    assign sts_mwr = w_sts_mwr;
    assign sts_srd = w_sts_srd;
    assign sts_swr = w_sts_swr;

    // ---- master side nets -----------------------------------------------------
    logic [IW-1:0] m_awid, m_arid, m_bid, m_rid;
    logic [31:0]   m_awaddr, m_araddr;
    logic [7:0]    m_awlen, m_arlen;
    logic [2:0]    m_awsize, m_arsize, m_awprot, m_arprot;
    logic [1:0]    m_awburst, m_arburst, m_bresp, m_rresp;
    logic          m_awlock, m_arlock;
    logic [3:0]    m_awcache, m_arcache, m_awqos, m_arqos, m_awregion, m_arregion;
    logic          m_awuser, m_aruser, m_wuser, m_buser, m_ruser;
    logic          m_awvalid, m_awready, m_wvalid, m_wready, m_bvalid, m_bready;
    logic          m_arvalid, m_arready, m_rvalid, m_rready, m_wlast, m_rlast;
    logic [DW-1:0] m_wdata, m_rdata;
    logic [DW/8-1:0] m_wstrb;
    logic [IW-1:0] m_wid, s_wid;      // AXI3 only; 0 with AXI4
    // AXI5 only; 0 with AXI3 / AXI4
    logic [3:0]    m_awnsaid, m_arnsaid;
    logic          m_awtrace, m_artrace, m_btrace, m_rtrace, m_wpoison, m_rpoison;
    logic [10:0]   m_awmpam, m_armpam;
    logic [15:0]   m_awmecid, m_armecid;
    logic          m_aridunq, m_ridunq, m_awidunq, m_bidunq;
    logic [5:0]    m_awatop, s_awatop;
    localparam int NT = (DW / 128 > 0) ? DW / 128 : 1;
    localparam int TW = 4 * NT;
    logic [1:0]    m_awtagop, m_artagop, s_artagop, m_btagmatch, s_btagmatch;
    logic [TW-1:0] m_wtag, s_wtag, m_rtag, s_rtag;
    logic [NT-1:0] m_wtagupdate;

    // ---- APB bus (PROTO 5 / 6) -------------------------------------------------
    localparam bit IS_APB = (PROTO == 5) || (PROTO == 6);
    localparam bit IS_WB  = (PROTO == 7);
    // Request faults held from a transfer's start to its end: APB, and WB4
    // in classic mode (a completer may sample at any cycle of the transfer).
    // A pipelined WB4 slave samples at acceptance, which is when they fire.
    localparam bit REQ_HOLD = IS_APB || (IS_WB && WB_CLASSIC != 0);
    // The master's pins; the slave sees the same handshake, the address as an
    // offset (OFFSET_LG2), and the data through the injector. PREADY is the
    // slave's, seen by both.
    logic          p_sel, p_enable, p_write, p_ready, p_slverr_m, p_slverr_s;
    logic          p_wakeup;          // APB5: the requester's PWAKEUP

    // ---- Wishbone bus (PROTO 7) ------------------------------------------------
    logic          wb_cyc, wb_stb, wb_we, wb_stall, wb_ack_s, wb_err_s, wb_rty_s;
    logic          wb_ack_m, wb_err_m;
    logic [31:0]   wb_adr;
    logic [DW-1:0] wb_dat_w, wb_dat_r_s;
    logic [DW/8-1:0] wb_sel;
    logic          r_wb_open;         // classic: a transfer is on the bus
    wire  wb_term  = wb_ack_s || wb_err_s || wb_rty_s;
    wire  wb_acc   = wb_cyc && wb_stb && ((WB_CLASSIC != 0) ? wb_term : !wb_stall);
    wire  wb_start = (WB_CLASSIC != 0) ? (wb_cyc && wb_stb && !r_wb_open) : wb_acc;
    // Terminations come back in acceptance order: the direction of each
    // accepted, unterminated transfer, oldest at [0].
    logic [DEPTH:0]        r_wbq;
    logic [$clog2(DEPTH+2)-1:0] r_wbq_n;
    wire  wb_head_wr = (r_wbq_n == '0) ? wb_we : r_wbq[0];
    logic [31:0]   p_addr;
    logic [DW-1:0] p_wdata, p_rdata_s;
    logic [DW/8-1:0] p_strb;
    logic [2:0]    p_prot;
    wire           p_xfer  = p_sel && p_enable && p_ready;
    wire           p_setup = p_sel && !p_enable;
    logic [1:0]    r_p_flip;          // APB: [0] PWDATA / [1] PADDR corrupted this transfer
    localparam logic [31:0] OFFSET_MASK = (OFFSET_LG2 > 0 && OFFSET_LG2 < 32)
                                          ? ((32'd1 << OFFSET_LG2) - 32'd1) : 32'hFFFF_FFFF;

    // ---- slave side nets (after the injector) ---------------------------------
    logic [IW-1:0] s_bid, s_rid;
    logic [31:0]   s_araddr;
    logic [1:0]    s_bresp, s_rresp;
    logic          s_rlast;
    logic [DW-1:0] s_wdata, s_rdata;
    logic          s_artrace, s_wpoison, s_rtrace, s_rpoison, s_btrace;
    logic [15:0]   s_awmecid;
    logic          s_aridunq, s_ridunq, s_bidunq;

    generate if (PROTO == 0) begin : g_mst4
        axi4_master_stress #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_axi_awid(m_awid), .m_axi_awaddr(m_awaddr), .m_axi_awlen(m_awlen),
            .m_axi_awsize(m_awsize), .m_axi_awburst(m_awburst), .m_axi_awlock(m_awlock),
            .m_axi_awcache(m_awcache), .m_axi_awprot(m_awprot), .m_axi_awqos(m_awqos),
            .m_axi_awregion(m_awregion), .m_axi_awuser(m_awuser),
            .m_axi_awvalid(m_awvalid), .m_axi_awready(m_awready),
            .m_axi_wdata(m_wdata), .m_axi_wstrb(m_wstrb), .m_axi_wlast(m_wlast),
            .m_axi_wuser(m_wuser), .m_axi_wvalid(m_wvalid), .m_axi_wready(m_wready),
            .m_axi_bid(m_bid), .m_axi_bresp(m_bresp), .m_axi_buser(m_buser),
            .m_axi_bvalid(m_bvalid), .m_axi_bready(m_bready),
            .m_axi_arid(m_arid), .m_axi_araddr(m_araddr), .m_axi_arlen(m_arlen),
            .m_axi_arsize(m_arsize), .m_axi_arburst(m_arburst), .m_axi_arlock(m_arlock),
            .m_axi_arcache(m_arcache), .m_axi_arprot(m_arprot), .m_axi_arqos(m_arqos),
            .m_axi_arregion(m_arregion), .m_axi_aruser(m_aruser),
            .m_axi_arvalid(m_arvalid), .m_axi_arready(m_arready),
            .m_axi_rid(m_rid), .m_axi_rdata(m_rdata), .m_axi_rresp(m_rresp),
            .m_axi_rlast(m_rlast), .m_axi_ruser(m_ruser),
            .m_axi_rvalid(m_rvalid), .m_axi_rready(m_rready)
        );
        assign m_wid = '0;
    end else if (PROTO == 1) begin : g_mst3
        logic [3:0] a3_awlen, a3_arlen;
        logic [1:0] a3_awlock, a3_arlock;
        assign m_awlen  = {4'd0, a3_awlen};
        assign m_arlen  = {4'd0, a3_arlen};
        assign m_awlock = a3_awlock[0];
        assign m_arlock = a3_arlock[0];
        assign m_awqos = '0;
        assign m_arqos = '0;
        assign m_awregion = '0;
        assign m_arregion = '0;

        axi3_master_stress #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_axi_awid(m_awid), .m_axi_awaddr(m_awaddr), .m_axi_awlen(a3_awlen),
            .m_axi_awsize(m_awsize), .m_axi_awburst(m_awburst), .m_axi_awlock(a3_awlock),
            .m_axi_awcache(m_awcache), .m_axi_awprot(m_awprot), .m_axi_awuser(m_awuser),
            .m_axi_awvalid(m_awvalid), .m_axi_awready(m_awready),
            .m_axi_wid(m_wid),
            .m_axi_wdata(m_wdata), .m_axi_wstrb(m_wstrb), .m_axi_wlast(m_wlast),
            .m_axi_wuser(m_wuser), .m_axi_wvalid(m_wvalid), .m_axi_wready(m_wready),
            .m_axi_bid(m_bid), .m_axi_bresp(m_bresp), .m_axi_buser(m_buser),
            .m_axi_bvalid(m_bvalid), .m_axi_bready(m_bready),
            .m_axi_arid(m_arid), .m_axi_araddr(m_araddr), .m_axi_arlen(a3_arlen),
            .m_axi_arsize(m_arsize), .m_axi_arburst(m_arburst), .m_axi_arlock(a3_arlock),
            .m_axi_arcache(m_arcache), .m_axi_arprot(m_arprot), .m_axi_aruser(m_aruser),
            .m_axi_arvalid(m_arvalid), .m_axi_arready(m_arready),
            .m_axi_rid(m_rid), .m_axi_rdata(m_rdata), .m_axi_rresp(m_rresp),
            .m_axi_rlast(m_rlast), .m_axi_ruser(m_ruser),
            .m_axi_rvalid(m_rvalid), .m_axi_rready(m_rready)
        );
    end else if (PROTO == 3) begin : g_mstl4
        axil4_master_stress #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_axil_awaddr(m_awaddr), .m_axil_awprot(m_awprot),
            .m_axil_awvalid(m_awvalid), .m_axil_awready(m_awready),
            .m_axil_wdata(m_wdata), .m_axil_wstrb(m_wstrb),
            .m_axil_wvalid(m_wvalid), .m_axil_wready(m_wready),
            .m_axil_bresp(m_bresp), .m_axil_bvalid(m_bvalid), .m_axil_bready(m_bready),
            .m_axil_araddr(m_araddr), .m_axil_arprot(m_arprot),
            .m_axil_arvalid(m_arvalid), .m_axil_arready(m_arready),
            .m_axil_rdata(m_rdata), .m_axil_rresp(m_rresp),
            .m_axil_rvalid(m_rvalid), .m_axil_rready(m_rready)
        );
        // The AXI4-shaped nets the monitor reads, filled with what every
        // AXI4-Lite transfer is: ID 0, one beat, bus-wide, INCR.
        assign m_awid = '0;  assign m_awlen = '0;  assign m_awsize = 3'($clog2(DW / 8));
        assign m_awburst = 2'b01;  assign m_awlock = 1'b0;  assign m_awcache = '0;
        assign m_awqos = '0;  assign m_awregion = '0;  assign m_awuser = 1'b0;
        assign m_wlast = 1'b1;  assign m_wuser = 1'b0;  assign m_wid = '0;
        assign m_arid = '0;  assign m_arlen = '0;  assign m_arsize = 3'($clog2(DW / 8));
        assign m_arburst = 2'b01;  assign m_arlock = 1'b0;  assign m_arcache = '0;
        assign m_arqos = '0;  assign m_arregion = '0;  assign m_aruser = 1'b0;
    end else if (PROTO == 4) begin : g_mstl5
        axil5_master_stress #(
            .EN_TRACE(1'b1), .EN_POISON(1'b1),
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_axil_awid(m_awid), .m_axil_awaddr(m_awaddr), .m_axil_awprot(m_awprot),
            .m_axil_awtrace(m_awtrace),
            .m_axil_awvalid(m_awvalid), .m_axil_awready(m_awready),
            .m_axil_wdata(m_wdata), .m_axil_wstrb(m_wstrb), .m_axil_wpoison(m_wpoison),
            .m_axil_wvalid(m_wvalid), .m_axil_wready(m_wready),
            .m_axil_bid(m_bid), .m_axil_bresp(m_bresp), .m_axil_btrace(m_btrace),
            .m_axil_bvalid(m_bvalid), .m_axil_bready(m_bready),
            .m_axil_arid(m_arid), .m_axil_araddr(m_araddr), .m_axil_arprot(m_arprot),
            .m_axil_artrace(m_artrace),
            .m_axil_arvalid(m_arvalid), .m_axil_arready(m_arready),
            .m_axil_rid(m_rid), .m_axil_rdata(m_rdata), .m_axil_rresp(m_rresp),
            .m_axil_rtrace(m_rtrace), .m_axil_rpoison(m_rpoison),
            .m_axil_rvalid(m_rvalid), .m_axil_rready(m_rready)
        );
        // AXI4-shaped nets: one beat, bus-wide, INCR; the IDs are real.
        assign m_awlen = '0;  assign m_awsize = 3'($clog2(DW / 8));
        assign m_awburst = 2'b01;  assign m_awlock = 1'b0;  assign m_awcache = '0;
        assign m_awqos = '0;  assign m_awregion = '0;  assign m_awuser = 1'b0;
        assign m_wlast = 1'b1;  assign m_wuser = 1'b0;  assign m_wid = '0;
        assign m_arlen = '0;  assign m_arsize = 3'($clog2(DW / 8));
        assign m_arburst = 2'b01;  assign m_arlock = 1'b0;  assign m_arcache = '0;
        assign m_arqos = '0;  assign m_arregion = '0;  assign m_aruser = 1'b0;
    end else if (IS_APB) begin : g_mstp
        if (PROTO == 5) begin : g_p4
            apb4_master_stress #(
                .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW)
            ) u_mst (
                .aclk, .aresetn, .go, .stop,
                .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
                .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
                .m_apb_PSEL(p_sel), .m_apb_PENABLE(p_enable), .m_apb_PADDR(p_addr),
                .m_apb_PWRITE(p_write), .m_apb_PWDATA(p_wdata), .m_apb_PSTRB(p_strb),
                .m_apb_PPROT(p_prot),
                .m_apb_PRDATA(m_rdata),
                .m_apb_PSLVERR(p_slverr_m),
                .m_apb_PREADY(p_ready)
            );
            assign p_wakeup = 1'b0;
        end else begin : g_p5
            apb5_master_stress #(
                .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW)
            ) u_mst (
                .aclk, .aresetn, .go, .stop,
                .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
                .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
                .m_apb_PSEL(p_sel), .m_apb_PENABLE(p_enable), .m_apb_PADDR(p_addr),
                .m_apb_PWRITE(p_write), .m_apb_PWDATA(p_wdata), .m_apb_PSTRB(p_strb),
                .m_apb_PPROT(p_prot),
                .m_apb_PRDATA(m_rdata),
                .m_apb_PSLVERR(p_slverr_m),
                .m_apb_PREADY(p_ready),
                .m_apb_PWAKEUP(p_wakeup)
            );
        end
        // The master sees the injector's response: SLVERR for its direction.
        assign p_slverr_m = p_write ? (m_bresp != RESP_OKAY) : (m_rresp != RESP_OKAY);
        // AXI4-shaped nets for the monitor and the injector, from the APB
        // handshake: a read in its access phase is an AR, and the cycle that
        // completes it the R; a write is AW, W and B in that cycle.
        assign m_arvalid = p_sel && p_enable && !p_write;  assign m_arready = p_ready;
        assign m_araddr  = p_addr;  assign m_arprot = p_prot;
        assign m_rvalid  = p_xfer && !p_write;  assign m_rready = 1'b1;
        assign m_awvalid = p_sel && p_enable && p_write;   assign m_awready = p_ready;
        assign m_awaddr  = p_addr;  assign m_awprot = p_prot;
        assign m_wvalid  = p_sel && p_enable && p_write;   assign m_wready  = p_ready;
        assign m_wdata   = p_wdata;  assign m_wstrb = p_strb;
        assign m_bready  = 1'b1;
        assign m_awid = '0;  assign m_awlen = '0;  assign m_awsize = 3'($clog2(DW / 8));
        assign m_awburst = 2'b01;  assign m_awlock = 1'b0;  assign m_awcache = '0;
        assign m_awqos = '0;  assign m_awregion = '0;  assign m_awuser = 1'b0;
        assign m_wlast = 1'b1;  assign m_wuser = 1'b0;  assign m_wid = '0;
        assign m_arid = '0;  assign m_arlen = '0;  assign m_arsize = 3'($clog2(DW / 8));
        assign m_arburst = 2'b01;  assign m_arlock = 1'b0;  assign m_arcache = '0;
        assign m_arqos = '0;  assign m_arregion = '0;  assign m_aruser = 1'b0;
    end else if (IS_WB) begin : g_mstwb
        wb4_master_stress #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .CLASSIC(WB_CLASSIC)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_wb_CYC(wb_cyc), .m_wb_STB(wb_stb), .m_wb_WE(wb_we), .m_wb_ADR(wb_adr),
            .m_wb_DAT_W(wb_dat_w), .m_wb_SEL(wb_sel), .m_wb_STALL(wb_stall),
            .m_wb_ACK(wb_ack_m), .m_wb_ERR(wb_err_m), .m_wb_RTY(1'b0),
            .m_wb_DAT_R(m_rdata)
        );
        // The master sees the injector's response for the transfer at the head.
        wire w_rsp_err = wb_head_wr ? (m_bresp != RESP_OKAY) : (m_rresp != RESP_OKAY);
        assign wb_ack_m = wb_term && !w_rsp_err;
        assign wb_err_m = wb_term &&  w_rsp_err;
        // AXI4-shaped nets: acceptance is the AR (or AW + W), termination the
        // R (or B).
        assign m_arvalid = wb_acc && !wb_we;  assign m_arready = 1'b1;
        assign m_araddr  = wb_adr;  assign m_arprot = 3'd0;
        assign m_rvalid  = wb_term && !wb_head_wr;  assign m_rready = 1'b1;
        assign m_awvalid = wb_acc && wb_we;  assign m_awready = 1'b1;
        assign m_awaddr  = wb_adr;  assign m_awprot = 3'd0;
        assign m_wvalid  = wb_acc && wb_we;  assign m_wready = 1'b1;
        assign m_wdata   = wb_dat_w;  assign m_wstrb = wb_sel;
        assign m_bready  = 1'b1;
        assign m_awid = '0;  assign m_awlen = '0;  assign m_awsize = 3'($clog2(DW / 8));
        assign m_awburst = 2'b01;  assign m_awlock = 1'b0;  assign m_awcache = '0;
        assign m_awqos = '0;  assign m_awregion = '0;  assign m_awuser = 1'b0;
        assign m_wlast = 1'b1;  assign m_wuser = 1'b0;  assign m_wid = '0;
        assign m_arid = '0;  assign m_arlen = '0;  assign m_arsize = 3'($clog2(DW / 8));
        assign m_arburst = 2'b01;  assign m_arlock = 1'b0;  assign m_arcache = '0;
        assign m_arqos = '0;  assign m_arregion = '0;  assign m_aruser = 1'b0;
    end else begin : g_mst5
        assign m_wid = '0;
        assign m_awregion = '0;
        assign m_arregion = '0;
        /* verilator lint_off PINCONNECTEMPTY */
        axi5_master_stress #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .EN_NSAID(1'b1), .EN_TRACE(1'b1), .EN_MPAM(1'b1), .EN_MECID(1'b1), .EN_POISON(1'b1),
            .EN_UNIQUE(1'b1), .EN_ATOMIC(1'b1), .EN_MTE(1'b1)
        ) u_mst (
            .aclk, .aresetn, .go, .stop,
            .cfg_rd (cfg_mrd), .cfg_wr (cfg_mwr), .cfg_win (w_win), .cfg_hash_seed,
            .sts_rd (w_sts_mrd), .sts_wr (w_sts_mwr),
            .m_axi_awid(m_awid), .m_axi_awaddr(m_awaddr), .m_axi_awlen(m_awlen),
            .m_axi_awsize(m_awsize), .m_axi_awburst(m_awburst), .m_axi_awlock(m_awlock),
            .m_axi_awcache(m_awcache), .m_axi_awprot(m_awprot), .m_axi_awqos(m_awqos),
            .m_axi_awuser(m_awuser), .m_axi_awvalid(m_awvalid), .m_axi_awready(m_awready),
            .m_axi_awatop(m_awatop), .m_axi_awnsaid(m_awnsaid), .m_axi_awtrace(m_awtrace),
            .m_axi_awmpam(m_awmpam), .m_axi_awmecid(m_awmecid), .m_axi_awidunq(m_awidunq),
            .m_axi_awtagop(m_awtagop), .m_axi_awakeup(),
            .m_axi_wdata(m_wdata), .m_axi_wstrb(m_wstrb), .m_axi_wlast(m_wlast),
            .m_axi_wuser(m_wuser), .m_axi_wvalid(m_wvalid), .m_axi_wready(m_wready),
            .m_axi_wpoison(m_wpoison), .m_axi_wtag(m_wtag), .m_axi_wtagupdate(m_wtagupdate),
            .m_axi_bid(m_bid), .m_axi_bresp(m_bresp), .m_axi_buser(m_buser),
            .m_axi_bvalid(m_bvalid), .m_axi_bready(m_bready),
            .m_axi_btrace(m_btrace), .m_axi_bidunq(m_bidunq), .m_axi_btagmatch(m_btagmatch),
            .m_axi_arid(m_arid), .m_axi_araddr(m_araddr), .m_axi_arlen(m_arlen),
            .m_axi_arsize(m_arsize), .m_axi_arburst(m_arburst), .m_axi_arlock(m_arlock),
            .m_axi_arcache(m_arcache), .m_axi_arprot(m_arprot), .m_axi_arqos(m_arqos),
            .m_axi_aruser(m_aruser), .m_axi_arvalid(m_arvalid), .m_axi_arready(m_arready),
            .m_axi_arnsaid(m_arnsaid), .m_axi_artrace(m_artrace), .m_axi_armpam(m_armpam),
            .m_axi_armecid(m_armecid), .m_axi_aridunq(m_aridunq), .m_axi_archunken(), .m_axi_artagop(m_artagop),
            .m_axi_rid(m_rid), .m_axi_rdata(m_rdata), .m_axi_rresp(m_rresp),
            .m_axi_rlast(m_rlast), .m_axi_ruser(m_ruser),
            .m_axi_rvalid(m_rvalid), .m_axi_rready(m_rready),
            .m_axi_rtrace(m_rtrace), .m_axi_ridunq(m_ridunq), .m_axi_rpoison(m_rpoison),
            .m_axi_rchunkv(1'b0), .m_axi_rchunknum(4'd0), .m_axi_rchunkstrb('0), .m_axi_rtag(m_rtag)
        );
        /* verilator lint_on PINCONNECTEMPTY */
    end endgenerate

    // The APB bus nets exist only with APB4.
    generate if (!IS_APB) begin : g_no_apb
        assign p_sel = 1'b0;  assign p_enable = 1'b0;  assign p_write = 1'b0;
        assign p_wakeup = 1'b0;
        assign p_ready = 1'b0;  assign p_slverr_m = 1'b0;  assign p_slverr_s = 1'b0;
        assign p_addr = '0;  assign p_wdata = '0;  assign p_rdata_s = '0;
        assign p_strb = '0;  assign p_prot = '0;
    end endgenerate

    // The Wishbone bus nets exist only with WB4.
    generate if (!IS_WB) begin : g_no_wb
        assign wb_cyc = 1'b0;  assign wb_stb = 1'b0;  assign wb_we = 1'b0;
        assign wb_stall = 1'b0;  assign wb_ack_s = 1'b0;  assign wb_err_s = 1'b0;
        assign wb_rty_s = 1'b0;  assign wb_ack_m = 1'b0;  assign wb_err_m = 1'b0;
        assign wb_adr = '0;  assign wb_dat_w = '0;  assign wb_dat_r_s = '0;  assign wb_sel = '0;
    end endgenerate

    // TRACE / POISON: AXI5 and AXI5-Lite carry them; tied 0 for the others.
    generate if (PROTO != 2 && PROTO != 4) begin : g_no_tp
        assign m_awtrace = '0;
        assign m_artrace = '0;
        assign m_wpoison = '0;
        assign s_rtrace  = '0;
        assign s_rpoison = '0;
        assign s_btrace  = '0;
    end endgenerate

    // The rest of the AXI5 sideband: AXI5 only.
    generate if (PROTO != 2) begin : g_no_sb
        assign m_awnsaid = '0;
        assign m_arnsaid = '0;
        assign m_awmpam  = '0;
        assign m_armpam  = '0;
        assign m_awmecid = '0;
        assign m_armecid = '0;
        assign m_aridunq = '0;
        assign m_awidunq = '0;
        assign m_awatop  = '0;
        assign m_awtagop = '0;
        assign m_artagop = '0;
        assign m_wtag    = '0;
        assign m_wtagupdate = '0;
        assign s_rtag    = '0;
        assign s_btagmatch = '0;
        assign s_ridunq  = '0;
        assign s_bidunq  = '0;
    end endgenerate

    // ---- fault injector ----------------------------------------------------------
    logic [23:0] r_armed;
    logic [7:0]  r_rd_out [1 << IW];      // read bursts outstanding per ID, on the wire
    wire w_r_hs  = m_rvalid  && m_rready;
    wire w_w_hs  = m_wvalid  && m_wready;
    wire w_b_hs  = m_bvalid  && m_bready;

    // hold_b: the slave keeps its B and the master sees none, for as long as
    // a test holds it -- a single burst can then outlast any latency counter
    logic s_bvalid, s_bready;
    assign m_bvalid = s_bvalid && !hold_b;
    assign s_bready = m_bready && !hold_b;
    wire w_ar_hs = m_arvalid && m_arready;

    wire w_aw_hs = m_awvalid && m_awready;

    logic [23:0] w_fire;
    always_comb begin
        w_fire    = '0;
        w_fire[0] = r_armed[0] && w_r_hs;
        w_fire[1] = r_armed[1] && w_r_hs;
        w_fire[2] = r_armed[2] && w_r_hs && s_rlast;
        // APB: a completer samples PADDR / PWDATA from the setup phase on,
        // not at PREADY, so the request faults fire at a transfer's setup
        // and are held to its end (r_p_flip) -- keyed to the completing
        // cycle they could arm mid-transfer, after the slave had sampled.
        w_fire[3] = IS_APB ? (r_armed[3] && p_setup && p_write && p_strb[0])
                  : IS_WB  ? (r_armed[3] && wb_start && wb_we && wb_sel[0])
                           : (r_armed[3] && w_w_hs && m_wstrb[0]);
        w_fire[4] = r_armed[4] && w_b_hs;
        w_fire[5] = IS_APB ? (r_armed[5] && p_setup && !p_write)
                  : IS_WB  ? (r_armed[5] && wb_start && !wb_we)
                           : (r_armed[5] && w_ar_hs);
        w_fire[6] = r_armed[6] && w_b_hs;
        w_fire[7] = r_armed[7] && w_r_hs;
        w_fire[8] = r_armed[8] && w_w_hs;
        w_fire[9]  = r_armed[9]  && w_ar_hs;
        w_fire[10] = r_armed[10] && w_w_hs;
        w_fire[11] = r_armed[11] && w_r_hs;
        w_fire[12] = r_armed[12] && w_r_hs;
        w_fire[13] = r_armed[13] && w_b_hs;
        w_fire[14] = r_armed[14] && w_aw_hs;
        w_fire[15] = r_armed[15] && w_r_hs;
        w_fire[16] = r_armed[16] && w_b_hs;
        w_fire[17] = r_armed[17] && w_ar_hs && (r_rd_out[m_arid] > 8'd1) && !m_aridunq;
        w_fire[18] = r_armed[18] && w_r_hs && s_rid[IW-1] && (s_rresp == RESP_OKAY);
        w_fire[19] = r_armed[19] && w_aw_hs && (m_awatop != 6'd0);
        w_fire[20] = r_armed[20] && w_w_hs;
        w_fire[21] = r_armed[21] && w_r_hs && !s_rid[IW-1];
        w_fire[22] = r_armed[22] && w_b_hs;
        w_fire[23] = r_armed[23] && w_ar_hs;
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_armed  <= '0;
            flt_done <= '0;
            r_p_flip <= '0;
            r_wbq    <= '0;
            r_wbq_n  <= '0;
            r_wb_open <= 1'b0;
            for (int i = 0; i < (1 << IW); i++) r_rd_out[i] <= '0;
        end else begin
            r_armed  <= (r_armed & ~w_fire) | flt_arm;
            if (wb_term)                    r_wb_open <= 1'b0;
            else if (wb_cyc && wb_stb)      r_wb_open <= 1'b1;
            // direction queue: pop a termination, push an acceptance; in
            // classic mode both fall in one cycle and the queue stays empty
            if (wb_term && wb_acc && r_wbq_n == '0) begin
                r_wbq <= r_wbq;
            end else begin
                automatic logic [DEPTH:0] q = r_wbq;
                automatic logic [$clog2(DEPTH+2)-1:0] n = r_wbq_n;
                if (wb_term) begin q = q >> 1; n = n - 1'b1; end
                if (wb_acc)  begin q[n] = wb_we; n = n + 1'b1; end
                r_wbq   <= q;
                r_wbq_n <= n;
            end
            if (IS_APB ? p_xfer : wb_term)  r_p_flip <= 2'b00;
            else if (REQ_HOLD) begin
                if (w_fire[3])             r_p_flip[0] <= 1'b1;
                if (w_fire[5])             r_p_flip[1] <= 1'b1;
            end
            flt_done <= (flt_done | w_fire) & ~flt_arm;
            for (int i = 0; i < (1 << IW); i++)
                r_rd_out[i] <= r_rd_out[i] + 8'(w_ar_hs && (m_arid == IW'(i)))
                                           - 8'(w_r_hs && m_rlast && (m_rid == IW'(i)));
        end
    end

    assign m_rdata  = s_rdata ^ ((r_armed[0] || (r_armed[18] && s_rid[IW-1] && (s_rresp == RESP_OKAY)))
                                 ? {(DW/8){8'h01}} : '0);
    assign m_rid    = s_rid   ^ IW'(r_armed[1]);
    assign m_rlast  = s_rlast && !r_armed[2];
    assign m_rresp  = r_armed[7] ? RESP_SLVERR : s_rresp;
    assign s_wdata  = m_wdata ^ DW'((IS_APB || IS_WB) ? (r_p_flip[0] || w_fire[3])
                                                      : (r_armed[3] && m_wstrb[0]));
    assign m_bid    = s_bid   ^ IW'(r_armed[4]);
    assign m_bresp  = r_armed[6] ? RESP_SLVERR : s_bresp;
    localparam int FLT_ADDR_BIT = (OFFSET_LG2 > 0) ? OFFSET_LG2 - 1 : 31;
    assign s_araddr = m_araddr ^ (32'((IS_APB || IS_WB) ? (r_p_flip[1] || w_fire[5])
                                                        : r_armed[5]) << FLT_ADDR_BIT);
    assign s_wid    = m_wid   ^ IW'(r_armed[8]);
    assign s_artrace = m_artrace ^ r_armed[9];
    assign s_wpoison = m_wpoison ^ r_armed[10];
    assign m_rtrace  = s_rtrace  ^ r_armed[11];
    assign m_rpoison = s_rpoison ^ r_armed[12];
    assign m_btrace  = s_btrace  ^ r_armed[13];
    assign s_awmecid = m_awmecid ^ 16'(r_armed[14]);
    assign m_ridunq  = s_ridunq  ^ r_armed[15];
    assign m_bidunq  = s_bidunq  ^ r_armed[16];
    assign s_aridunq = m_aridunq || w_fire[17];
    assign s_awatop  = (r_armed[19] && (m_awatop != 6'd0)) ? 6'b110010 : m_awatop;
    assign s_wtag      = m_wtag      ^ TW'(r_armed[20]);
    assign m_rtag      = s_rtag      ^ TW'(r_armed[21] && !s_rid[IW-1]);
    assign m_btagmatch = s_btagmatch ^ 2'(r_armed[22]);
    assign s_artagop   = m_artagop   ^ 2'(r_armed[23]);

    generate if (PROTO == 0) begin : g_slv4
        axi4_slave_stress #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_axi_awid(m_awid), .s_axi_awaddr(m_awaddr), .s_axi_awlen(m_awlen),
            .s_axi_awsize(m_awsize), .s_axi_awburst(m_awburst), .s_axi_awlock(m_awlock),
            .s_axi_awcache(m_awcache), .s_axi_awprot(m_awprot), .s_axi_awqos(m_awqos),
            .s_axi_awregion(m_awregion), .s_axi_awuser(m_awuser),
            .s_axi_awvalid(m_awvalid), .s_axi_awready(m_awready),
            .s_axi_wdata(s_wdata), .s_axi_wstrb(m_wstrb), .s_axi_wlast(m_wlast),
            .s_axi_wuser(m_wuser), .s_axi_wvalid(m_wvalid), .s_axi_wready(m_wready),
            .s_axi_bid(s_bid), .s_axi_bresp(s_bresp), .s_axi_buser(m_buser),
            .s_axi_bvalid(s_bvalid), .s_axi_bready(s_bready),
            .s_axi_arid(m_arid), .s_axi_araddr(s_araddr), .s_axi_arlen(m_arlen),
            .s_axi_arsize(m_arsize), .s_axi_arburst(m_arburst), .s_axi_arlock(m_arlock),
            .s_axi_arcache(m_arcache), .s_axi_arprot(m_arprot), .s_axi_arqos(m_arqos),
            .s_axi_arregion(m_arregion), .s_axi_aruser(m_aruser),
            .s_axi_arvalid(m_arvalid), .s_axi_arready(m_arready),
            .s_axi_rid(s_rid), .s_axi_rdata(s_rdata), .s_axi_rresp(s_rresp),
            .s_axi_rlast(s_rlast), .s_axi_ruser(m_ruser),
            .s_axi_rvalid(m_rvalid), .s_axi_rready(m_rready)
        );
    end else if (PROTO == 1) begin : g_slv3
        axi3_slave_stress #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_axi_awid(m_awid), .s_axi_awaddr(m_awaddr), .s_axi_awlen(m_awlen[3:0]),
            .s_axi_awsize(m_awsize), .s_axi_awburst(m_awburst), .s_axi_awlock({1'b0, m_awlock}),
            .s_axi_awcache(m_awcache), .s_axi_awprot(m_awprot), .s_axi_awuser(m_awuser),
            .s_axi_awvalid(m_awvalid), .s_axi_awready(m_awready),
            .s_axi_wid(s_wid),
            .s_axi_wdata(s_wdata), .s_axi_wstrb(m_wstrb), .s_axi_wlast(m_wlast),
            .s_axi_wuser(m_wuser), .s_axi_wvalid(m_wvalid), .s_axi_wready(m_wready),
            .s_axi_bid(s_bid), .s_axi_bresp(s_bresp), .s_axi_buser(m_buser),
            .s_axi_bvalid(s_bvalid), .s_axi_bready(s_bready),
            .s_axi_arid(m_arid), .s_axi_araddr(s_araddr), .s_axi_arlen(m_arlen[3:0]),
            .s_axi_arsize(m_arsize), .s_axi_arburst(m_arburst), .s_axi_arlock({1'b0, m_arlock}),
            .s_axi_arcache(m_arcache), .s_axi_arprot(m_arprot), .s_axi_aruser(m_aruser),
            .s_axi_arvalid(m_arvalid), .s_axi_arready(m_arready),
            .s_axi_rid(s_rid), .s_axi_rdata(s_rdata), .s_axi_rresp(s_rresp),
            .s_axi_rlast(s_rlast), .s_axi_ruser(m_ruser),
            .s_axi_rvalid(m_rvalid), .s_axi_rready(m_rready)
        );
    end else if (PROTO == 3) begin : g_slvl4
        axil4_slave_stress #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_axil_awaddr(m_awaddr), .s_axil_awprot(m_awprot),
            .s_axil_awvalid(m_awvalid), .s_axil_awready(m_awready),
            .s_axil_wdata(s_wdata), .s_axil_wstrb(m_wstrb),
            .s_axil_wvalid(m_wvalid), .s_axil_wready(m_wready),
            .s_axil_bresp(s_bresp), .s_axil_bvalid(s_bvalid), .s_axil_bready(s_bready),
            .s_axil_araddr(s_araddr), .s_axil_arprot(m_arprot),
            .s_axil_arvalid(m_arvalid), .s_axil_arready(m_arready),
            .s_axil_rdata(s_rdata), .s_axil_rresp(s_rresp),
            .s_axil_rvalid(m_rvalid), .s_axil_rready(m_rready)
        );
        assign s_bid = '0;  assign s_rid = '0;  assign s_rlast = 1'b1;
        assign m_buser = 1'b0;  assign m_ruser = 1'b0;
    end else if (PROTO == 4) begin : g_slvl5
        axil5_slave_stress #(
            .EN_TRACE(1'b1), .EN_POISON(1'b1),
            .DEPTH(DEPTH), .IW(IW), .DW(DW)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_axil_awid(m_awid), .s_axil_awaddr(m_awaddr), .s_axil_awprot(m_awprot),
            .s_axil_awtrace(m_awtrace),
            .s_axil_awvalid(m_awvalid), .s_axil_awready(m_awready),
            .s_axil_wdata(s_wdata), .s_axil_wstrb(m_wstrb), .s_axil_wpoison(s_wpoison),
            .s_axil_wvalid(m_wvalid), .s_axil_wready(m_wready),
            .s_axil_bid(s_bid), .s_axil_bresp(s_bresp), .s_axil_btrace(s_btrace),
            .s_axil_bvalid(s_bvalid), .s_axil_bready(s_bready),
            .s_axil_arid(m_arid), .s_axil_araddr(s_araddr), .s_axil_arprot(m_arprot),
            .s_axil_artrace(s_artrace),
            .s_axil_arvalid(m_arvalid), .s_axil_arready(m_arready),
            .s_axil_rid(s_rid), .s_axil_rdata(s_rdata), .s_axil_rresp(s_rresp),
            .s_axil_rtrace(s_rtrace), .s_axil_rpoison(s_rpoison),
            .s_axil_rvalid(m_rvalid), .s_axil_rready(m_rready)
        );
        assign s_rlast = 1'b1;
        assign m_buser = 1'b0;  assign m_ruser = 1'b0;
    end else if (IS_APB) begin : g_slvp
        if (PROTO == 5) begin : g_p4
            apb4_slave_stress #(
                .DEPTH(DEPTH), .IW(IW), .DW(DW)
            ) u_slv (
                .aclk, .aresetn, .clear,
                .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
                .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
                .s_apb_PSEL(p_sel), .s_apb_PENABLE(p_enable), .s_apb_PREADY(p_ready),
                .s_apb_PADDR((p_write ? m_awaddr : s_araddr) & OFFSET_MASK),
                .s_apb_PWRITE(p_write), .s_apb_PWDATA(s_wdata), .s_apb_PSTRB(m_wstrb),
                .s_apb_PPROT(p_prot),
                .s_apb_PRDATA(p_rdata_s), .s_apb_PSLVERR(p_slverr_s)
            );
        end else begin : g_p5
            apb5_slave_stress #(
                .DEPTH(DEPTH), .IW(IW), .DW(DW)
            ) u_slv (
                .aclk, .aresetn, .clear,
                .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
                .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
                .s_apb_PSEL(p_sel), .s_apb_PENABLE(p_enable), .s_apb_PREADY(p_ready),
                .s_apb_PADDR((p_write ? m_awaddr : s_araddr) & OFFSET_MASK),
                .s_apb_PWRITE(p_write), .s_apb_PWDATA(s_wdata), .s_apb_PSTRB(m_wstrb),
                .s_apb_PPROT(p_prot),
                .s_apb_PRDATA(p_rdata_s), .s_apb_PSLVERR(p_slverr_s),
                .s_apb_PWAKEUP(p_wakeup)
            );
        end
        assign s_rdata  = p_rdata_s;
        assign s_rresp  = p_slverr_s ? RESP_SLVERR : RESP_OKAY;
        assign s_bresp  = p_slverr_s ? RESP_SLVERR : RESP_OKAY;
        assign s_bvalid = p_xfer && p_write;
        assign s_bid = '0;  assign s_rid = '0;  assign s_rlast = 1'b1;
        assign m_buser = 1'b0;  assign m_ruser = 1'b0;
    end else if (IS_WB) begin : g_slvwb
        wb4_slave_stress #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .CLASSIC(WB_CLASSIC)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_wb_CYC(wb_cyc), .s_wb_STB(wb_stb), .s_wb_WE(wb_we),
            .s_wb_ADR(wb_we ? m_awaddr : s_araddr),
            .s_wb_DAT_W(s_wdata), .s_wb_SEL(m_wstrb), .s_wb_STALL(wb_stall),
            .s_wb_ACK(wb_ack_s), .s_wb_ERR(wb_err_s), .s_wb_RTY(wb_rty_s),
            .s_wb_DAT_R(wb_dat_r_s)
        );
        assign s_rdata  = wb_dat_r_s;
        assign s_rresp  = wb_ack_s ? RESP_OKAY : RESP_SLVERR;
        assign s_bresp  = wb_ack_s ? RESP_OKAY : RESP_SLVERR;
        assign s_bvalid = wb_term && wb_head_wr;
        assign s_bid = '0;  assign s_rid = '0;  assign s_rlast = 1'b1;
        assign m_buser = 1'b0;  assign m_ruser = 1'b0;
    end else begin : g_slv5
        /* verilator lint_off PINCONNECTEMPTY */
        axi5_slave_stress #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1),
            .EN_NSAID(1'b1), .EN_TRACE(1'b1), .EN_MPAM(1'b1), .EN_MECID(1'b1), .EN_POISON(1'b1),
            .EN_UNIQUE(1'b1), .EN_ATOMIC(1'b1), .EN_MTE(1'b1)
        ) u_slv (
            .aclk, .aresetn, .clear,
            .cfg_rd (cfg_srd), .cfg_wr (cfg_swr), .cfg_hash_seed,
            .sts_rd (w_sts_srd), .sts_wr (w_sts_swr),
            .s_axi_awid(m_awid), .s_axi_awaddr(m_awaddr), .s_axi_awlen(m_awlen),
            .s_axi_awsize(m_awsize), .s_axi_awburst(m_awburst), .s_axi_awlock(m_awlock),
            .s_axi_awcache(m_awcache), .s_axi_awprot(m_awprot), .s_axi_awqos(m_awqos),
            .s_axi_awuser(m_awuser), .s_axi_awvalid(m_awvalid), .s_axi_awready(m_awready),
            .s_axi_awatop(s_awatop), .s_axi_awnsaid(m_awnsaid), .s_axi_awtrace(m_awtrace),
            .s_axi_awmpam(m_awmpam), .s_axi_awmecid(s_awmecid), .s_axi_awidunq(m_awidunq),
            .s_axi_awtagop(m_awtagop), .s_axi_awakeup(1'b0),
            .s_axi_wdata(s_wdata), .s_axi_wstrb(m_wstrb), .s_axi_wlast(m_wlast),
            .s_axi_wuser(m_wuser), .s_axi_wvalid(m_wvalid), .s_axi_wready(m_wready),
            .s_axi_wpoison(s_wpoison), .s_axi_wtag(s_wtag), .s_axi_wtagupdate(m_wtagupdate),
            .s_axi_bid(s_bid), .s_axi_bresp(s_bresp), .s_axi_buser(m_buser),
            .s_axi_bvalid(s_bvalid), .s_axi_bready(s_bready),
            .s_axi_btrace(s_btrace), .s_axi_bidunq(s_bidunq), .s_axi_btagmatch(s_btagmatch),
            .s_axi_arid(m_arid), .s_axi_araddr(s_araddr), .s_axi_arlen(m_arlen),
            .s_axi_arsize(m_arsize), .s_axi_arburst(m_arburst), .s_axi_arlock(m_arlock),
            .s_axi_arcache(m_arcache), .s_axi_arprot(m_arprot), .s_axi_arqos(m_arqos),
            .s_axi_aruser(m_aruser), .s_axi_arvalid(m_arvalid), .s_axi_arready(m_arready),
            .s_axi_arnsaid(m_arnsaid), .s_axi_artrace(s_artrace), .s_axi_armpam(m_armpam),
            .s_axi_armecid(m_armecid), .s_axi_aridunq(s_aridunq), .s_axi_archunken(1'b0),
            .s_axi_artagop(s_artagop),
            .s_axi_rid(s_rid), .s_axi_rdata(s_rdata), .s_axi_rresp(s_rresp),
            .s_axi_rlast(s_rlast), .s_axi_ruser(m_ruser),
            .s_axi_rvalid(m_rvalid), .s_axi_rready(m_rready),
            .s_axi_rtrace(s_rtrace), .s_axi_ridunq(s_ridunq), .s_axi_rpoison(s_rpoison),
            .s_axi_rchunkv(), .s_axi_rchunknum(), .s_axi_rchunkstrb(), .s_axi_rtag(s_rtag)
        );
        /* verilator lint_on PINCONNECTEMPTY */
    end endgenerate

endmodule : tb_axi_stress_pair
