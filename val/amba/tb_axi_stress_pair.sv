// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_axi_stress_pair
// Purpose: Simulation harness: axi{4,3,5}_master_stress -> fault injector ->
//          axi{4,3,5}_slave_stress, back to back with no fabric between them.
//
// PROTO selects the shells: 0 = AXI4, 1 = AXI3, 2 = AXI5. The nets below are
// AXI4 shaped either way (AxLEN 8 bits, AxLOCK 1 bit), so the Python monitor
// reads one set of names; with AXI3 the upper AxLEN bits are tied 0 and m_wid
// carries WID. AXI5 builds both shells with NSAID, TRACE, MPAM, MECID, POISON,
// UNIQUE, ATOMIC and MTE, and adds the m_*trace / m_*poison / m_*nsaid / m_*mpam / m_*mecid
// nets; they are 0 for AXI3 / AXI4.
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
//   [5] AR: flip ARADDR bit 31               -> slave  ERR_S_ADDR
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
    parameter int PROTO = 0            // 0 = AXI4, 1 = AXI3, 2 = AXI5
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

    generate if (PROTO != 2) begin : g_no_sb
        assign m_awnsaid = '0;
        assign m_arnsaid = '0;
        assign m_awtrace = '0;
        assign m_artrace = '0;
        assign m_awmpam  = '0;
        assign m_armpam  = '0;
        assign m_awmecid = '0;
        assign m_armecid = '0;
        assign m_wpoison = '0;
        assign s_rtrace  = '0;
        assign s_rpoison = '0;
        assign s_btrace  = '0;
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
    wire w_ar_hs = m_arvalid && m_arready;

    wire w_aw_hs = m_awvalid && m_awready;

    logic [23:0] w_fire;
    always_comb begin
        w_fire    = '0;
        w_fire[0] = r_armed[0] && w_r_hs;
        w_fire[1] = r_armed[1] && w_r_hs;
        w_fire[2] = r_armed[2] && w_r_hs && s_rlast;
        w_fire[3] = r_armed[3] && w_w_hs && m_wstrb[0];
        w_fire[4] = r_armed[4] && w_b_hs;
        w_fire[5] = r_armed[5] && w_ar_hs;
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
            for (int i = 0; i < (1 << IW); i++) r_rd_out[i] <= '0;
        end else begin
            r_armed  <= (r_armed & ~w_fire) | flt_arm;
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
    assign s_wdata  = m_wdata ^ DW'(r_armed[3] && m_wstrb[0]);
    assign m_bid    = s_bid   ^ IW'(r_armed[4]);
    assign m_bresp  = r_armed[6] ? RESP_SLVERR : s_bresp;
    assign s_araddr = m_araddr ^ {r_armed[5], 31'd0};
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
            .s_axi_bvalid(m_bvalid), .s_axi_bready(m_bready),
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
            .s_axi_bvalid(m_bvalid), .s_axi_bready(m_bready),
            .s_axi_arid(m_arid), .s_axi_araddr(s_araddr), .s_axi_arlen(m_arlen[3:0]),
            .s_axi_arsize(m_arsize), .s_axi_arburst(m_arburst), .s_axi_arlock({1'b0, m_arlock}),
            .s_axi_arcache(m_arcache), .s_axi_arprot(m_arprot), .s_axi_aruser(m_aruser),
            .s_axi_arvalid(m_arvalid), .s_axi_arready(m_arready),
            .s_axi_rid(s_rid), .s_axi_rdata(s_rdata), .s_axi_rresp(s_rresp),
            .s_axi_rlast(s_rlast), .s_axi_ruser(m_ruser),
            .s_axi_rvalid(m_rvalid), .s_axi_rready(m_rready)
        );
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
            .s_axi_bvalid(m_bvalid), .s_axi_bready(m_bready),
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
