// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_axi4_arb
// Purpose: peregrine's house AXI4 arbiter (PRD P7): NM masters (the I$
//          refill, the D$, the uncached port) merged onto one fabric port.
//
//          - AR and AW are arbitrated independently, each by
//            arbiter_round_robin in ACK mode: the grant is registered and
//            held until the granted address handshake (the ack), so the
//            selected master's address is stable while it waits.
//          - The response is routed by id: the fabric id is
//            {master index, master id}, so R and B return to the master
//            that issued them, and reads from different masters may be in
//            flight together.
//          - W follows AW: an AW grant makes its master the W owner until
//            the W beat with wlast, and no other AW is granted meanwhile.
//            Writes are therefore serialized; every master here has at
//            most one write in flight (the D$ write-back, the uncached
//            store), so this costs nothing and needs no W-order FIFO.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - NM: number of masters (>= 2).
//   - AXI_DW: data width.
//   - AXI_IW: master-side id width; the fabric side is AXI_IW + clog2(NM).
//
// Notes:
//   - The AxLOCK/CACHE/PROT/QOS/REGION/USER fields are not carried: no
//     master here drives them and the fabric memory ignores them.  The
//     fabric port drives them 0.
//   - Grant latency: one cycle from a master raising its valid to the
//     fabric valid (the registered grant).
//
// Related Modules:
//   - arbiter_round_robin (rtl/common)
//   - peregrine_top
//
// Test:
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_axi4_arb.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_axi4_arb #(
    parameter int NM     = 3,
    parameter int AXI_DW = 64,
    parameter int AXI_IW = 4,
    localparam int MI_W  = $clog2(NM),
    localparam int FIW   = AXI_IW + MI_W,
    localparam int STRBW = AXI_DW / 8
) (
    input  logic                     clk,
    input  logic                     rst_n,

    // ---------------- master side (flattened per master) -------------
    input  logic [NM*AXI_IW-1:0]     s_axi_arid,
    input  logic [NM*32-1:0]         s_axi_araddr,
    input  logic [NM*8-1:0]          s_axi_arlen,
    input  logic [NM*3-1:0]          s_axi_arsize,
    input  logic [NM*2-1:0]          s_axi_arburst,
    input  logic [NM-1:0]            s_axi_arvalid,
    output logic [NM-1:0]            s_axi_arready,
    output logic [NM*AXI_IW-1:0]     s_axi_rid,
    output logic [NM*AXI_DW-1:0]     s_axi_rdata,
    output logic [NM*2-1:0]          s_axi_rresp,
    output logic [NM-1:0]            s_axi_rlast,
    output logic [NM-1:0]            s_axi_rvalid,
    input  logic [NM-1:0]            s_axi_rready,

    input  logic [NM*AXI_IW-1:0]     s_axi_awid,
    input  logic [NM*32-1:0]         s_axi_awaddr,
    input  logic [NM*8-1:0]          s_axi_awlen,
    input  logic [NM*3-1:0]          s_axi_awsize,
    input  logic [NM*2-1:0]          s_axi_awburst,
    input  logic [NM-1:0]            s_axi_awvalid,
    output logic [NM-1:0]            s_axi_awready,
    input  logic [NM*AXI_DW-1:0]     s_axi_wdata,
    input  logic [NM*STRBW-1:0]      s_axi_wstrb,
    input  logic [NM-1:0]            s_axi_wlast,
    input  logic [NM-1:0]            s_axi_wvalid,
    output logic [NM-1:0]            s_axi_wready,
    output logic [NM*AXI_IW-1:0]     s_axi_bid,
    output logic [NM*2-1:0]          s_axi_bresp,
    output logic [NM-1:0]            s_axi_bvalid,
    input  logic [NM-1:0]            s_axi_bready,

    // ---------------- fabric side -------------------------------------
    output logic [FIW-1:0]           m_axi_arid,
    output logic [31:0]              m_axi_araddr,
    output logic [7:0]               m_axi_arlen,
    output logic [2:0]               m_axi_arsize,
    output logic [1:0]               m_axi_arburst,
    output logic                     m_axi_arlock,
    output logic [3:0]               m_axi_arcache,
    output logic [2:0]               m_axi_arprot,
    output logic [3:0]               m_axi_arqos,
    output logic [3:0]               m_axi_arregion,
    output logic                     m_axi_arvalid,
    input  logic                     m_axi_arready,
    input  logic [FIW-1:0]           m_axi_rid,
    input  logic [AXI_DW-1:0]        m_axi_rdata,
    input  logic [1:0]               m_axi_rresp,
    input  logic                     m_axi_rlast,
    input  logic                     m_axi_rvalid,
    output logic                     m_axi_rready,

    output logic [FIW-1:0]           m_axi_awid,
    output logic [31:0]              m_axi_awaddr,
    output logic [7:0]               m_axi_awlen,
    output logic [2:0]               m_axi_awsize,
    output logic [1:0]               m_axi_awburst,
    output logic                     m_axi_awlock,
    output logic [3:0]               m_axi_awcache,
    output logic [2:0]               m_axi_awprot,
    output logic [3:0]               m_axi_awqos,
    output logic [3:0]               m_axi_awregion,
    output logic                     m_axi_awvalid,
    input  logic                     m_axi_awready,
    output logic [AXI_DW-1:0]        m_axi_wdata,
    output logic [STRBW-1:0]         m_axi_wstrb,
    output logic                     m_axi_wlast,
    output logic                     m_axi_wvalid,
    input  logic                     m_axi_wready,
    input  logic [FIW-1:0]           m_axi_bid,
    input  logic [1:0]               m_axi_bresp,
    input  logic                     m_axi_bvalid,
    output logic                     m_axi_bready
);

    initial begin
        if (NM < 2) $error("peregrine_axi4_arb: NM must be >= 2");
    end

    // -----------------------------------------------------------------
    // AR: registered grant held to the handshake
    // -----------------------------------------------------------------
    logic            w_ar_gvalid;
    logic [NM-1:0]   w_ar_grant;
    logic [MI_W-1:0] w_ar_gid;
    logic [NM-1:0]   w_ar_ack;

    arbiter_round_robin #(
        .CLIENTS      (NM),
        .WAIT_GNT_ACK (1)
    ) u_ar_arb (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (1'b0),
        .request     (s_axi_arvalid),
        .grant_ack   (w_ar_ack),
        .grant_valid (w_ar_gvalid),
        .grant       (w_ar_grant),
        .grant_id    (w_ar_gid),
        .last_grant  ()
    );

    assign m_axi_arvalid  = w_ar_gvalid & s_axi_arvalid[w_ar_gid];
    assign m_axi_arid     = {w_ar_gid, s_axi_arid[w_ar_gid * AXI_IW +: AXI_IW]};
    assign m_axi_araddr   = s_axi_araddr[w_ar_gid * 32 +: 32];
    assign m_axi_arlen    = s_axi_arlen[w_ar_gid * 8 +: 8];
    assign m_axi_arsize   = s_axi_arsize[w_ar_gid * 3 +: 3];
    assign m_axi_arburst  = s_axi_arburst[w_ar_gid * 2 +: 2];
    assign m_axi_arlock   = 1'b0;
    assign m_axi_arcache  = 4'd0;
    assign m_axi_arprot   = 3'd0;
    assign m_axi_arqos    = 4'd0;
    assign m_axi_arregion = 4'd0;
    assign s_axi_arready  = (w_ar_gvalid & m_axi_arready) ? w_ar_grant : '0;
    assign w_ar_ack       = (m_axi_arvalid & m_axi_arready) ? w_ar_grant : '0;

    // R: route by the id's master field
    logic [MI_W-1:0] w_r_mi;
    assign w_r_mi = m_axi_rid[FIW-1 -: MI_W];

    always_comb begin
        for (int i = 0; i < NM; i++) begin
            s_axi_rid[i * AXI_IW +: AXI_IW] = m_axi_rid[AXI_IW-1:0];
            s_axi_rdata[i * AXI_DW +: AXI_DW] = m_axi_rdata;
            s_axi_rresp[i * 2 +: 2] = m_axi_rresp;
            s_axi_rlast[i] = m_axi_rlast;
            s_axi_rvalid[i] = m_axi_rvalid & (w_r_mi == MI_W'(i));
        end
    end
    assign m_axi_rready = s_axi_rready[w_r_mi];

    // -----------------------------------------------------------------
    // AW: same arbiter, blocked while a W burst is owed
    // -----------------------------------------------------------------
    logic            w_aw_gvalid;
    logic [NM-1:0]   w_aw_grant;
    logic [MI_W-1:0] w_aw_gid;
    logic [NM-1:0]   w_aw_ack;
    logic            r_w_busy;
    logic [MI_W-1:0] r_w_owner;
    logic            w_aw_hs;
    logic            w_w_last_hs;

    arbiter_round_robin #(
        .CLIENTS      (NM),
        .WAIT_GNT_ACK (1)
    ) u_aw_arb (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (r_w_busy),
        .request     (s_axi_awvalid),
        .grant_ack   (w_aw_ack),
        .grant_valid (w_aw_gvalid),
        .grant       (w_aw_grant),
        .grant_id    (w_aw_gid),
        .last_grant  ()
    );

    assign m_axi_awvalid  = w_aw_gvalid & ~r_w_busy & s_axi_awvalid[w_aw_gid];
    assign m_axi_awid     = {w_aw_gid, s_axi_awid[w_aw_gid * AXI_IW +: AXI_IW]};
    assign m_axi_awaddr   = s_axi_awaddr[w_aw_gid * 32 +: 32];
    assign m_axi_awlen    = s_axi_awlen[w_aw_gid * 8 +: 8];
    assign m_axi_awsize   = s_axi_awsize[w_aw_gid * 3 +: 3];
    assign m_axi_awburst  = s_axi_awburst[w_aw_gid * 2 +: 2];
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = 4'd0;
    assign m_axi_awprot   = 3'd0;
    assign m_axi_awqos    = 4'd0;
    assign m_axi_awregion = 4'd0;
    assign w_aw_hs        = m_axi_awvalid & m_axi_awready;
    assign s_axi_awready  = w_aw_hs ? w_aw_grant : '0;
    assign w_aw_ack       = w_aw_hs ? w_aw_grant : '0;

    assign w_w_last_hs = m_axi_wvalid & m_axi_wready & m_axi_wlast;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_w_busy  <= 1'b0;
            r_w_owner <= '0;
        end else begin
            if (w_aw_hs) begin
                r_w_busy  <= 1'b1;
                r_w_owner <= w_aw_gid;
            end else if (w_w_last_hs) begin
                r_w_busy  <= 1'b0;
            end
        end
    )

    // W: only the owner's beats pass, and only once its AW is accepted.
    assign m_axi_wvalid = r_w_busy & s_axi_wvalid[r_w_owner];
    assign m_axi_wdata  = s_axi_wdata[r_w_owner * AXI_DW +: AXI_DW];
    assign m_axi_wstrb  = s_axi_wstrb[r_w_owner * STRBW +: STRBW];
    assign m_axi_wlast  = s_axi_wlast[r_w_owner];
    always_comb begin
        for (int i = 0; i < NM; i++) begin
            s_axi_wready[i] = r_w_busy & m_axi_wready & (r_w_owner == MI_W'(i));
        end
    end

    // B: route by id
    logic [MI_W-1:0] w_b_mi;
    assign w_b_mi = m_axi_bid[FIW-1 -: MI_W];

    always_comb begin
        for (int i = 0; i < NM; i++) begin
            s_axi_bid[i * AXI_IW +: AXI_IW] = m_axi_bid[AXI_IW-1:0];
            s_axi_bresp[i * 2 +: 2] = m_axi_bresp;
            s_axi_bvalid[i] = m_axi_bvalid & (w_b_mi == MI_W'(i));
        end
    end
    assign m_axi_bready = s_axi_bready[w_b_mi];

endmodule : peregrine_axi4_arb
