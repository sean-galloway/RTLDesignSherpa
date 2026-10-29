// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_axi4_half_agg
// Purpose: The simple AXI aggregator at the memory controller's host edge, for
//          masters that write or read a full DRAM beat as two half-width single
//          beats (lo then hi). Two adjacent half-width single-beat commands to
//          the two halves of one full-width beat leave as ONE full-width
//          single-beat command, so the controller spends one DRAM burst on the
//          pair instead of two (each half alone is padded to a whole burst by
//          mc_wr_splitter and costs the same as a full beat).
//
//          The pairing rule is the amba axi4_aggregator_cmd core, instantiated
//          at HALF the port width so a "single" is a half-width beat and a pair
//          is one full beat. What the amba wrappers leave to the downstream
//          slave (a 2-beat narrow burst) this block folds itself, because the
//          controller's chopper has no narrow-burst support:
//            AW/AR  an aggregated command is rewritten to AxLEN = 0 at the
//                   full size, lo's address;
//            W      the two narrow beats are packed into one by strobe (each
//                   half's bytes are in its own lanes of the full word);
//            B      the one downstream B is presented upstream twice;
//            R      the one downstream beat is presented upstream twice with
//                   RLAST on both (each half reads its own lanes of the word).
//          Side queues (gaxi_fifo_sync, one bit per issued command: agg) carry
//          the decision from AW to W and B, and from AR to R, in issue order.
//          W is held until its AW has issued (the queue must have the entry);
//          R replay assumes the controller returns R bursts in AR order, which
//          mc_rd_return_ring guarantees.
//
//          A lone lo waits HOLD_CYCLES for its hi, then leaves alone (it costs
//          those cycles of latency on single half-width beats, nothing on
//          full-width traffic: a full-width beat is never "single" here).
//          HOLD_CYCLES = 0 is a pass-through. Only modifiable commands
//          (AxCACHE[1]) pair unless MERGE_NONMOD = 1.
//
// Documentation: granite TASK-005 (vault/tracking/.../granite-ddr2-lpddr2/task).

`timescale 1ns / 1ps
`include "reset_defs.svh"

module mc_axi4_half_agg
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,
    parameter int HOLD_CYCLES    = 4,    // cycles a lone lo waits for its hi; 0 = pass-through
    parameter int AGG_FIFO_DEPTH = 4,    // side queue depth = commands in flight per direction
    parameter bit MERGE_NONMOD   = 1'b0, // 1 = pair non-modifiable (AxCACHE[1] = 0) commands too
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8
)
(
    input  logic            aclk,
    input  logic            aresetn,

    // ---- upstream (host) ----
    input  logic [IW-1:0]   fub_awid,    input  logic [AW-1:0] fub_awaddr,
    input  logic [7:0]      fub_awlen,   input  logic [2:0]    fub_awsize,
    input  logic [1:0]      fub_awburst, input  logic          fub_awlock,
    input  logic [3:0]      fub_awcache, input  logic [2:0]    fub_awprot,
    input  logic [3:0]      fub_awqos,   input  logic [3:0]    fub_awregion,
    input  logic [UW-1:0]   fub_awuser,  input  logic          fub_awvalid,
    output logic            fub_awready,
    input  logic [DW-1:0]   fub_wdata,   input  logic [SW-1:0] fub_wstrb,
    input  logic            fub_wlast,   input  logic [UW-1:0] fub_wuser,
    input  logic            fub_wvalid,  output logic          fub_wready,
    output logic [IW-1:0]   fub_bid,     output logic [1:0]    fub_bresp,
    output logic [UW-1:0]   fub_buser,   output logic          fub_bvalid,
    input  logic            fub_bready,
    input  logic [IW-1:0]   fub_arid,    input  logic [AW-1:0] fub_araddr,
    input  logic [7:0]      fub_arlen,   input  logic [2:0]    fub_arsize,
    input  logic [1:0]      fub_arburst, input  logic          fub_arlock,
    input  logic [3:0]      fub_arcache, input  logic [2:0]    fub_arprot,
    input  logic [3:0]      fub_arqos,   input  logic [3:0]    fub_arregion,
    input  logic [UW-1:0]   fub_aruser,  input  logic          fub_arvalid,
    output logic            fub_arready,
    output logic [IW-1:0]   fub_rid,     output logic [DW-1:0] fub_rdata,
    output logic [1:0]      fub_rresp,   output logic          fub_rlast,
    output logic [UW-1:0]   fub_ruser,   output logic          fub_rvalid,
    input  logic            fub_rready,

    // ---- downstream (the controller's splitters / ring) ----
    output logic [IW-1:0]   m_awid,      output logic [AW-1:0] m_awaddr,
    output logic [7:0]      m_awlen,     output logic [2:0]    m_awsize,
    output logic [1:0]      m_awburst,   output logic          m_awlock,
    output logic [3:0]      m_awcache,   output logic [2:0]    m_awprot,
    output logic [3:0]      m_awqos,     output logic [3:0]    m_awregion,
    output logic [UW-1:0]   m_awuser,    output logic          m_awvalid,
    input  logic            m_awready,
    output logic [DW-1:0]   m_wdata,     output logic [SW-1:0] m_wstrb,
    output logic            m_wlast,     output logic [UW-1:0] m_wuser,
    output logic            m_wvalid,    input  logic          m_wready,
    input  logic [IW-1:0]   m_bid,       input  logic [1:0]    m_bresp,
    input  logic [UW-1:0]   m_buser,     input  logic          m_bvalid,
    output logic            m_bready,
    output logic [IW-1:0]   m_arid,      output logic [AW-1:0] m_araddr,
    output logic [7:0]      m_arlen,     output logic [2:0]    m_arsize,
    output logic [1:0]      m_arburst,   output logic          m_arlock,
    output logic [3:0]      m_arcache,   output logic [2:0]    m_arprot,
    output logic [3:0]      m_arqos,     output logic [3:0]    m_arregion,
    output logic [UW-1:0]   m_aruser,    output logic          m_arvalid,
    input  logic            m_arready,
    input  logic [IW-1:0]   m_rid,       input  logic [DW-1:0] m_rdata,
    input  logic [1:0]      m_rresp,     input  logic          m_rlast,
    input  logic [UW-1:0]   m_ruser,     input  logic          m_rvalid,
    output logic            m_rready
);

    localparam int   QW        = 4 + 3 + 4 + 4 + UW;      // cache, prot, qos, region, user
    localparam int   HALF_DW   = DW / 2;                   // the pairing width
    localparam [2:0] FULL_SIZE = 3'($clog2(SW));

    // ======================================================================
    // AW: pair, then rewrite a pair to one full-width beat
    // ======================================================================
    logic [IW-1:0] w_aw_id;
    logic [AW-1:0] w_aw_addr;
    logic [7:0]    w_aw_len;
    logic [2:0]    w_aw_size;
    logic [1:0]    w_aw_burst;
    logic          w_aw_lock;
    logic [QW-1:0] w_aw_qual;
    logic          w_aw_agg, w_aw_valid, w_aw_ready, w_aw_issue;
    logic          w_winfo_ready, w_binfo_ready;

    axi4_aggregator_cmd #(
        .ID_WIDTH    (IW),
        .ADDR_WIDTH  (AW),
        .DATA_WIDTH  (HALF_DW),
        .QUAL_WIDTH  (QW),
        .HOLD_CYCLES (HOLD_CYCLES)
    ) u_aw_core (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .s_id        (fub_awid),
        .s_addr      (fub_awaddr),
        .s_len       (fub_awlen),
        .s_size      (fub_awsize),
        .s_burst     (fub_awburst),
        .s_lock      (fub_awlock),
        .s_mergeable (fub_awcache[1] || MERGE_NONMOD),
        .s_qual      ({fub_awcache, fub_awprot, fub_awqos, fub_awregion, fub_awuser}),
        .s_valid     (fub_awvalid),
        .s_ready     (fub_awready),
        .m_id        (w_aw_id),
        .m_addr      (w_aw_addr),
        .m_len       (w_aw_len),
        .m_size      (w_aw_size),
        .m_burst     (w_aw_burst),
        .m_lock      (w_aw_lock),
        .m_qual      (w_aw_qual),
        .m_agg       (w_aw_agg),
        .m_valid     (w_aw_valid),
        .m_ready     (w_aw_ready)
    );

    assign m_awid     = w_aw_id;
    assign m_awaddr   = w_aw_addr;                          // lo's address
    assign m_awlen    = w_aw_agg ? 8'd0      : w_aw_len;    // the pair is ONE full beat
    assign m_awsize   = w_aw_agg ? FULL_SIZE : w_aw_size;
    assign m_awburst  = w_aw_burst;
    assign m_awlock   = w_aw_lock;
    assign {m_awcache, m_awprot, m_awqos, m_awregion, m_awuser} = w_aw_qual;
    // an AW issues only when both side queues can record it
    assign m_awvalid  = w_aw_valid && w_winfo_ready && w_binfo_ready;
    assign w_aw_ready = m_awready  && w_winfo_ready && w_binfo_ready;
    assign w_aw_issue = m_awvalid  && m_awready;

    // ======================================================================
    // W: pack the two narrow beats of a pair into one full beat, by strobe
    // ======================================================================
    logic          w_winfo_valid, w_winfo_agg, w_w_pop;
    logic          w_w_agg, w_w_absorb, w_w_hs;
    logic          r_w_held;
    logic [DW-1:0] r_w_data;
    logic [SW-1:0] r_w_strb;
    logic [DW-1:0] w_w_merged;

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_winfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_issue),
        .wr_ready    (w_winfo_ready),
        .wr_data     (w_aw_agg),
        .rd_ready    (w_w_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_winfo_valid),
        .rd_data     (w_winfo_agg)
    );

    assign w_w_agg    = w_winfo_valid && w_winfo_agg;
    assign w_w_absorb = w_w_agg && !r_w_held;             // first beat of a pair: take it, forward nothing

    always_comb begin
        for (int b = 0; b < SW; b++)
            w_w_merged[b*8 +: 8] = r_w_strb[b] ? r_w_data[b*8 +: 8] : fub_wdata[b*8 +: 8];
    end

    assign m_wdata    = w_w_agg ? w_w_merged            : fub_wdata;
    assign m_wstrb    = w_w_agg ? (r_w_strb | fub_wstrb) : fub_wstrb;
    assign m_wlast    = w_w_agg ? 1'b1                  : fub_wlast;
    assign m_wuser    = fub_wuser;
    assign m_wvalid   = fub_wvalid && w_winfo_valid && !w_w_absorb;
    assign fub_wready = w_winfo_valid && (w_w_absorb ? 1'b1 : m_wready);
    assign w_w_hs     = fub_wvalid && fub_wready;
    // pop at the end of the upstream burst: the pair's second beat, or WLAST
    assign w_w_pop    = w_w_hs && (w_w_agg ? r_w_held : fub_wlast);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_w_held <= 1'b0;
            r_w_data <= '0;
            r_w_strb <= '0;
        end else if (w_w_hs && w_w_absorb) begin
            r_w_held <= 1'b1;
            r_w_data <= fub_wdata;
            r_w_strb <= fub_wstrb;
        end else if (w_w_pop) begin
            r_w_held <= 1'b0;
        end
    )

    // ======================================================================
    // B: a pair's one B is presented upstream twice
    // ======================================================================
    logic w_binfo_valid, w_binfo_agg, w_b_pop, w_b_hs;
    logic r_b_rep;    // the first presentation of a pair's B has been accepted

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_binfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_issue),
        .wr_ready    (w_binfo_ready),
        .wr_data     (w_aw_agg),
        .rd_ready    (w_b_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_binfo_valid),
        .rd_data     (w_binfo_agg)
    );

    assign fub_bid    = m_bid;
    assign fub_bresp  = m_bresp;
    assign fub_buser  = m_buser;
    assign fub_bvalid = m_bvalid && w_binfo_valid;
    assign w_b_hs     = fub_bvalid && fub_bready;
    assign m_bready   = fub_bready && w_binfo_valid && (w_binfo_agg ? r_b_rep : 1'b1);
    assign w_b_pop    = w_b_hs && (w_binfo_agg ? r_b_rep : 1'b1);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_rep <= 1'b0;
        end else if (w_b_hs && w_binfo_agg) begin
            r_b_rep <= ~r_b_rep;
        end
    )

    // ======================================================================
    // AR: pair, then rewrite a pair to one full-width beat
    // ======================================================================
    logic [IW-1:0] w_ar_id;
    logic [AW-1:0] w_ar_addr;
    logic [7:0]    w_ar_len;
    logic [2:0]    w_ar_size;
    logic [1:0]    w_ar_burst;
    logic          w_ar_lock;
    logic [QW-1:0] w_ar_qual;
    logic          w_ar_agg, w_ar_valid, w_ar_ready, w_ar_issue;
    logic          w_rinfo_ready;

    axi4_aggregator_cmd #(
        .ID_WIDTH    (IW),
        .ADDR_WIDTH  (AW),
        .DATA_WIDTH  (HALF_DW),
        .QUAL_WIDTH  (QW),
        .HOLD_CYCLES (HOLD_CYCLES)
    ) u_ar_core (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .s_id        (fub_arid),
        .s_addr      (fub_araddr),
        .s_len       (fub_arlen),
        .s_size      (fub_arsize),
        .s_burst     (fub_arburst),
        .s_lock      (fub_arlock),
        .s_mergeable (fub_arcache[1] || MERGE_NONMOD),
        .s_qual      ({fub_arcache, fub_arprot, fub_arqos, fub_arregion, fub_aruser}),
        .s_valid     (fub_arvalid),
        .s_ready     (fub_arready),
        .m_id        (w_ar_id),
        .m_addr      (w_ar_addr),
        .m_len       (w_ar_len),
        .m_size      (w_ar_size),
        .m_burst     (w_ar_burst),
        .m_lock      (w_ar_lock),
        .m_qual      (w_ar_qual),
        .m_agg       (w_ar_agg),
        .m_valid     (w_ar_valid),
        .m_ready     (w_ar_ready)
    );

    assign m_arid     = w_ar_id;
    assign m_araddr   = w_ar_addr;
    assign m_arlen    = w_ar_agg ? 8'd0      : w_ar_len;
    assign m_arsize   = w_ar_agg ? FULL_SIZE : w_ar_size;
    assign m_arburst  = w_ar_burst;
    assign m_arlock   = w_ar_lock;
    assign {m_arcache, m_arprot, m_arqos, m_arregion, m_aruser} = w_ar_qual;
    assign m_arvalid  = w_ar_valid && w_rinfo_ready;
    assign w_ar_ready = m_arready  && w_rinfo_ready;
    assign w_ar_issue = m_arvalid  && m_arready;

    // ======================================================================
    // R: a pair's one beat is presented upstream twice, RLAST on both
    // ======================================================================
    logic w_rinfo_valid, w_rinfo_agg, w_r_pop, w_r_hs;
    logic r_r_rep;    // the first presentation of a pair's beat has been accepted

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_rinfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_issue),
        .wr_ready    (w_rinfo_ready),
        .wr_data     (w_ar_agg),
        .rd_ready    (w_r_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_rinfo_valid),
        .rd_data     (w_rinfo_agg)
    );

    assign fub_rid    = m_rid;
    assign fub_rdata  = m_rdata;
    assign fub_rresp  = m_rresp;
    assign fub_ruser  = m_ruser;
    assign fub_rlast  = w_rinfo_agg ? 1'b1 : m_rlast;     // each half is its own burst upstream
    assign fub_rvalid = m_rvalid && w_rinfo_valid;
    assign w_r_hs     = fub_rvalid && fub_rready;
    assign m_rready   = fub_rready && w_rinfo_valid && (w_rinfo_agg ? r_r_rep : 1'b1);
    assign w_r_pop    = w_r_hs && (w_rinfo_agg ? r_r_rep : m_rlast);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_r_rep <= 1'b0;
        end else if (w_r_hs && w_rinfo_agg) begin
            r_r_rep <= ~r_r_rep;
        end
    )

endmodule : mc_axi4_half_agg
