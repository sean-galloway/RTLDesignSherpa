// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_intake
// Purpose: AXI4 host-protocol intake. Accepts AW/W/AR from the host via the
//          AMBA axi4_slave_wr / axi4_slave_rd skid-buffered protocol modules,
//          stages write data into a flat w_buf RAM, AND-reduces wstrb across
//          the burst to compute a full_strb hint, and emits decoded burst
//          metadata downstream to addr_mapper / wr_cmd_cam / rd_cmd_cam.
//
// Description:
//   This is the "host face" of the AXI frontend macro. It replaces what the
//   testbench previously drove directly into the macro (decoded aw_addr/id/
//   len + pre-allocated w_buf_ptr).
//
//   Protocol layer is delegated to the AMBA modules — they handle valid/
//   ready handshakes, AW/W/B/AR/R channel decoupling, and per-channel skid
//   buffering. This FUB sees post-skid fub_axi_* signals and contributes:
//
//     - aw_pending FIFO (gaxi_fifo_sync) — buffers AW metadata until the
//       matching W burst has been received in full.
//     - w_buf + wstrb_buf — flat distributed RAM that holds in-flight W
//       beats and per-byte strobes, indexed by a monotonic write pointer.
//     - per-burst wstrb AND-reduce — accumulates &(wstrb) across beats to
//       compute the full_strb hint consumed by wr2rd_forward.
//     - ar_pending FIFO (gaxi_fifo_sync) — pass-through head buffer for
//       AR metadata before downstream push.
//     - b_fifo (gaxi_fifo_sync) — pushed on wr_entry_complete_strb_i,
//       drained on B handshake.
//     - R-channel mux — forwarded reads (from wr2rd_forward) pull data
//       out of w_buf; non-forwarded reads come from the rd_inject_*
//       interface that rd_data_path will eventually drive.
//
//   Per the macro test plan, only the wr/rd command CAMs are instantiated
//   as separate modules — there are no new CAMs inside this FUB. The
//   AXI-side metadata pass-through (awcache/awprot/awqos/awregion etc.)
//   is currently dropped; if a future revision needs it, it becomes a
//   separate axi_id_side_table_fub keyed by AXI ID.
//
// References:
//   rtl/amba/axi4/axi4_slave_wr.sv
//   rtl/amba/axi4/axi4_slave_rd.sv
//   rtl/amba/gaxi/gaxi_fifo_sync.sv
//   projects/components/stream/rtl/fub/axi_write_engine.sv
//   docs/ddr2_lpddr2_mas/ch02_blocks/02_axi4_slave.md
//
// Author: sean galloway
// Created: 2026-06-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_intake
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_ID_WIDTH      = 4,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_STRB_WIDTH    = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH   = 8,

    // AMBA axi4_slave_wr / axi4_slave_rd skid depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Internal FIFO depths
    parameter int AW_PENDING_DEPTH  = 4,
    parameter int AR_PENDING_DEPTH  = 4,
    parameter int B_FIFO_DEPTH      = 4,

    // w_buf storage — power-of-two for clean modulo wrap
    parameter int W_BUF_DEPTH       = 128,
    parameter int W_BUF_PTR_WIDTH   = $clog2(W_BUF_DEPTH),

    // Aliases (long names for external configuration)
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int SW  = AXI_STRB_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    //=========================================================================
    // AXI4 slave-side host ports
    //=========================================================================
    // AW
    input  logic [IW-1:0]        s_axi_awid,
    input  logic [AW-1:0]        s_axi_awaddr,
    input  logic [7:0]           s_axi_awlen,
    input  logic [2:0]           s_axi_awsize,
    input  logic [1:0]           s_axi_awburst,
    input  logic                 s_axi_awlock,
    input  logic [3:0]           s_axi_awcache,
    input  logic [2:0]           s_axi_awprot,
    input  logic [3:0]           s_axi_awqos,
    input  logic [3:0]           s_axi_awregion,
    input  logic [UW-1:0]        s_axi_awuser,
    input  logic                 s_axi_awvalid,
    output logic                 s_axi_awready,
    // W
    input  logic [DW-1:0]        s_axi_wdata,
    input  logic [SW-1:0]        s_axi_wstrb,
    input  logic                 s_axi_wlast,
    input  logic [UW-1:0]        s_axi_wuser,
    input  logic                 s_axi_wvalid,
    output logic                 s_axi_wready,
    // B
    output logic [IW-1:0]        s_axi_bid,
    output logic [1:0]           s_axi_bresp,
    output logic [UW-1:0]        s_axi_buser,
    output logic                 s_axi_bvalid,
    input  logic                 s_axi_bready,
    // AR
    input  logic [IW-1:0]        s_axi_arid,
    input  logic [AW-1:0]        s_axi_araddr,
    input  logic [7:0]           s_axi_arlen,
    input  logic [2:0]           s_axi_arsize,
    input  logic [1:0]           s_axi_arburst,
    input  logic                 s_axi_arlock,
    input  logic [3:0]           s_axi_arcache,
    input  logic [2:0]           s_axi_arprot,
    input  logic [3:0]           s_axi_arqos,
    input  logic [3:0]           s_axi_arregion,
    input  logic [UW-1:0]        s_axi_aruser,
    input  logic                 s_axi_arvalid,
    output logic                 s_axi_arready,
    // R
    output logic [IW-1:0]        s_axi_rid,
    output logic [DW-1:0]        s_axi_rdata,
    output logic [1:0]           s_axi_rresp,
    output logic                 s_axi_rlast,
    output logic [UW-1:0]        s_axi_ruser,
    output logic                 s_axi_rvalid,
    input  logic                 s_axi_rready,

    //=========================================================================
    // Downstream AW push (to addr_mapper → wr_cmd_cam)
    //=========================================================================
    output logic                 aw_push_valid_o,
    input  logic                 aw_push_ready_i,
    output logic [AW-1:0]        aw_push_addr_o,
    output logic [IW-1:0]        aw_push_id_o,
    output logic [BLW-1:0]       aw_push_len_o,      // beats (NOT len-1)
    output logic [WPW-1:0]       aw_push_w_buf_ptr_o,
    output logic [WPW-1:0]       aw_push_strb_ptr_o,
    output logic                 aw_push_full_strb_o,
    output logic [3:0]           aw_push_qos_o,

    //=========================================================================
    // Downstream AR push (to addr_mapper → wr2rd_forward / rd_cmd_cam)
    //=========================================================================
    output logic                 ar_push_valid_o,
    input  logic                 ar_push_ready_i,
    output logic [AW-1:0]        ar_push_addr_o,
    output logic [IW-1:0]        ar_push_id_o,
    output logic [BLW-1:0]       ar_push_len_o,
    output logic [3:0]           ar_push_qos_o,

    //=========================================================================
    // Write completion (from wr_cmd_cam entry_complete) → B-channel push
    //=========================================================================
    input  logic                 wr_entry_complete_strb_i,
    input  logic [IW-1:0]        wr_entry_complete_id_i,

    //=========================================================================
    // Read completion (from rd_cmd_cam) — reserved for v2
    //=========================================================================
    input  logic                 rd_entry_complete_strb_i,
    input  logic [IW-1:0]        rd_entry_complete_id_i,

    //=========================================================================
    // Forwarded-read data path (from wr2rd_forward) — R beats sourced
    // from w_buf at fwd_w_buf_ptr_i + counter.
    //=========================================================================
    input  logic                 fwd_valid_i,
    output logic                 fwd_ready_o,
    input  logic [IW-1:0]        fwd_id_i,
    input  logic [WPW-1:0]       fwd_w_buf_ptr_i,
    input  logic [BLW-1:0]       fwd_len_i,

    //=========================================================================
    // Non-forwarded R-data injection (rd_data_path stub / TB)
    //=========================================================================
    input  logic                 rd_inject_valid_i,
    output logic                 rd_inject_ready_o,
    input  logic [IW-1:0]        rd_inject_id_i,
    input  logic [DW-1:0]        rd_inject_data_i,
    input  logic                 rd_inject_last_i,

    //=========================================================================
    // External w_buf read port (wr_data_path stub / TB)
    //=========================================================================
    input  logic [WPW-1:0]       wbuf_ext_rd_ptr_i,
    output logic [DW-1:0]        wbuf_ext_rd_data_o,
    output logic [SW-1:0]        wbuf_ext_rd_strb_o,

    //=========================================================================
    // Status
    //=========================================================================
    output logic                 busy_o,

    // ----- observability -----
    output logic [15:0]          obs_wr_completions_o,
    output logic [15:0]          obs_rd_completions_o,
    output logic [15:0]          obs_aw_meta_writes_o,
    output logic [15:0]          obs_ar_meta_writes_o
);

    //=========================================================================
    // F4 side-table lookup outputs — declared up-front so the
    // aw_push_qos_o / ar_push_qos_o assigns + B/R user-echo paths can
    // reference them. Driven by u_id_side_table further down.
    logic [3:0]    w_aw_push_qos;
    logic [UW-1:0] w_aw_compl_user;
    logic [3:0]    w_ar_push_qos;
    logic [UW-1:0] w_ar_compl_user;

    // Internal fub_axi_* — post-skid signals from the AMBA wrappers
    //=========================================================================
    // From axi4_slave_wr (AW side, W side)
    logic [IW-1:0]        fub_axi_awid;
    logic [AW-1:0]        fub_axi_awaddr;
    logic [7:0]           fub_axi_awlen;
    logic [2:0]           fub_axi_awsize;
    logic [1:0]           fub_axi_awburst;
    logic                 fub_axi_awlock;
    logic [3:0]           fub_axi_awcache;
    logic [2:0]           fub_axi_awprot;
    logic [3:0]           fub_axi_awqos;
    logic [3:0]           fub_axi_awregion;
    logic [UW-1:0]        fub_axi_awuser;
    logic                 fub_axi_awvalid;
    logic                 fub_axi_awready;

    logic [DW-1:0]        fub_axi_wdata;
    logic [SW-1:0]        fub_axi_wstrb;
    logic                 fub_axi_wlast;
    logic [UW-1:0]        fub_axi_wuser;
    logic                 fub_axi_wvalid;
    logic                 fub_axi_wready;

    // To axi4_slave_wr (B side — this FUB produces B responses)
    logic [IW-1:0]        fub_axi_bid;
    logic [1:0]           fub_axi_bresp;
    logic [UW-1:0]        fub_axi_buser;
    logic                 fub_axi_bvalid;
    logic                 fub_axi_bready;

    // From axi4_slave_rd (AR side)
    logic [IW-1:0]        fub_axi_arid;
    logic [AW-1:0]        fub_axi_araddr;
    logic [7:0]           fub_axi_arlen;
    logic [2:0]           fub_axi_arsize;
    logic [1:0]           fub_axi_arburst;
    logic                 fub_axi_arlock;
    logic [3:0]           fub_axi_arcache;
    logic [2:0]           fub_axi_arprot;
    logic [3:0]           fub_axi_arqos;
    logic [3:0]           fub_axi_arregion;
    logic [UW-1:0]        fub_axi_aruser;
    logic                 fub_axi_arvalid;
    logic                 fub_axi_arready;

    // To axi4_slave_rd (R side — this FUB produces R data)
    logic [IW-1:0]        fub_axi_rid;
    logic [DW-1:0]        fub_axi_rdata;
    logic [1:0]           fub_axi_rresp;
    logic                 fub_axi_rlast;
    logic [UW-1:0]        fub_axi_ruser;
    logic                 fub_axi_rvalid;
    logic                 fub_axi_rready;

    // Status from the AMBA wrappers
    logic                 wr_busy;
    logic                 rd_busy;

    //=========================================================================
    // axi4_slave_wr — AW/W/B protocol layer
    //=========================================================================
    axi4_slave_wr #(
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B),
        .AXI_ID_WIDTH    (IW),
        .AXI_ADDR_WIDTH  (AW),
        .AXI_DATA_WIDTH  (DW),
        .AXI_USER_WIDTH  (UW)
    ) i_axi4_slave_wr (
        .aclk            (aclk),
        .aresetn         (aresetn),
        // Host AW
        .s_axi_awid      (s_axi_awid),
        .s_axi_awaddr    (s_axi_awaddr),
        .s_axi_awlen     (s_axi_awlen),
        .s_axi_awsize    (s_axi_awsize),
        .s_axi_awburst   (s_axi_awburst),
        .s_axi_awlock    (s_axi_awlock),
        .s_axi_awcache   (s_axi_awcache),
        .s_axi_awprot    (s_axi_awprot),
        .s_axi_awqos     (s_axi_awqos),
        .s_axi_awregion  (s_axi_awregion),
        .s_axi_awuser    (s_axi_awuser),
        .s_axi_awvalid   (s_axi_awvalid),
        .s_axi_awready   (s_axi_awready),
        // Host W
        .s_axi_wdata     (s_axi_wdata),
        .s_axi_wstrb     (s_axi_wstrb),
        .s_axi_wlast     (s_axi_wlast),
        .s_axi_wuser     (s_axi_wuser),
        .s_axi_wvalid    (s_axi_wvalid),
        .s_axi_wready    (s_axi_wready),
        // Host B
        .s_axi_bid       (s_axi_bid),
        .s_axi_bresp     (s_axi_bresp),
        .s_axi_buser     (s_axi_buser),
        .s_axi_bvalid    (s_axi_bvalid),
        .s_axi_bready    (s_axi_bready),
        // Post-skid AW → this FUB
        .fub_axi_awid    (fub_axi_awid),
        .fub_axi_awaddr  (fub_axi_awaddr),
        .fub_axi_awlen   (fub_axi_awlen),
        .fub_axi_awsize  (fub_axi_awsize),
        .fub_axi_awburst (fub_axi_awburst),
        .fub_axi_awlock  (fub_axi_awlock),
        .fub_axi_awcache (fub_axi_awcache),
        .fub_axi_awprot  (fub_axi_awprot),
        .fub_axi_awqos   (fub_axi_awqos),
        .fub_axi_awregion(fub_axi_awregion),
        .fub_axi_awuser  (fub_axi_awuser),
        .fub_axi_awvalid (fub_axi_awvalid),
        .fub_axi_awready (fub_axi_awready),
        // Post-skid W → this FUB
        .fub_axi_wdata   (fub_axi_wdata),
        .fub_axi_wstrb   (fub_axi_wstrb),
        .fub_axi_wlast   (fub_axi_wlast),
        .fub_axi_wuser   (fub_axi_wuser),
        .fub_axi_wvalid  (fub_axi_wvalid),
        .fub_axi_wready  (fub_axi_wready),
        // B response from this FUB
        .fub_axi_bid     (fub_axi_bid),
        .fub_axi_bresp   (fub_axi_bresp),
        .fub_axi_buser   (fub_axi_buser),
        .fub_axi_bvalid  (fub_axi_bvalid),
        .fub_axi_bready  (fub_axi_bready),
        .busy            (wr_busy)
    );

    //=========================================================================
    // axi4_slave_rd — AR/R protocol layer
    //=========================================================================
    axi4_slave_rd #(
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R),
        .AXI_ID_WIDTH    (IW),
        .AXI_ADDR_WIDTH  (AW),
        .AXI_DATA_WIDTH  (DW),
        .AXI_USER_WIDTH  (UW)
    ) i_axi4_slave_rd (
        .aclk            (aclk),
        .aresetn         (aresetn),
        // Host AR
        .s_axi_arid      (s_axi_arid),
        .s_axi_araddr    (s_axi_araddr),
        .s_axi_arlen     (s_axi_arlen),
        .s_axi_arsize    (s_axi_arsize),
        .s_axi_arburst   (s_axi_arburst),
        .s_axi_arlock    (s_axi_arlock),
        .s_axi_arcache   (s_axi_arcache),
        .s_axi_arprot    (s_axi_arprot),
        .s_axi_arqos     (s_axi_arqos),
        .s_axi_arregion  (s_axi_arregion),
        .s_axi_aruser    (s_axi_aruser),
        .s_axi_arvalid   (s_axi_arvalid),
        .s_axi_arready   (s_axi_arready),
        // Host R
        .s_axi_rid       (s_axi_rid),
        .s_axi_rdata     (s_axi_rdata),
        .s_axi_rresp     (s_axi_rresp),
        .s_axi_rlast     (s_axi_rlast),
        .s_axi_ruser     (s_axi_ruser),
        .s_axi_rvalid    (s_axi_rvalid),
        .s_axi_rready    (s_axi_rready),
        // Post-skid AR → this FUB
        .fub_axi_arid    (fub_axi_arid),
        .fub_axi_araddr  (fub_axi_araddr),
        .fub_axi_arlen   (fub_axi_arlen),
        .fub_axi_arsize  (fub_axi_arsize),
        .fub_axi_arburst (fub_axi_arburst),
        .fub_axi_arlock  (fub_axi_arlock),
        .fub_axi_arcache (fub_axi_arcache),
        .fub_axi_arprot  (fub_axi_arprot),
        .fub_axi_arqos   (fub_axi_arqos),
        .fub_axi_arregion(fub_axi_arregion),
        .fub_axi_aruser  (fub_axi_aruser),
        .fub_axi_arvalid (fub_axi_arvalid),
        .fub_axi_arready (fub_axi_arready),
        // R data driven by this FUB
        .fub_axi_rid     (fub_axi_rid),
        .fub_axi_rdata   (fub_axi_rdata),
        .fub_axi_rresp   (fub_axi_rresp),
        .fub_axi_rlast   (fub_axi_rlast),
        .fub_axi_ruser   (fub_axi_ruser),
        .fub_axi_rvalid  (fub_axi_rvalid),
        .fub_axi_rready  (fub_axi_rready),
        .busy            (rd_busy)
    );

    //=========================================================================
    // aw_pending FIFO
    //
    // Holds AWs that have been accepted from the host but whose W burst
    // hasn't been pushed downstream yet. The head is the "current" burst
    // being W-streamed. Pop on aw_push handshake.
    //=========================================================================
    typedef struct packed {
        logic [IW-1:0]   id;
        logic [AW-1:0]   addr;
        logic [BLW-1:0]  len;          // beats — already len-1 + 1
        logic [WPW-1:0]  w_buf_ptr;
        logic [WPW-1:0]  strb_ptr;
    } aw_pending_t;

    aw_pending_t        w_aw_pend_din;
    aw_pending_t        w_aw_pend_dout;
    logic               w_aw_pend_wr_valid;
    logic               w_aw_pend_wr_ready;
    logic               w_aw_pend_rd_valid;
    logic               w_aw_pend_rd_ready;

    // Monotonic w_buf write pointer — advances on each W beat accepted.
    logic [WPW-1:0]     r_wbuf_wptr;

    assign w_aw_pend_din.id        = fub_axi_awid;
    assign w_aw_pend_din.addr      = fub_axi_awaddr;
    assign w_aw_pend_din.len       = BLW'(fub_axi_awlen) + BLW'(1);
    assign w_aw_pend_din.w_buf_ptr = r_wbuf_wptr;
    assign w_aw_pend_din.strb_ptr  = r_wbuf_wptr;

    assign w_aw_pend_wr_valid = fub_axi_awvalid;
    assign fub_axi_awready    = w_aw_pend_wr_ready;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(aw_pending_t)),
        .DEPTH      (AW_PENDING_DEPTH)
    ) i_aw_pending_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_pend_wr_valid),
        .wr_ready    (w_aw_pend_wr_ready),
        .wr_data     (w_aw_pend_din),
        .rd_valid    (w_aw_pend_rd_valid),
        .rd_ready    (w_aw_pend_rd_ready),
        .rd_data     (w_aw_pend_dout),
        .count       ()
    );

    //=========================================================================
    // W intake — write to w_buf, AND-reduce wstrb, detect wlast
    //=========================================================================
    // w_buf storage (distributed RAM)
    logic [DW-1:0] r_w_buf      [W_BUF_DEPTH];
    logic [SW-1:0] r_wstrb_buf  [W_BUF_DEPTH];

    // Per-burst AND-reduce accumulator
    logic           r_full_strb_acc;
    logic           r_burst_done;       // wlast received; aw_pending head ready to push
    logic           r_final_full_strb;  // captured at wlast

    // Accept W beats only when (a) the AMBA wrapper has data, (b) aw_pending
    // has a head AW for it to belong to, and (c) we don't already have a
    // burst-complete waiting for downstream push. Holding wready low while
    // r_burst_done prevents the next burst's W beats from leaking in before
    // the current head is committed downstream.
    assign fub_axi_wready = w_aw_pend_rd_valid && !r_burst_done;

    wire w_w_beat_handshake = fub_axi_wvalid && fub_axi_wready;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wbuf_wptr       <= '0;
            r_full_strb_acc   <= 1'b1;
            r_burst_done      <= 1'b0;
            r_final_full_strb <= 1'b1;
        end else begin
            if (w_w_beat_handshake) begin
                r_w_buf    [r_wbuf_wptr] <= fub_axi_wdata;
                r_wstrb_buf[r_wbuf_wptr] <= fub_axi_wstrb;
                r_wbuf_wptr              <= r_wbuf_wptr + 1'b1;
                r_full_strb_acc          <= r_full_strb_acc & (&fub_axi_wstrb);
                if (fub_axi_wlast) begin
                    r_burst_done      <= 1'b1;
                    r_final_full_strb <= r_full_strb_acc & (&fub_axi_wstrb);
                end
            end
            // On downstream aw_push accept: clear pending flag, reset
            // accumulator for the next burst, pop the aw_pending head.
            if (aw_push_valid_o && aw_push_ready_i) begin
                r_burst_done    <= 1'b0;
                r_full_strb_acc <= 1'b1;
            end
        end
    end)

    // Downstream AW push — gated on burst-complete + aw_pending head valid
    assign aw_push_valid_o     = r_burst_done && w_aw_pend_rd_valid;
    assign aw_push_addr_o      = w_aw_pend_dout.addr;
    assign aw_push_id_o        = w_aw_pend_dout.id;
    assign aw_push_len_o       = w_aw_pend_dout.len;
    assign aw_push_w_buf_ptr_o = w_aw_pend_dout.w_buf_ptr;
    assign aw_push_strb_ptr_o  = w_aw_pend_dout.strb_ptr;
    assign aw_push_full_strb_o = r_final_full_strb;
    assign aw_push_qos_o       = w_aw_push_qos;

    // Pop aw_pending head on push handshake
    assign w_aw_pend_rd_ready  = aw_push_valid_o && aw_push_ready_i;

    //=========================================================================
    // ar_pending FIFO — head buffer for AR metadata
    //=========================================================================
    typedef struct packed {
        logic [IW-1:0]   id;
        logic [AW-1:0]   addr;
        logic [BLW-1:0]  len;
    } ar_pending_t;

    ar_pending_t   w_ar_pend_din;
    ar_pending_t   w_ar_pend_dout;
    logic          w_ar_pend_wr_valid;
    logic          w_ar_pend_wr_ready;
    logic          w_ar_pend_rd_valid;
    logic          w_ar_pend_rd_ready;

    assign w_ar_pend_din.id   = fub_axi_arid;
    assign w_ar_pend_din.addr = fub_axi_araddr;
    assign w_ar_pend_din.len  = BLW'(fub_axi_arlen) + BLW'(1);

    assign w_ar_pend_wr_valid = fub_axi_arvalid;
    assign fub_axi_arready    = w_ar_pend_wr_ready;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(ar_pending_t)),
        .DEPTH      (AR_PENDING_DEPTH)
    ) i_ar_pending_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_pend_wr_valid),
        .wr_ready    (w_ar_pend_wr_ready),
        .wr_data     (w_ar_pend_din),
        .rd_valid    (w_ar_pend_rd_valid),
        .rd_ready    (w_ar_pend_rd_ready),
        .rd_data     (w_ar_pend_dout),
        .count       ()
    );

    assign ar_push_valid_o = w_ar_pend_rd_valid;
    assign ar_push_addr_o  = w_ar_pend_dout.addr;
    assign ar_push_id_o    = w_ar_pend_dout.id;
    assign ar_push_len_o   = w_ar_pend_dout.len;
    assign ar_push_qos_o   = w_ar_push_qos;
    assign w_ar_pend_rd_ready = ar_push_valid_o && ar_push_ready_i;

    //=========================================================================
    // F2/F4: AXI metadata side-table — extracted into axi_id_side_table.
    // Two read ports per side:
    //   *_push_* — feeds aw_push_qos_o / ar_push_qos_o downstream so
    //              the CAMs + scheduler can do QoS-aware arbitration.
    //   *_compl_* — feeds the B FIFO push (BUSER) and R emit (RUSER).
    // The four lookup wires are declared near the top of the module so
    // earlier aw_push_qos_o / ar_push_qos_o / BUSER / RUSER assigns can
    // reference them.
    //=========================================================================
    // ar_compl_id selects the R-emit ID for the user echo. Driven in the
    // R emit block below (where r_r_fwd_active / r_r_fwd_id are declared).
    logic [IW-1:0] w_ar_compl_id;

    axi_id_side_table #(
        .AXI_ID_WIDTH   (IW),
        .AXI_USER_WIDTH (UW)
    ) u_id_side_table (
        .aclk             (aclk),
        .aresetn          (aresetn),
        // AW writes
        .aw_we_i          (fub_axi_awvalid && fub_axi_awready),
        .aw_id_i          (fub_axi_awid),
        .aw_user_i        (fub_axi_awuser),
        .aw_cache_i       (fub_axi_awcache),
        .aw_prot_i        (fub_axi_awprot),
        .aw_qos_i         (fub_axi_awqos),
        .aw_region_i      (fub_axi_awregion),
        .aw_size_i        (fub_axi_awsize),
        .aw_burst_i       (fub_axi_awburst),
        // AR writes
        .ar_we_i          (fub_axi_arvalid && fub_axi_arready),
        .ar_id_i          (fub_axi_arid),
        .ar_user_i        (fub_axi_aruser),
        .ar_cache_i       (fub_axi_arcache),
        .ar_prot_i        (fub_axi_arprot),
        .ar_qos_i         (fub_axi_arqos),
        .ar_region_i      (fub_axi_arregion),
        .ar_size_i        (fub_axi_arsize),
        .ar_burst_i       (fub_axi_arburst),
        // AW push-side (qos forward)
        .aw_push_id_i     (w_aw_pend_dout.id),
        .aw_push_qos_o    (w_aw_push_qos),
        // AW completion-side (user echo)
        .aw_compl_id_i    (wr_entry_complete_id_i),
        .aw_compl_user_o  (w_aw_compl_user),
        // AR push-side
        .ar_push_id_i     (w_ar_pend_dout.id),
        .ar_push_qos_o    (w_ar_push_qos),
        // AR completion-side
        .ar_compl_id_i    (w_ar_compl_id),
        .ar_compl_user_o  (w_ar_compl_user),
        .obs_aw_writes_o  (obs_aw_meta_writes_o),
        .obs_ar_writes_o  (obs_ar_meta_writes_o)
    );

    //=========================================================================
    // B response FIFO — pushed on wr_entry_complete_strb, drained on B
    // handshake. We drive fub_axi_b* into axi4_slave_wr's skid buffer; it
    // emits s_axi_b* to the host.
    //=========================================================================
    typedef struct packed {
        logic [IW-1:0]  id;
        logic [1:0]     resp;
        logic [UW-1:0]  user;
    } b_entry_t;

    b_entry_t       w_b_din;
    b_entry_t       w_b_dout;
    logic           w_b_wr_valid;
    logic           w_b_wr_ready;
    logic           w_b_rd_valid;
    logic           w_b_rd_ready;

    assign w_b_din.id   = wr_entry_complete_id_i;
    assign w_b_din.resp = 2'b00;            // RESP_OKAY
    // BUSER mirrors AWUSER from the id-side-table completion port.
    assign w_b_din.user = w_aw_compl_user;
    assign w_b_wr_valid = wr_entry_complete_strb_i;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(b_entry_t)),
        .DEPTH      (B_FIFO_DEPTH)
    ) i_b_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_b_wr_valid),
        .wr_ready    (w_b_wr_ready),
        .wr_data     (w_b_din),
        .rd_valid    (w_b_rd_valid),
        .rd_ready    (w_b_rd_ready),
        .rd_data     (w_b_dout),
        .count       ()
    );

    assign fub_axi_bvalid = w_b_rd_valid;
    assign fub_axi_bid    = w_b_dout.id;
    assign fub_axi_bresp  = w_b_dout.resp;
    assign fub_axi_buser  = w_b_dout.user;
    assign w_b_rd_ready   = fub_axi_bvalid && fub_axi_bready;

    //=========================================================================
    // R emit — mux between forwarded (from w_buf via wr2rd_forward) and
    // injected (from rd_data_path / TB) sources.
    //
    // Forwarded burst captured at fwd handshake. While r_r_fwd_active,
    // R emits len beats reading r_w_buf[r_r_fwd_ptr] each beat; on last
    // beat (when fub_axi_rready accepts), r_r_fwd_active clears.
    //
    // Injected path is straight pass-through to fub_axi_r* while not
    // forwarded.
    //=========================================================================
    logic           r_r_fwd_active;
    logic [IW-1:0]  r_r_fwd_id;
    logic [WPW-1:0] r_r_fwd_ptr;
    logic [BLW-1:0] r_r_fwd_remaining;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_r_fwd_active    <= 1'b0;
            r_r_fwd_id        <= '0;
            r_r_fwd_ptr       <= '0;
            r_r_fwd_remaining <= '0;
        end else begin
            if (fwd_valid_i && fwd_ready_o) begin
                r_r_fwd_active    <= 1'b1;
                r_r_fwd_id        <= fwd_id_i;
                r_r_fwd_ptr       <= fwd_w_buf_ptr_i;
                r_r_fwd_remaining <= fwd_len_i;
            end else if (r_r_fwd_active && fub_axi_rvalid && fub_axi_rready) begin
                r_r_fwd_ptr       <= r_r_fwd_ptr + 1'b1;
                r_r_fwd_remaining <= r_r_fwd_remaining - 1'b1;
                if (r_r_fwd_remaining == BLW'(1)) begin
                    r_r_fwd_active <= 1'b0;
                end
            end
        end
    end)

    // fwd_ready_o — accept a new forwarded burst only when not currently
    // emitting one.
    assign fwd_ready_o = !r_r_fwd_active;

    // rd_inject_ready — accept injected beats only when forwarded burst
    // is idle AND the R skid buffer can accept.
    assign rd_inject_ready_o = !r_r_fwd_active && fub_axi_rready;

    // Side-table AR completion lookup ID: forwarded path uses r_r_fwd_id;
    // injected path uses the live rd_inject_id.
    assign w_ar_compl_id = r_r_fwd_active ? r_r_fwd_id : rd_inject_id_i;

    always_comb begin
        fub_axi_rvalid = 1'b0;
        fub_axi_rid    = '0;
        fub_axi_rdata  = '0;
        fub_axi_rresp  = 2'b00;
        fub_axi_rlast  = 1'b0;
        fub_axi_ruser  = '0;
        if (r_r_fwd_active) begin
            fub_axi_rvalid = 1'b1;
            fub_axi_rid    = r_r_fwd_id;
            fub_axi_rdata  = r_w_buf[r_r_fwd_ptr];
            fub_axi_rresp  = 2'b00;
            fub_axi_rlast  = (r_r_fwd_remaining == BLW'(1));
            // RUSER mirrors ARUSER from the id-side-table completion port.
            // (w_ar_compl_id selects r_r_fwd_id when r_r_fwd_active.)
            fub_axi_ruser  = w_ar_compl_user;
        end else if (rd_inject_valid_i) begin
            fub_axi_rvalid = rd_inject_valid_i;
            fub_axi_rid    = rd_inject_id_i;
            fub_axi_rdata  = rd_inject_data_i;
            fub_axi_rresp  = 2'b00;
            fub_axi_rlast  = rd_inject_last_i;
            fub_axi_ruser  = w_ar_compl_user;
        end
    end

    //=========================================================================
    // External w_buf read port — combinational read at the requested
    // pointer. Consumed by wr_data_path (or the TB stub).
    //=========================================================================
    assign wbuf_ext_rd_data_o = r_w_buf    [wbuf_ext_rd_ptr_i];
    assign wbuf_ext_rd_strb_o = r_wstrb_buf[wbuf_ext_rd_ptr_i];

    //=========================================================================
    // Status / telemetry
    //=========================================================================
    assign busy_o = wr_busy || rd_busy || r_r_fwd_active || r_burst_done;

    //=========================================================================
    // Unused signals — present in AXI4 ports for full-compliance interface
    // but not yet consumed in v1 (lock/cache/prot/qos/region/size/burst).
    //=========================================================================
    // F2 captures awsize/awburst/awcache/awprot/awqos/awregion/awuser and the
    // AR equivalents into the side-table. Only lock + wuser remain truly
    // dropped (LOCK is exclusive-access — not supported in v1; WUSER has no
    // standard echo path).
    wire unused_axi = |{ fub_axi_awlock,
                         fub_axi_wuser,
                         fub_axi_arlock,
                         1'b0 };

    //=========================================================================
    // Hazard probes — debug-only, no fanout.
    //
    // These nets encode logical invariants of the W intake path.
    // Synthesis DCE removes them (they drive nothing); Verilator --trace
    // preserves them in the FST so you can spot a misbehavior at a glance
    // without grepping through every channel signal.
    //
    // Any one of them pulsing in simulation is a real bug — interpret as
    // "this invariant just broke."
    //=========================================================================

    // 1-cycle delayed observers used to compare edge-to-edge state changes
    logic [WPW-1:0] r_wbuf_wptr_q;
    logic           r_burst_done_q;
    logic           r_full_strb_acc_q;
    logic           r_w_beat_handshake_q;
    logic           r_wlast_q;
    logic           r_aw_push_hs_q;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wbuf_wptr_q        <= '0;
            r_burst_done_q       <= 1'b0;
            r_full_strb_acc_q    <= 1'b1;
            r_w_beat_handshake_q <= 1'b0;
            r_wlast_q            <= 1'b0;
            r_aw_push_hs_q       <= 1'b0;
        end else begin
            r_wbuf_wptr_q        <= r_wbuf_wptr;
            r_burst_done_q       <= r_burst_done;
            r_full_strb_acc_q    <= r_full_strb_acc;
            r_w_beat_handshake_q <= w_w_beat_handshake;
            r_wlast_q            <= fub_axi_wlast;
            r_aw_push_hs_q       <= aw_push_valid_o && aw_push_ready_i;
        end
    end)

    // (a) w_buf write-pointer changed in a cycle with no W beat handshake.
    //     Means a beat got written to w_buf without a valid AXI handshake —
    //     would corrupt w_buf and any subsequent snarf reads from it.
    logic w_hazard_wbuf_wptr_glitch;
    assign w_hazard_wbuf_wptr_glitch = (r_wbuf_wptr != r_wbuf_wptr_q)
                                    && !r_w_beat_handshake_q;

    // (b) burst_done rose without a wlast handshake on the previous cycle.
    //     burst_done is the gate that promotes a write into the wr CAM
    //     (aw_push_valid_o is gated on it). If it rises prematurely, the
    //     entry becomes snarf-eligible before the W beats have all landed.
    logic w_hazard_burst_done_premature;
    assign w_hazard_burst_done_premature = r_burst_done && !r_burst_done_q
                                        && !(r_w_beat_handshake_q && r_wlast_q);

    // (c) Another W beat handshake happened while r_burst_done was already
    //     set. fub_axi_wready is supposed to be gated by !r_burst_done so
    //     this is unreachable — but if it ever fires, the next burst is
    //     leaking into the current w_buf.
    logic w_hazard_w_after_wlast;
    assign w_hazard_w_after_wlast = r_burst_done && w_w_beat_handshake;

    // (d) full_strb_acc went from 0 → 1 without an aw_push handshake on the
    //     prior cycle. The only legal cause for that reset is the per-burst
    //     reset on AW-push accept. A spurious reset would let a partial-
    //     strobe burst look fully-covered → snarf eligible → silent
    //     data corruption.
    logic w_hazard_full_strb_acc_glitch;
    assign w_hazard_full_strb_acc_glitch = r_full_strb_acc && !r_full_strb_acc_q
                                        && !r_aw_push_hs_q;

    // (e) aw_push_valid_o asserted while r_burst_done is low. Trivially
    //     forbidden by the assign (`r_burst_done && w_aw_pend_rd_valid`),
    //     but keeping it visible catches any future regression that
    //     accidentally relaxes the gate.
    logic w_hazard_aw_push_before_burst_done;
    assign w_hazard_aw_push_before_burst_done = aw_push_valid_o && !r_burst_done;

    // OR of all individual hazards — single yellow flag for the
    // overview pane in gtkwave.
    logic w_hazard_any;
    assign w_hazard_any = w_hazard_wbuf_wptr_glitch
                       || w_hazard_burst_done_premature
                       || w_hazard_w_after_wlast
                       || w_hazard_full_strb_acc_glitch
                       || w_hazard_aw_push_before_burst_done;

    //=========================================================================
    // Observability counters — increment on each entry_complete strobe.
    // Useful for end-to-end health-check from CSR: total writes / reads
    // that round-tripped through the controller.
    //=========================================================================
    logic [15:0] r_wr_completions;
    logic [15:0] r_rd_completions;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_completions <= 16'd0;
            r_rd_completions <= 16'd0;
        end else begin
            if (wr_entry_complete_strb_i) r_wr_completions <= r_wr_completions + 16'd1;
            if (rd_entry_complete_strb_i) r_rd_completions <= r_rd_completions + 16'd1;
        end
    end)

    assign obs_wr_completions_o = r_wr_completions;
    assign obs_rd_completions_o = r_rd_completions;

    wire unused_rd_id = |rd_entry_complete_id_i;

endmodule : axi_intake
