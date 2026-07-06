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
//   docs/pumice_mas/ch02_blocks/02_axi4_slave.md
//
// Author: sean galloway
// Created: 2026-06-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_intake
    import pumice_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 64,
    parameter int AXI_ID_WIDTH      = 4,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_STRB_WIDTH    = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH   = 8,

    // TASK-GEAR: DRAM beat width may be NARROWER than the AXI data width
    // (e.g. AXI=64 driving an x16 DDR2 whose DFI per-phase = 2*16 = 32).
    // GEAR = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH DRAM beats pack into one AXI
    // beat. Default = AXI_DATA_WIDTH => GEAR=1 => bit-identical to the
    // legacy AXI==beat design. Everything the DRAM side sees (w_buf ptr,
    // aw_push_len, wbuf_ext read data, rd_inject data) is in DRAM-beat
    // units; only the s_axi_* host ports stay at AXI_DATA_WIDTH.
    parameter int DRAM_BEAT_WIDTH   = AXI_DATA_WIDTH,

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

    // w_buf storage — power-of-two for clean modulo wrap. NOTE (TASK-GEAR):
    // W_BUF_DEPTH now counts DRAM beats (== AXI beats when GEAR=1). The
    // AXI-beat capacity is W_BUF_DEPTH / GEAR. WPW addresses DRAM beats, so
    // it is unchanged vs the legacy design — no pointer-width ripple into
    // the wr CAM / wr_beat_sequencer / data_path.
    parameter int W_BUF_DEPTH       = 128,
    parameter int W_BUF_PTR_WIDTH   = $clog2(W_BUF_DEPTH),

    // Aliases (long names for external configuration)
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int SW  = AXI_STRB_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,

    // TASK-GEAR aliases
    parameter int DBW    = DRAM_BEAT_WIDTH,        // DRAM beat data width
    parameter int DSW    = DRAM_BEAT_WIDTH / 8,    // DRAM beat strobe width
    parameter int GEAR   = AXI_DATA_WIDTH / DRAM_BEAT_WIDTH,  // DRAM beats / AXI beat
    parameter int LGGEAR = (GEAR <= 1) ? 1 : $clog2(GEAR)
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
    // DRAM burst-length constraint (CSR-loaded after MR0 init). When the
    // host's AXI burst exceeds dram_bl_i beats, this FUB splits it into
    // ceil(awlen+1 / dram_bl_i) downstream pushes so each CAS-WR command
    // drives exactly dram_bl_i DRAM beats. dram_bl_i=0 disables splitting
    // (legacy FUB path / TB without BL plumbing).
    //=========================================================================
    input  logic [3:0]           dram_bl_i,

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
    // High on the LAST chunk of a split AW (always high if no split).
    // wr_cmd_cam stores this; axi_intake's B-path filters on it.
    output logic                 aw_push_is_last_chunk_o,

    //=========================================================================
    // Downstream AR push (to addr_mapper → wr2rd_forward / rd_cmd_cam)
    //=========================================================================
    output logic                 ar_push_valid_o,
    input  logic                 ar_push_ready_i,
    output logic [AW-1:0]        ar_push_addr_o,
    output logic [IW-1:0]        ar_push_id_o,
    output logic [BLW-1:0]       ar_push_len_o,
    output logic [3:0]           ar_push_qos_o,
    // High on the LAST chunk of a split AR (always high if no split).
    // wr2rd_forward forwards it; rd_cmd_cam stores it; rd_cl_aligner
    // reads it to gate rd_inject_last_o.
    output logic                 ar_push_is_last_chunk_o,

    //=========================================================================
    // Write completion (from wr_cmd_cam entry_complete) → B-channel push.
    // For split AXI bursts: every chunk's slot retire fires
    // wr_entry_complete_strb_i, but only the LAST chunk has
    // wr_entry_complete_is_last_chunk_i=1. Non-last chunks free their
    // CAM slot silently (no AXI B emitted) so the host sees exactly one
    // B per original AW.
    //=========================================================================
    input  logic                 wr_entry_complete_strb_i,
    input  logic [IW-1:0]        wr_entry_complete_id_i,
    input  logic                 wr_entry_complete_is_last_chunk_i,

    //=========================================================================
    // W-buffer free notification (driven by wr_beat_sequencer.b_complete via
    // the axi_frontend wiring). When `wbuf_free_strb_i` is high, the freed
    // burst's beat count is on `wbuf_free_len_i`; axi_intake subtracts that
    // from its outstanding-W-beat counter so the next AW(s) can land safely.
    // FUB-only setups can leave this idle (counter never decrements) and
    // drive it manually from the TB.
    //=========================================================================
    input  logic                 wbuf_free_strb_i,
    input  logic [BLW-1:0]       wbuf_free_len_i,

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
    // High when this forwarded chunk is the LAST chunk of its AR.
    // r_r_fwd_remaining alone fires rlast on every chunk boundary; this
    // gates rlast to ONLY fire on the last chunk's last beat (issue #22).
    input  logic                 fwd_is_last_chunk_i,

    //=========================================================================
    // Non-forwarded R-data injection (rd_data_path stub / TB)
    //=========================================================================
    // rd_inject carries ONE DRAM beat (DBW). axi_intake assembles GEAR of
    // them into one AXI R beat (DW) before returning to the host.
    input  logic                 rd_inject_valid_i,
    output logic                 rd_inject_ready_o,
    input  logic [IW-1:0]        rd_inject_id_i,
    input  logic [DBW-1:0]       rd_inject_data_i,
    input  logic                 rd_inject_last_i,

    //=========================================================================
    // External w_buf read port (wr_data_path stub / TB). Returns ONE DRAM
    // beat (DBW) at the requested DRAM-beat pointer.
    //=========================================================================
    input  logic [WPW-1:0]       wbuf_ext_rd_ptr_i,
    output logic [DBW-1:0]       wbuf_ext_rd_data_o,
    output logic [DSW-1:0]       wbuf_ext_rd_strb_o,

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
    // TASK-GEAR internal widths.
    //   LG   = log2(GEAR), 0 when GEAR==1 (used for ×GEAR / sub-beat index).
    //   BLWG = burst-len width in DRAM beats (pre-split total = (awlen+1)*GEAR
    //          can exceed BLW; per-chunk output len stays BLW).
    // At GEAR==1 these collapse to the legacy widths (LG=0, BLWG=BLW).
    //=========================================================================
    localparam int LG   = (GEAR <= 1) ? 0 : $clog2(GEAR);
    localparam int BLWG = BLW + LG;

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
        logic [BLWG-1:0] len;          // DRAM beats — (awlen+1)*GEAR
        logic [WPW-1:0]  w_buf_ptr;    // DRAM-beat start pointer
        logic [WPW-1:0]  strb_ptr;
        logic [2:0]      size;         // awsize — for split chunk address arithmetic
    } aw_pending_t;

    aw_pending_t        w_aw_pend_din;
    aw_pending_t        w_aw_pend_dout;
    logic               w_aw_pend_wr_valid;
    logic               w_aw_pend_wr_ready;
    logic               w_aw_pend_rd_valid;
    logic               w_aw_pend_rd_ready;

    // Monotonic w_buf write pointer — advances on each W beat accepted.
    logic [WPW-1:0]     r_wbuf_wptr;
    // Separate AW-side allocation pointer. Captures where each pending
    // AW's beats will START landing in w_buf. Required because the AXI4
    // host (e.g. axi4_master_wr_pattern_gen with its decoupled AW/W
    // path) can pipeline multiple AWs before any W beats arrive — using
    // r_wbuf_wptr for the capture would assign every queued AW the same
    // start pointer.
    logic [WPW-1:0]     r_aw_pend_next_ptr;

    assign w_aw_pend_din.id        = fub_axi_awid;
    assign w_aw_pend_din.addr      = fub_axi_awaddr;
    // DRAM-beat total = (awlen+1) * GEAR  (<<LG; LG=0 at GEAR=1).
    assign w_aw_pend_din.len       = (BLWG'(fub_axi_awlen) + BLWG'(1)) << LG;
    assign w_aw_pend_din.w_buf_ptr = r_aw_pend_next_ptr;
    assign w_aw_pend_din.strb_ptr  = r_aw_pend_next_ptr;
    assign w_aw_pend_din.size      = fub_axi_awsize;

    // ---- W-buffer occupancy + AW flow-control --------------------------
    // Track outstanding W beats (= pushed by accepted AWs - freed by
    // wr_beat_sequencer's b_complete). +1 bit so the counter can express
    // W_BUF_DEPTH itself (= "wbuf full").
    logic [WPW:0] r_wbuf_outstanding;
    logic [WPW:0] w_new_aw_burst_size;
    // Compute (awlen+1) in the WIDER of (BLW, WPW+1) so widening to the
    // (WPW+1) cast doesn't trip Verilator WIDTHEXPAND when WPW+1 > BLW
    // (e.g. W_BUF_DEPTH=512 → WPW+1=10 > BLW=8).
    // DRAM beats reserved by this AW = (awlen+1) * GEAR.
    assign w_new_aw_burst_size =
        (WPW+1)'(((WPW+1)'(fub_axi_awlen) + (WPW+1)'(1)) << LG);

    // The arriving AW would push (awlen+1) beats. Backpressure if that
    // would exceed wbuf depth. Without this gate the AW-side pointer
    // wraps and a new burst's beats overwrite still-pending data for an
    // older burst that wr_beat_sequencer hasn't drained yet.
    logic w_wbuf_room_for_new_aw;
    assign w_wbuf_room_for_new_aw =
        ((WPW+1)'(r_wbuf_outstanding) + w_new_aw_burst_size)
        <= (WPW+1)'(W_BUF_DEPTH);

    assign w_aw_pend_wr_valid = fub_axi_awvalid && w_wbuf_room_for_new_aw;
    assign fub_axi_awready    = w_aw_pend_wr_ready && w_wbuf_room_for_new_aw;

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
    // w_buf storage (distributed RAM) — DRAM-beat granular (TASK-GEAR).
    // At GEAR=1 (DBW==DW) this is identical to the legacy AXI-wide buffer.
    logic [DBW-1:0] r_w_buf      [W_BUF_DEPTH];
    logic [DSW-1:0] r_wstrb_buf  [W_BUF_DEPTH];

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

    // Forward declarations: these three nets are all driven further
    // below in the AW-split FSM but must be visible to this always_ff
    // block's r_burst_done / r_full_strb_acc gate (line ~609).
    logic w_aw_push_skid_in_valid;
    logic w_aw_push_skid_in_ready;
    logic w_is_last_chunk;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wbuf_wptr         <= '0;
            r_aw_pend_next_ptr  <= '0;
            r_wbuf_outstanding  <= '0;
            r_full_strb_acc     <= 1'b1;
            r_burst_done        <= 1'b0;
            r_final_full_strb   <= 1'b1;
        end else begin
            // Advance the AW-side allocation pointer + outstanding count
            // by awlen+1 on each accepted AW so the NEXT AW captures the
            // correct w_buf start position AND the flow-control gate sees
            // the new beats reserved.
            //
            // Same-cycle free is netted in here too so the counter never
            // briefly under/overshoots: if a free strobe arrives at the
            // moment a new AW is accepted, both adjustments apply.
            if (w_aw_pend_wr_valid && w_aw_pend_wr_ready) begin
                // Same widen-first idiom as w_new_aw_burst_size: do the
                // (awlen+1) at WPW width so 256-beat bursts (awlen=255)
                // don't wrap at BLW=8 bits.
                r_aw_pend_next_ptr <=
                    r_aw_pend_next_ptr +
                    WPW'((WPW'(fub_axi_awlen) + WPW'(1)) << LG);
                if (wbuf_free_strb_i) begin
                    r_wbuf_outstanding <=
                        r_wbuf_outstanding
                        + w_new_aw_burst_size
                        - (WPW+1)'(wbuf_free_len_i);
                end else begin
                    r_wbuf_outstanding <=
                        r_wbuf_outstanding
                        + w_new_aw_burst_size;
                end
            end else if (wbuf_free_strb_i) begin
                r_wbuf_outstanding <=
                    r_wbuf_outstanding - (WPW+1)'(wbuf_free_len_i);
            end
            if (w_w_beat_handshake) begin
                // TASK-GEAR: split the AXI beat (DW) into GEAR DRAM beats
                // (DBW each), LSB→MSB into consecutive w_buf entries. At
                // GEAR=1 this is the single legacy write. wptr advances by
                // GEAR DRAM beats.
                for (int g = 0; g < GEAR; g++) begin
                    r_w_buf    [r_wbuf_wptr + WPW'(g)] <= fub_axi_wdata[g*DBW +: DBW];
                    r_wstrb_buf[r_wbuf_wptr + WPW'(g)] <= fub_axi_wstrb[g*DSW +: DSW];
                end
                r_wbuf_wptr              <= r_wbuf_wptr + WPW'(GEAR);
                r_full_strb_acc          <= r_full_strb_acc & (&fub_axi_wstrb);
                if (fub_axi_wlast) begin
                    r_burst_done      <= 1'b1;
                    r_final_full_strb <= r_full_strb_acc & (&fub_axi_wstrb);
                end
            end
            // On the LAST chunk handshaking INTO the aw_push skid:
            // clear the burst-done flag and reset the strb accumulator.
            // Non-last chunks leave r_burst_done set so the next chunk's
            // push re-asserts on the very next cycle.
            if (w_aw_push_skid_in_valid && w_aw_push_skid_in_ready
                                        && w_is_last_chunk) begin
                r_burst_done    <= 1'b0;
                r_full_strb_acc <= 1'b1;
            end
        end
    end)

    //=========================================================================
    // AW-split chunk FSM (issue #22).
    //
    // When dram_bl_i is non-zero AND the head AW's len exceeds dram_bl_i,
    // the head pops out as ceil(len / dram_bl_i) downstream pushes:
    //   - chunk K's wbuf_ptr = head.w_buf_ptr + K*dram_bl_i
    //   - chunk K's addr     = head.addr      + K*dram_bl_i*(1<<head.size)
    //   - chunk K's len      = min(dram_bl_i, head.len - K*dram_bl_i)
    //   - chunk K's is_last  = (chunk K covers the final beat of head.len)
    // aw_pending head is held until the last-chunk push fires (only then
    // does r_burst_done clear).
    //
    // When dram_bl_i == 0 or head.len <= dram_bl_i, exactly one chunk
    // fires (the legacy / "no split" fast path).
    //
    // FPGA timing notes:
    //   * (1) `chunk_idx * bl` is replaced by a left-shift driven by a
    //     small log2 mux (dram_bl_i ∈ {0,1,2,4,8,16} only). No multiplier.
    //   * (2)+(3) A gaxi_skid_buffer between this comb path and the
    //     downstream addr_mapper registers chunk fields, so addr_mapper
    //     still sees a flop output (same depth as pre-#22). Skid adds
    //     1 cycle of latency per AW; steady-state throughput is 1 chunk
    //     per cycle so streaming holds.
    //=========================================================================
    logic [BLW-1:0]  r_chunk_idx;
    logic [BLWG-1:0] w_eff_bl;
    // Treat dram_bl_i==0 as "no split". Use head.len directly so the
    // single-chunk gate always fires on the first push. NOTE: dram_bl_i and
    // head.len are both in DRAM beats (TASK-GEAR).
    assign w_eff_bl = (dram_bl_i == 4'd0) ? w_aw_pend_dout.len
                                          : BLWG'(dram_bl_i);
    // log2(eff_bl) — small mux on dram_bl_i so the chunk offset is just
    // a left-shift, not a multiply. DDR2/LPDDR2 only ever programs BL to
    // a power of two, so this is exact (no rounding).
    logic [2:0] w_eff_bl_log2;
    always_comb begin
        // dram_bl_i is 4 bits (max 4'd15). DDR2/LPDDR2 program BL to
        // 4 or 8 only; 1/2 kept for TB / narrow-AXI paths. BL=16 has
        // no representation in a 4-bit field so it doesn't need a case
        // (that width mismatch would silently truncate).
        unique case (dram_bl_i)
            4'd1:    w_eff_bl_log2 = 3'd0;
            4'd2:    w_eff_bl_log2 = 3'd1;
            4'd4:    w_eff_bl_log2 = 3'd2;
            4'd8:    w_eff_bl_log2 = 3'd3;
            default: w_eff_bl_log2 = 3'd0;  // dram_bl_i==0 → no-split (idx stays 0)
        endcase
    end
    logic [BLWG-1:0] w_chunk_offset_beats;
    assign w_chunk_offset_beats = BLWG'(r_chunk_idx) << w_eff_bl_log2;
    logic [BLWG:0]   w_remaining_ext;
    assign w_remaining_ext = {1'b0, w_aw_pend_dout.len}
                           - {1'b0, w_chunk_offset_beats};
    logic [BLWG-1:0] w_remaining;
    assign w_remaining = w_remaining_ext[BLWG-1:0];
    logic [BLWG-1:0] w_chunk_len;
    assign w_chunk_len = (w_remaining > w_eff_bl) ? w_eff_bl : w_remaining;
    // w_is_last_chunk forward-declared near the top of the module.
    assign w_is_last_chunk = (w_remaining <= w_eff_bl);

    // Chunk address: head.addr + chunk_offset_beats * DRAM-beat-bytes.
    // chunk_offset is in DRAM beats; each DRAM beat is (1<<(awsize-LG)) bytes
    // (awsize is the AXI-beat byte size; one AXI beat = GEAR DRAM beats).
    logic [2:0] w_dram_size;
    generate
        if (LG == 0) begin : g_dram_size_g1
            assign w_dram_size = w_aw_pend_dout.size;
        end else begin : g_dram_size_gn
            assign w_dram_size = (w_aw_pend_dout.size >= 3'(LG))
                               ? (w_aw_pend_dout.size - 3'(LG)) : 3'd0;
        end
    endgenerate
    logic [AW-1:0] w_chunk_addr_off;
    assign w_chunk_addr_off = AW'(w_chunk_offset_beats) << w_dram_size;
    logic [AW-1:0] w_chunk_addr;
    assign w_chunk_addr = w_aw_pend_dout.addr + w_chunk_addr_off;
    logic [WPW-1:0] w_chunk_wbuf_ptr;
    assign w_chunk_wbuf_ptr = w_aw_pend_dout.w_buf_ptr
                            + WPW'(w_chunk_offset_beats);
    logic [WPW-1:0] w_chunk_strb_ptr;
    assign w_chunk_strb_ptr = w_aw_pend_dout.strb_ptr
                            + WPW'(w_chunk_offset_beats);

    // ---- AW push skid -------------------------------------------------
    typedef struct packed {
        logic [AW-1:0]  addr;
        logic [IW-1:0]  id;
        logic [BLW-1:0] len;
        logic [WPW-1:0] w_buf_ptr;
        logic [WPW-1:0] strb_ptr;
        logic           full_strb;
        logic [3:0]     qos;
        logic           is_last_chunk;
    } aw_push_skid_t;

    aw_push_skid_t w_aw_push_skid_in;
    aw_push_skid_t w_aw_push_skid_out;
    // w_aw_push_skid_in_{valid,ready} forward-declared near the top of the module.

    assign w_aw_push_skid_in.addr          = w_chunk_addr;
    assign w_aw_push_skid_in.id            = w_aw_pend_dout.id;
    assign w_aw_push_skid_in.len           = BLW'(w_chunk_len);
    assign w_aw_push_skid_in.w_buf_ptr     = w_chunk_wbuf_ptr;
    assign w_aw_push_skid_in.strb_ptr      = w_chunk_strb_ptr;
    assign w_aw_push_skid_in.full_strb     = r_final_full_strb;
    assign w_aw_push_skid_in.qos           = w_aw_push_qos;
    assign w_aw_push_skid_in.is_last_chunk = w_is_last_chunk;

    // Push into skid as soon as the host's wlast lands and the
    // ar_pending head is valid. Each handshake into the skid is one
    // chunk; the chunk-idx advances per skid-IN handshake (NOT per
    // module-output handshake, which lags by skid latency).
    assign w_aw_push_skid_in_valid = r_burst_done && w_aw_pend_rd_valid;

    // Pop aw_pending head only when the LAST chunk handshakes INTO the
    // skid. Non-last chunks advance r_chunk_idx but leave the head in
    // the ar_pending FIFO so the next cycle re-emits with chunk K+1.
    assign w_aw_pend_rd_ready = w_aw_push_skid_in_valid
                             && w_aw_push_skid_in_ready
                             && w_is_last_chunk;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_chunk_idx <= '0;
        end else if (w_aw_push_skid_in_valid && w_aw_push_skid_in_ready) begin
            r_chunk_idx <= w_is_last_chunk ? BLW'(0)
                                           : r_chunk_idx + BLW'(1);
        end
    end)

    gaxi_skid_buffer #(
        .DATA_WIDTH ($bits(aw_push_skid_t)),
        .DEPTH      (2)
    ) i_aw_push_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_push_skid_in_valid),
        .wr_ready    (w_aw_push_skid_in_ready),
        .wr_data     (w_aw_push_skid_in),
        .count       (),
        .rd_valid    (aw_push_valid_o),
        .rd_ready    (aw_push_ready_i),
        .rd_count    (),
        .rd_data     (w_aw_push_skid_out)
    );

    assign aw_push_addr_o          = w_aw_push_skid_out.addr;
    assign aw_push_id_o            = w_aw_push_skid_out.id;
    assign aw_push_len_o           = w_aw_push_skid_out.len;
    assign aw_push_w_buf_ptr_o     = w_aw_push_skid_out.w_buf_ptr;
    assign aw_push_strb_ptr_o      = w_aw_push_skid_out.strb_ptr;
    assign aw_push_full_strb_o     = w_aw_push_skid_out.full_strb;
    assign aw_push_qos_o           = w_aw_push_skid_out.qos;
    assign aw_push_is_last_chunk_o = w_aw_push_skid_out.is_last_chunk;

    //=========================================================================
    // ar_pending FIFO — head buffer for AR metadata
    //=========================================================================
    typedef struct packed {
        logic [IW-1:0]   id;
        logic [AW-1:0]   addr;
        logic [BLWG-1:0] len;         // DRAM beats — (arlen+1)*GEAR
        logic [2:0]      size;        // arsize — for split chunk addr arithmetic
    } ar_pending_t;

    ar_pending_t   w_ar_pend_din;
    ar_pending_t   w_ar_pend_dout;
    logic          w_ar_pend_wr_valid;
    logic          w_ar_pend_wr_ready;
    logic          w_ar_pend_rd_valid;
    logic          w_ar_pend_rd_ready;

    assign w_ar_pend_din.id   = fub_axi_arid;
    assign w_ar_pend_din.addr = fub_axi_araddr;
    // DRAM-beat total = (arlen+1) * GEAR.
    assign w_ar_pend_din.len  = (BLWG'(fub_axi_arlen) + BLWG'(1)) << LG;
    assign w_ar_pend_din.size = fub_axi_arsize;

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

    //=========================================================================
    // AR-split chunk FSM (issue #22 — mirror of AW-split above).
    //
    // Same shift-not-mult + skid topology as AW; see notes above.
    //=========================================================================
    logic [BLW-1:0]  r_ar_chunk_idx;
    logic [BLWG-1:0] w_ar_eff_bl;
    assign w_ar_eff_bl = (dram_bl_i == 4'd0) ? w_ar_pend_dout.len
                                              : BLWG'(dram_bl_i);
    // log2 mux mirrors AW side; same constants, share via w_eff_bl_log2.
    logic [BLWG-1:0] w_ar_chunk_offset_beats;
    assign w_ar_chunk_offset_beats = BLWG'(r_ar_chunk_idx) << w_eff_bl_log2;
    logic [BLWG:0]   w_ar_remaining_ext;
    assign w_ar_remaining_ext = {1'b0, w_ar_pend_dout.len}
                              - {1'b0, w_ar_chunk_offset_beats};
    logic [BLWG-1:0] w_ar_remaining;
    assign w_ar_remaining = w_ar_remaining_ext[BLWG-1:0];
    logic [BLWG-1:0] w_ar_chunk_len;
    assign w_ar_chunk_len = (w_ar_remaining > w_ar_eff_bl)
                          ? w_ar_eff_bl : w_ar_remaining;
    logic           w_ar_is_last_chunk;
    assign w_ar_is_last_chunk = (w_ar_remaining <= w_ar_eff_bl);

    logic [2:0] w_ar_dram_size;
    generate
        if (LG == 0) begin : g_ar_dram_size_g1
            assign w_ar_dram_size = w_ar_pend_dout.size;
        end else begin : g_ar_dram_size_gn
            assign w_ar_dram_size = (w_ar_pend_dout.size >= 3'(LG))
                                  ? (w_ar_pend_dout.size - 3'(LG)) : 3'd0;
        end
    endgenerate
    logic [AW-1:0] w_ar_chunk_addr_off;
    assign w_ar_chunk_addr_off =
        AW'(w_ar_chunk_offset_beats) << w_ar_dram_size;
    logic [AW-1:0] w_ar_chunk_addr;
    assign w_ar_chunk_addr = w_ar_pend_dout.addr + w_ar_chunk_addr_off;

    // ---- AR push skid -------------------------------------------------
    typedef struct packed {
        logic [AW-1:0]  addr;
        logic [IW-1:0]  id;
        logic [BLW-1:0] len;
        logic [3:0]     qos;
        logic           is_last_chunk;
    } ar_push_skid_t;

    ar_push_skid_t w_ar_push_skid_in;
    ar_push_skid_t w_ar_push_skid_out;
    logic          w_ar_push_skid_in_valid;
    logic          w_ar_push_skid_in_ready;

    assign w_ar_push_skid_in.addr          = w_ar_chunk_addr;
    assign w_ar_push_skid_in.id            = w_ar_pend_dout.id;
    assign w_ar_push_skid_in.len           = BLW'(w_ar_chunk_len);
    assign w_ar_push_skid_in.qos           = w_ar_push_qos;
    assign w_ar_push_skid_in.is_last_chunk = w_ar_is_last_chunk;

    assign w_ar_push_skid_in_valid = w_ar_pend_rd_valid;

    // Pop ar_pending head only when the LAST chunk handshakes IN.
    assign w_ar_pend_rd_ready = w_ar_push_skid_in_valid
                             && w_ar_push_skid_in_ready
                             && w_ar_is_last_chunk;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_ar_chunk_idx <= '0;
        end else if (w_ar_push_skid_in_valid && w_ar_push_skid_in_ready) begin
            r_ar_chunk_idx <= w_ar_is_last_chunk ? BLW'(0)
                                                 : r_ar_chunk_idx + BLW'(1);
        end
    end)

    gaxi_skid_buffer #(
        .DATA_WIDTH ($bits(ar_push_skid_t)),
        .DEPTH      (2)
    ) i_ar_push_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_push_skid_in_valid),
        .wr_ready    (w_ar_push_skid_in_ready),
        .wr_data     (w_ar_push_skid_in),
        .count       (),
        .rd_valid    (ar_push_valid_o),
        .rd_ready    (ar_push_ready_i),
        .rd_count    (),
        .rd_data     (w_ar_push_skid_out)
    );

    assign ar_push_addr_o          = w_ar_push_skid_out.addr;
    assign ar_push_id_o            = w_ar_push_skid_out.id;
    assign ar_push_len_o           = w_ar_push_skid_out.len;
    assign ar_push_qos_o           = w_ar_push_skid_out.qos;
    assign ar_push_is_last_chunk_o = w_ar_push_skid_out.is_last_chunk;

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
    // Filter: only the LAST chunk of a split AXI burst pushes a B FIFO
    // entry. Non-last chunks free their CAM slot silently (issue #22).
    assign w_b_wr_valid = wr_entry_complete_strb_i
                       && wr_entry_complete_is_last_chunk_i;

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
    // Captured at fwd handshake; gates fub_axi_rlast in the forwarded
    // R-path so chunked ARs don't fire early rlast (issue #22).
    logic           r_r_fwd_is_last_chunk;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_r_fwd_active    <= 1'b0;
            r_r_fwd_id        <= '0;
            r_r_fwd_ptr       <= '0;
            r_r_fwd_remaining <= '0;
            r_r_fwd_is_last_chunk <= 1'b0;
        end else begin
            if (fwd_valid_i && fwd_ready_o) begin
                r_r_fwd_active    <= 1'b1;
                r_r_fwd_id        <= fwd_id_i;
                r_r_fwd_ptr       <= fwd_w_buf_ptr_i;
                r_r_fwd_remaining <= fwd_len_i;
                r_r_fwd_is_last_chunk <= fwd_is_last_chunk_i;
            end else if (r_r_fwd_active && fub_axi_rvalid && fub_axi_rready) begin
                // One AXI R beat = GEAR DRAM beats. fwd_len_i is in DRAM
                // beats (always a multiple of GEAR since forwarded reads are
                // whole AXI beats), so advance/consume by GEAR per R beat.
                r_r_fwd_ptr       <= r_r_fwd_ptr + WPW'(GEAR);
                r_r_fwd_remaining <= r_r_fwd_remaining - BLW'(GEAR);
                if (r_r_fwd_remaining == BLW'(GEAR)) begin
                    r_r_fwd_active <= 1'b0;
                end
            end
        end
    end)

    // fwd_ready_o — accept a new forwarded burst only when not currently
    // emitting one.
    assign fwd_ready_o = !r_r_fwd_active;

    //---------------------------------------------------------------------
    // TASK-GEAR read assembly.
    //  * Forwarded path: assemble GEAR consecutive DRAM-beat w_buf entries
    //    (starting at the GEAR-aligned r_r_fwd_ptr) into one AXI R beat.
    //  * Injected path: rd_inject delivers ONE DRAM beat per handshake;
    //    accumulate GEAR of them, emit one AXI R beat on the GEAR-th.
    // At GEAR=1 both collapse to the legacy pass-through.
    //---------------------------------------------------------------------
    logic [DW-1:0]      w_fwd_rdata;
    always_comb begin
        w_fwd_rdata = '0;
        for (int g = 0; g < GEAR; g++) begin
            w_fwd_rdata[g*DBW +: DBW] = r_w_buf[r_r_fwd_ptr + WPW'(g)];
        end
    end

    logic [DW-1:0]     r_inj_acc;      // holds the first GEAR-1 DRAM beats
    logic [LGGEAR-1:0] r_inj_cnt;      // which DRAM beat within the AXI beat
    logic              w_inj_last_beat; // this DRAM beat completes an AXI beat
    assign w_inj_last_beat = (r_inj_cnt == LGGEAR'(GEAR-1));

    logic [DW-1:0] w_inj_rdata;
    always_comb begin
        w_inj_rdata = r_inj_acc;
        w_inj_rdata[r_inj_cnt*DBW +: DBW] = rd_inject_data_i;
    end

    // rd_inject_ready — non-final DRAM beats are buffered freely (no
    // downstream handshake); the final beat of a group waits for the R
    // skid. Forwarded burst has priority (blocks inject).
    assign rd_inject_ready_o = !r_r_fwd_active
                            && (!w_inj_last_beat || fub_axi_rready);

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_inj_acc <= '0;
            r_inj_cnt <= '0;
        end else if (rd_inject_valid_i && rd_inject_ready_o) begin
            if (w_inj_last_beat) begin
                r_inj_cnt <= '0;
            end else begin
                r_inj_acc[r_inj_cnt*DBW +: DBW] <= rd_inject_data_i;
                r_inj_cnt <= r_inj_cnt + 1'b1;
            end
        end
    end)

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
            fub_axi_rdata  = w_fwd_rdata;
            fub_axi_rresp  = 2'b00;
            fub_axi_rlast  = (r_r_fwd_remaining == BLW'(GEAR))
                          && r_r_fwd_is_last_chunk;
            // RUSER mirrors ARUSER from the id-side-table completion port.
            // (w_ar_compl_id selects r_r_fwd_id when r_r_fwd_active.)
            fub_axi_ruser  = w_ar_compl_user;
        end else if (rd_inject_valid_i && w_inj_last_beat) begin
            // Emit only on the GEAR-th DRAM beat (full AXI beat assembled).
            fub_axi_rvalid = 1'b1;
            fub_axi_rid    = rd_inject_id_i;
            fub_axi_rdata  = w_inj_rdata;
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
