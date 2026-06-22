// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_frontend_macro
// Purpose: Integration macro bundling the AXI-frontend FUBs into one
//          testable / synthesizable group.
//
// Description:
//   Wraps the host-AXI4 protocol layer plus address decoding, the two
//   per-direction CAMs, and the write→read snarf path:
//
//     - axi_intake  (host AXI4 protocol + w_buf + b_fifo + fwd-R emit)
//     - addr_mapper (×2 — AW side, AR side; both combinational)
//     - wr_cmd_cam
//     - rd_cmd_cam
//     - wr2rd_forward
//
//   Flow (write):
//     host AW/W → axi_intake → aw_push (decoded by addr_mapper_aw) →
//     wr_cmd_cam → scheduler picks → beat_pull pulls from axi_intake's
//     w_buf via wbuf_ext_rd port → xbank_timers' b_complete strobe →
//     wr_cmd_cam entry_complete → axi_intake B response
//
//   Flow (read):
//     host AR → axi_intake → ar_push (decoded by addr_mapper_ar) →
//     wr2rd_forward → either:
//       (a) fwd hit → axi_intake pulls R data from w_buf at fwd_w_buf_ptr
//       (b) miss → rd_cmd_cam push → scheduler picks → rd_data_path stub
//                  (rd_inject) → axi_intake forwards as R beats
//
//   The macro is the testable unit for the AXI-ingress side of the
//   controller. axi_intake uses rtl/amba axi4_slave_wr / axi4_slave_rd
//   for the wire-level protocol, NOT a hand-rolled valid/ready engine.
//
// References:
//   docs/ddr2_lpddr2_mas/ch01_overview/01_architecture.md
//   docs/ddr2_lpddr2_mas/ch02_blocks/03_addr_mapper.md
//   docs/ddr2_lpddr2_mas/ch02_blocks/04_rd_cmd_cam.md
//   docs/ddr2_lpddr2_mas/ch02_blocks/05_wr_cmd_cam.md
//
// Author: sean galloway
// Created: 2026-06-17 (revised 2026-06-18: axi_intake integrated)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_frontend_macro
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int AXI_DATA_WIDTH       = 64,
    parameter int AXI_ID_WIDTH         = 4,
    parameter int AXI_USER_WIDTH       = 1,
    parameter int AXI_STRB_WIDTH       = AXI_DATA_WIDTH / 8,
    parameter int NUM_RANKS            = 1,
    parameter int NUM_BANKS            = 8,
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BURST_LEN_WIDTH      = 8,
    parameter int W_BUF_DEPTH          = 128,
    parameter int W_BUF_PTR_WIDTH      = $clog2(W_BUF_DEPTH),
    parameter int BYTE_OFFSET_WIDTH    = 3,
    parameter int WR_CAM_DEPTH         = 16,
    parameter int RD_CAM_DEPTH         = 16,
    parameter int SKID_DEPTH_AW        = 2,
    parameter int SKID_DEPTH_W         = 4,
    parameter int SKID_DEPTH_B         = 2,
    parameter int SKID_DEPTH_AR        = 2,
    parameter int SKID_DEPTH_R         = 4,
    parameter int AW_PENDING_DEPTH     = 4,
    parameter int AR_PENDING_DEPTH     = 4,
    parameter int B_FIFO_DEPTH         = 4,
    parameter bit SYNTH_ROW_MAJOR       = 1'b1,
    parameter bit SYNTH_BANK_INTERLEAVE = 1'b1,
    parameter bit SYNTH_XOR_HASH        = 1'b0,

    // Aliases
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int SW  = AXI_STRB_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // CSR (live)
    input  addr_map_scheme_e     scheme_active_i,
    input  logic [7:0]           xor_seed_i,

    //=========================================================================
    // AXI4 slave-side host ports (host drives s_axi_aw/w/ar; this macro
    // drives s_axi_b/r back)
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
    // Read-data injection (TB stub for rd_data_path; drives non-forwarded R)
    //=========================================================================
    input  logic                 rd_inject_valid_i,
    output logic                 rd_inject_ready_o,
    input  logic [IW-1:0]        rd_inject_id_i,
    input  logic [DW-1:0]        rd_inject_data_i,
    input  logic                 rd_inject_last_i,

    //=========================================================================
    // External w_buf read-back (data sourced for the slot currently being
    // beat-pulled by the scheduler stub / wr_data_path TB)
    //=========================================================================
    output logic [DW-1:0]        wbuf_ext_rd_data_o,
    output logic [SW-1:0]        wbuf_ext_rd_strb_o,

    //=========================================================================
    // Scheduler query (per-(rank, bank), with row for row-hit check)
    //=========================================================================
    input  logic [RKW-1:0]                  q_rank_i,
    input  logic [BKW-1:0]                  q_bank_i,
    input  logic [RW-1:0]                   q_row_i,
    output logic [WR_CAM_DEPTH-1:0]         wr_match_pending_o,
    output logic [WR_CAM_DEPTH-1:0]         wr_match_rowhit_o,
    output logic [RD_CAM_DEPTH-1:0]         rd_match_pending_o,
    output logic [RD_CAM_DEPTH-1:0]         rd_match_rowhit_o,

    //=========================================================================
    // Per-slot snapshots (combinational; scheduler picks a slot and uses
    // its decoded tuple directly rather than driving q_* per cycle)
    //=========================================================================
    output logic [WR_CAM_DEPTH-1:0][RKW-1:0] wr_snap_rank_o,
    output logic [WR_CAM_DEPTH-1:0][BKW-1:0] wr_snap_bank_o,
    output logic [WR_CAM_DEPTH-1:0][RW-1:0]  wr_snap_row_o,
    output logic [WR_CAM_DEPTH-1:0][CW-1:0]  wr_snap_col_o,
    output logic [WR_CAM_DEPTH-1:0][BLW-1:0] wr_snap_len_o,
    output logic [RD_CAM_DEPTH-1:0][RKW-1:0] rd_snap_rank_o,
    output logic [RD_CAM_DEPTH-1:0][BKW-1:0] rd_snap_bank_o,
    output logic [RD_CAM_DEPTH-1:0][RW-1:0]  rd_snap_row_o,
    output logic [RD_CAM_DEPTH-1:0][CW-1:0]  rd_snap_col_o,
    output logic [RD_CAM_DEPTH-1:0][BLW-1:0] rd_snap_len_o,

    //=========================================================================
    // Scheduler "mark issued" strobes
    //=========================================================================
    input  logic                 wr_issued_we_i,
    input  logic [WSL-1:0]       wr_issued_slot_i,
    input  logic                 rd_issued_we_i,
    input  logic [RSL-1:0]       rd_issued_slot_i,

    //=========================================================================
    // Write data-path beat pull (consumed by wr_data_path stub; the macro
    // wires this to axi_intake's w_buf read port internally)
    //=========================================================================
    input  logic                 beat_pull_strb_i,
    input  logic [WSL-1:0]       beat_pull_slot_i,
    output logic [WPW-1:0]       beat_pull_ptr_o,
    output logic [WPW-1:0]       beat_pull_strb_ptr_o,
    output logic                 beat_pull_last_o,

    //=========================================================================
    // Write completion (from xbank_timers stub / TB)
    //=========================================================================
    input  logic                 b_complete_strb_i,
    input  logic [WSL-1:0]       b_complete_slot_i,
    output logic                 wr_entry_complete_o,
    output logic [WSL-1:0]       wr_entry_complete_slot_o,
    output logic [IW-1:0]        wr_entry_complete_id_o,

    //=========================================================================
    // Read beat acknowledgement (when AXI R beat fully accepted by host)
    //=========================================================================
    input  logic                 rd_beat_we_i,
    input  logic [RSL-1:0]       rd_beat_slot_i,
    output logic                 rd_entry_complete_o,
    output logic [RSL-1:0]       rd_entry_complete_slot_o,
    output logic [IW-1:0]        rd_entry_complete_id_o,

    //=========================================================================
    // Telemetry / debug
    //=========================================================================
    output logic                 dbg_intake_busy_o,
    output logic [WSL:0]         dbg_wr_cam_occ_o,
    output logic [RSL:0]         dbg_rd_cam_occ_o,
    output logic                 dbg_forward_hit_o,
    output logic                 dbg_forward_miss_o,
    output logic                 dbg_fwd_valid_o,
    output logic [WSL-1:0]       dbg_fwd_src_slot_o,
    output logic [IW-1:0]        dbg_fwd_id_o
);

    //=========================================================================
    // axi_intake — host AXI4 protocol layer + w_buf + B FIFO + R emit
    //=========================================================================
    // aw_push_* go through addr_mapper_aw → wr_cmd_cam.push_*
    logic                 w_aw_push_valid;
    logic                 w_aw_push_ready;
    logic [AW-1:0]        w_aw_push_addr;
    logic [IW-1:0]        w_aw_push_id;
    logic [BLW-1:0]       w_aw_push_len;
    logic [WPW-1:0]       w_aw_push_w_buf_ptr;
    logic [WPW-1:0]       w_aw_push_strb_ptr;
    logic                 w_aw_push_full_strb;

    // ar_push_* go through addr_mapper_ar → wr2rd_forward.ar_*
    logic                 w_ar_push_valid;
    logic                 w_ar_push_ready;
    logic [AW-1:0]        w_ar_push_addr;
    logic [IW-1:0]        w_ar_push_id;
    logic [BLW-1:0]       w_ar_push_len;

    // wr2rd_forward.fwd_* → axi_intake.fwd_*
    logic                 w_fwd_valid;
    logic                 w_fwd_ready;
    logic [IW-1:0]        w_fwd_id;
    logic [WPW-1:0]       w_fwd_w_buf_ptr;
    logic [BLW-1:0]       w_fwd_len;
    logic [WSL-1:0]       w_fwd_src_slot;

    // wr_cmd_cam.entry_complete_* → axi_intake
    logic                 w_wr_entry_complete;
    logic [WSL-1:0]       w_wr_entry_complete_slot;
    logic [IW-1:0]        w_wr_entry_complete_id;

    axi_intake #(
        .AXI_ADDR_WIDTH    (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        .AXI_USER_WIDTH    (AXI_USER_WIDTH),
        .AXI_STRB_WIDTH    (AXI_STRB_WIDTH),
        .BURST_LEN_WIDTH   (BURST_LEN_WIDTH),
        .SKID_DEPTH_AW     (SKID_DEPTH_AW),
        .SKID_DEPTH_W      (SKID_DEPTH_W),
        .SKID_DEPTH_B      (SKID_DEPTH_B),
        .SKID_DEPTH_AR     (SKID_DEPTH_AR),
        .SKID_DEPTH_R      (SKID_DEPTH_R),
        .AW_PENDING_DEPTH  (AW_PENDING_DEPTH),
        .AR_PENDING_DEPTH  (AR_PENDING_DEPTH),
        .B_FIFO_DEPTH      (B_FIFO_DEPTH),
        .W_BUF_DEPTH       (W_BUF_DEPTH),
        .W_BUF_PTR_WIDTH   (W_BUF_PTR_WIDTH)
    ) u_axi_intake (
        .aclk                       (mc_clk),
        .aresetn                    (mc_rst_n),
        // Host AXI4
        .s_axi_awid                 (s_axi_awid),
        .s_axi_awaddr               (s_axi_awaddr),
        .s_axi_awlen                (s_axi_awlen),
        .s_axi_awsize               (s_axi_awsize),
        .s_axi_awburst              (s_axi_awburst),
        .s_axi_awlock               (s_axi_awlock),
        .s_axi_awcache              (s_axi_awcache),
        .s_axi_awprot               (s_axi_awprot),
        .s_axi_awqos                (s_axi_awqos),
        .s_axi_awregion             (s_axi_awregion),
        .s_axi_awuser               (s_axi_awuser),
        .s_axi_awvalid              (s_axi_awvalid),
        .s_axi_awready              (s_axi_awready),
        .s_axi_wdata                (s_axi_wdata),
        .s_axi_wstrb                (s_axi_wstrb),
        .s_axi_wlast                (s_axi_wlast),
        .s_axi_wuser                (s_axi_wuser),
        .s_axi_wvalid               (s_axi_wvalid),
        .s_axi_wready               (s_axi_wready),
        .s_axi_bid                  (s_axi_bid),
        .s_axi_bresp                (s_axi_bresp),
        .s_axi_buser                (s_axi_buser),
        .s_axi_bvalid               (s_axi_bvalid),
        .s_axi_bready               (s_axi_bready),
        .s_axi_arid                 (s_axi_arid),
        .s_axi_araddr               (s_axi_araddr),
        .s_axi_arlen                (s_axi_arlen),
        .s_axi_arsize               (s_axi_arsize),
        .s_axi_arburst              (s_axi_arburst),
        .s_axi_arlock               (s_axi_arlock),
        .s_axi_arcache              (s_axi_arcache),
        .s_axi_arprot               (s_axi_arprot),
        .s_axi_arqos                (s_axi_arqos),
        .s_axi_arregion             (s_axi_arregion),
        .s_axi_aruser               (s_axi_aruser),
        .s_axi_arvalid              (s_axi_arvalid),
        .s_axi_arready              (s_axi_arready),
        .s_axi_rid                  (s_axi_rid),
        .s_axi_rdata                (s_axi_rdata),
        .s_axi_rresp                (s_axi_rresp),
        .s_axi_rlast                (s_axi_rlast),
        .s_axi_ruser                (s_axi_ruser),
        .s_axi_rvalid               (s_axi_rvalid),
        .s_axi_rready               (s_axi_rready),
        // Downstream AW/AR push (to addr_mapper + CAMs)
        .aw_push_valid_o            (w_aw_push_valid),
        .aw_push_ready_i            (w_aw_push_ready),
        .aw_push_addr_o             (w_aw_push_addr),
        .aw_push_id_o               (w_aw_push_id),
        .aw_push_len_o              (w_aw_push_len),
        .aw_push_w_buf_ptr_o        (w_aw_push_w_buf_ptr),
        .aw_push_strb_ptr_o         (w_aw_push_strb_ptr),
        .aw_push_full_strb_o        (w_aw_push_full_strb),
        .ar_push_valid_o            (w_ar_push_valid),
        .ar_push_ready_i            (w_ar_push_ready),
        .ar_push_addr_o             (w_ar_push_addr),
        .ar_push_id_o               (w_ar_push_id),
        .ar_push_len_o              (w_ar_push_len),
        // Completion notifications
        .wr_entry_complete_strb_i   (w_wr_entry_complete),
        .wr_entry_complete_id_i     (w_wr_entry_complete_id),
        .rd_entry_complete_strb_i   (rd_entry_complete_o),
        .rd_entry_complete_id_i     (rd_entry_complete_id_o),
        // Forwarded R
        .fwd_valid_i                (w_fwd_valid),
        .fwd_ready_o                (w_fwd_ready),
        .fwd_id_i                   (w_fwd_id),
        .fwd_w_buf_ptr_i            (w_fwd_w_buf_ptr),
        .fwd_len_i                  (w_fwd_len),
        // Injected R
        .rd_inject_valid_i          (rd_inject_valid_i),
        .rd_inject_ready_o          (rd_inject_ready_o),
        .rd_inject_id_i             (rd_inject_id_i),
        .rd_inject_data_i           (rd_inject_data_i),
        .rd_inject_last_i           (rd_inject_last_i),
        // External w_buf read (driven by beat_pull's ptr internally)
        .wbuf_ext_rd_ptr_i          (beat_pull_ptr_o),
        .wbuf_ext_rd_data_o         (wbuf_ext_rd_data_o),
        .wbuf_ext_rd_strb_o         (wbuf_ext_rd_strb_o),
        .busy_o                     (dbg_intake_busy_o),
        // obs_* — harvested for CSR in the obs_* pass
        .obs_wr_completions_o       (),
        .obs_rd_completions_o       ()
    );

    //=========================================================================
    // AW-side address mapper
    //=========================================================================
    logic [RKW-1:0] w_aw_rank;
    logic [BKW-1:0] w_aw_bank;
    logic [RW-1:0]  w_aw_row;
    logic [CW-1:0]  w_aw_col;

    addr_mapper #(
        .AXI_ADDR_WIDTH        (AXI_ADDR_WIDTH),
        .NUM_RANKS             (NUM_RANKS),
        .NUM_BANKS             (NUM_BANKS),
        .ROW_WIDTH             (ROW_WIDTH),
        .COL_WIDTH             (COL_WIDTH),
        .BYTE_OFFSET_WIDTH     (BYTE_OFFSET_WIDTH),
        .SYNTH_ROW_MAJOR       (SYNTH_ROW_MAJOR),
        .SYNTH_BANK_INTERLEAVE (SYNTH_BANK_INTERLEAVE),
        .SYNTH_XOR_HASH        (SYNTH_XOR_HASH)
    ) u_addr_mapper_aw (
        .axi_addr_i      (w_aw_push_addr),
        .scheme_active_i (scheme_active_i),
        .xor_seed_i      (xor_seed_i),
        .bg_field_pos_i  (3'd0),
        .rank_o          (w_aw_rank),
        .bank_o          (w_aw_bank),
        .row_o           (w_aw_row),
        .col_o           (w_aw_col)
    );

    //=========================================================================
    // AR-side address mapper
    //=========================================================================
    logic [RKW-1:0] w_ar_rank;
    logic [BKW-1:0] w_ar_bank;
    logic [RW-1:0]  w_ar_row;
    logic [CW-1:0]  w_ar_col;

    addr_mapper #(
        .AXI_ADDR_WIDTH        (AXI_ADDR_WIDTH),
        .NUM_RANKS             (NUM_RANKS),
        .NUM_BANKS             (NUM_BANKS),
        .ROW_WIDTH             (ROW_WIDTH),
        .COL_WIDTH             (COL_WIDTH),
        .BYTE_OFFSET_WIDTH     (BYTE_OFFSET_WIDTH),
        .SYNTH_ROW_MAJOR       (SYNTH_ROW_MAJOR),
        .SYNTH_BANK_INTERLEAVE (SYNTH_BANK_INTERLEAVE),
        .SYNTH_XOR_HASH        (SYNTH_XOR_HASH)
    ) u_addr_mapper_ar (
        .axi_addr_i      (w_ar_push_addr),
        .scheme_active_i (scheme_active_i),
        .xor_seed_i      (xor_seed_i),
        .bg_field_pos_i  (3'd0),
        .rank_o          (w_ar_rank),
        .bank_o          (w_ar_bank),
        .row_o           (w_ar_row),
        .col_o           (w_ar_col)
    );

    //=========================================================================
    // wr_cmd_cam
    //=========================================================================
    logic [WR_CAM_DEPTH-1:0]                       w_wr_snap_valid;
    logic [WR_CAM_DEPTH-1:0][RKW-1:0]              w_wr_snap_rank;
    logic [WR_CAM_DEPTH-1:0][BKW-1:0]              w_wr_snap_bank;
    logic [WR_CAM_DEPTH-1:0][RW-1:0]               w_wr_snap_row;
    logic [WR_CAM_DEPTH-1:0][CW-1:0]               w_wr_snap_col;
    logic [WR_CAM_DEPTH-1:0][BLW-1:0]              w_wr_snap_len;
    logic [WR_CAM_DEPTH-1:0][WPW-1:0]              w_wr_snap_w_buf_ptr;
    logic [WR_CAM_DEPTH-1:0][WPW-1:0]              w_wr_snap_strb_ptr;
    logic [WR_CAM_DEPTH-1:0]                       w_wr_snap_issued;
    logic [WR_CAM_DEPTH-1:0]                       w_wr_snap_b_pending;
    logic [WR_CAM_DEPTH-1:0][IW-1:0]               w_wr_snap_id;

    // Per-write "full-strb" hint, latched from axi_intake's per-burst
    // AND-reduce result when the burst is pushed into the wr CAM.
    logic [WR_CAM_DEPTH-1:0] r_full_strb;
    logic [WSL-1:0]          w_wr_push_slot;
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_full_strb <= '0;
        end else if (w_aw_push_valid && w_aw_push_ready) begin
            r_full_strb[w_wr_push_slot] <= w_aw_push_full_strb;
        end
    end)

    wr_cmd_cam #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH),
        .W_BUF_PTR_WIDTH (W_BUF_PTR_WIDTH)
    ) u_wr_cam (
        .mc_clk                  (mc_clk),
        .mc_rst_n                (mc_rst_n),

        .push_valid_i            (w_aw_push_valid),
        .push_ready_o            (w_aw_push_ready),
        .push_id_i               (w_aw_push_id),
        .push_rank_i             (w_aw_rank),
        .push_bank_i             (w_aw_bank),
        .push_row_i              (w_aw_row),
        .push_col_i              (w_aw_col),
        .push_len_i              (w_aw_push_len),
        .push_w_buf_ptr_i        (w_aw_push_w_buf_ptr),
        .push_strb_ptr_i         (w_aw_push_strb_ptr),
        .push_slot_o             (w_wr_push_slot),

        .q_rank_i                (q_rank_i),
        .q_bank_i                (q_bank_i),
        .q_row_i                 (q_row_i),
        .match_pending_o         (wr_match_pending_o),
        .match_rowhit_o          (wr_match_rowhit_o),

        .issued_we_i             (wr_issued_we_i),
        .issued_slot_i           (wr_issued_slot_i),

        .beat_pull_strb_i        (beat_pull_strb_i),
        .beat_pull_slot_i        (beat_pull_slot_i),
        .beat_pull_ptr_o         (beat_pull_ptr_o),
        .beat_pull_strb_ptr_o    (beat_pull_strb_ptr_o),
        .beat_pull_last_o        (beat_pull_last_o),

        .b_complete_strb_i       (b_complete_strb_i),
        .b_complete_slot_i       (b_complete_slot_i),
        .entry_complete_o        (w_wr_entry_complete),
        .entry_complete_slot_o   (w_wr_entry_complete_slot),
        .entry_complete_id_o     (w_wr_entry_complete_id),

        .snap_valid_o            (w_wr_snap_valid),
        .snap_rank_o             (w_wr_snap_rank),
        .snap_bank_o             (w_wr_snap_bank),
        .snap_row_o              (w_wr_snap_row),
        .snap_col_o              (w_wr_snap_col),
        .snap_len_o              (w_wr_snap_len),
        .snap_w_buf_ptr_o        (w_wr_snap_w_buf_ptr),
        .snap_strb_ptr_o         (w_wr_snap_strb_ptr),
        .snap_issued_o           (w_wr_snap_issued),
        .snap_b_pending_o        (w_wr_snap_b_pending),
        .snap_id_o               (w_wr_snap_id),

        .dbg_occupancy_o         (dbg_wr_cam_occ_o)
    );

    // Expose CAM completion strobes at macro boundary
    assign wr_entry_complete_o      = w_wr_entry_complete;
    assign wr_entry_complete_slot_o = w_wr_entry_complete_slot;
    assign wr_entry_complete_id_o   = w_wr_entry_complete_id;

    //=========================================================================
    // wr2rd_forward — combinational match against the live wr_cmd_cam
    //=========================================================================
    logic        w_rd_push_valid;
    logic        w_rd_push_ready;
    logic [IW-1:0]  w_rd_push_id;
    logic [RKW-1:0] w_rd_push_rank;
    logic [BKW-1:0] w_rd_push_bank;
    logic [RW-1:0]  w_rd_push_row;
    logic [CW-1:0]  w_rd_push_col;
    logic [BLW-1:0] w_rd_push_len;

    wr2rd_forward #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH),
        .W_BUF_PTR_WIDTH (W_BUF_PTR_WIDTH)
    ) u_wr2rd_forward (
        .mc_clk              (mc_clk),
        .mc_rst_n            (mc_rst_n),

        .ar_valid_i          (w_ar_push_valid),
        .ar_ready_o          (w_ar_push_ready),
        .ar_id_i             (w_ar_push_id),
        .ar_rank_i           (w_ar_rank),
        .ar_bank_i           (w_ar_bank),
        .ar_row_i            (w_ar_row),
        .ar_col_i            (w_ar_col),
        .ar_len_i            (w_ar_push_len),

        .cam_valid_i         (w_wr_snap_valid),
        .cam_rank_i          (w_wr_snap_rank),
        .cam_bank_i          (w_wr_snap_bank),
        .cam_row_i           (w_wr_snap_row),
        .cam_col_i           (w_wr_snap_col),
        .cam_len_i           (w_wr_snap_len),
        .cam_w_buf_ptr_i     (w_wr_snap_w_buf_ptr),
        .cam_full_strb_i     (r_full_strb),

        .rd_push_valid_o     (w_rd_push_valid),
        .rd_push_ready_i     (w_rd_push_ready),
        .rd_push_id_o        (w_rd_push_id),
        .rd_push_rank_o      (w_rd_push_rank),
        .rd_push_bank_o      (w_rd_push_bank),
        .rd_push_row_o       (w_rd_push_row),
        .rd_push_col_o       (w_rd_push_col),
        .rd_push_len_o       (w_rd_push_len),

        .fwd_valid_o         (w_fwd_valid),
        .fwd_ready_i         (w_fwd_ready),
        .fwd_id_o            (w_fwd_id),
        .fwd_w_buf_ptr_o     (w_fwd_w_buf_ptr),
        .fwd_len_o           (w_fwd_len),
        .fwd_src_slot_o      (w_fwd_src_slot),

        .dbg_forward_hit_o   (dbg_forward_hit_o),
        .dbg_forward_miss_o  (dbg_forward_miss_o)
    );

    // Snarf-path observability
    assign dbg_fwd_valid_o    = w_fwd_valid;
    assign dbg_fwd_src_slot_o = w_fwd_src_slot;
    assign dbg_fwd_id_o       = w_fwd_id;

    //=========================================================================
    // rd_cmd_cam
    //=========================================================================
    logic [RD_CAM_DEPTH-1:0]                       w_rd_snap_valid;
    logic [RD_CAM_DEPTH-1:0][IW-1:0]               w_rd_snap_id;
    logic [RD_CAM_DEPTH-1:0][RKW-1:0]              w_rd_snap_rank;
    logic [RD_CAM_DEPTH-1:0][BKW-1:0]              w_rd_snap_bank;
    logic [RD_CAM_DEPTH-1:0][RW-1:0]               w_rd_snap_row;
    logic [RD_CAM_DEPTH-1:0][CW-1:0]               w_rd_snap_col;
    logic [RD_CAM_DEPTH-1:0][BLW-1:0]              w_rd_snap_len;
    logic [RD_CAM_DEPTH-1:0]                       w_rd_snap_issued;

    rd_cmd_cam #(
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH)
    ) u_rd_cam (
        .mc_clk                  (mc_clk),
        .mc_rst_n                (mc_rst_n),

        .push_valid_i            (w_rd_push_valid),
        .push_ready_o            (w_rd_push_ready),
        .push_id_i               (w_rd_push_id),
        .push_rank_i             (w_rd_push_rank),
        .push_bank_i             (w_rd_push_bank),
        .push_row_i              (w_rd_push_row),
        .push_col_i              (w_rd_push_col),
        .push_len_i              (w_rd_push_len),
        .push_slot_o             (),

        .q_rank_i                (q_rank_i),
        .q_bank_i                (q_bank_i),
        .q_row_i                 (q_row_i),
        .match_pending_o         (rd_match_pending_o),
        .match_rowhit_o          (rd_match_rowhit_o),

        .issued_we_i             (rd_issued_we_i),
        .issued_slot_i           (rd_issued_slot_i),

        .beat_we_i               (rd_beat_we_i),
        .beat_slot_i             (rd_beat_slot_i),

        .entry_complete_o        (rd_entry_complete_o),
        .entry_complete_slot_o   (rd_entry_complete_slot_o),
        .entry_complete_id_o     (rd_entry_complete_id_o),

        .snap_valid_o            (w_rd_snap_valid),
        .snap_id_o               (w_rd_snap_id),
        .snap_rank_o             (w_rd_snap_rank),
        .snap_bank_o             (w_rd_snap_bank),
        .snap_row_o              (w_rd_snap_row),
        .snap_col_o              (w_rd_snap_col),
        .snap_len_o              (w_rd_snap_len),
        .snap_issued_o           (w_rd_snap_issued),

        .dbg_occupancy_o         (dbg_rd_cam_occ_o)
    );

    // Expose snapshots at the macro boundary for the scheduler.
    assign wr_snap_rank_o = w_wr_snap_rank;
    assign wr_snap_bank_o = w_wr_snap_bank;
    assign wr_snap_row_o  = w_wr_snap_row;
    assign wr_snap_col_o  = w_wr_snap_col;
    assign wr_snap_len_o  = w_wr_snap_len;
    assign rd_snap_rank_o = w_rd_snap_rank;
    assign rd_snap_bank_o = w_rd_snap_bank;
    assign rd_snap_row_o  = w_rd_snap_row;
    assign rd_snap_col_o  = w_rd_snap_col;
    assign rd_snap_len_o  = w_rd_snap_len;

    // Tie unused snapshot consumers (remaining; not all wired yet).
    wire unused = |{ w_wr_snap_strb_ptr,
                     w_wr_snap_issued, w_wr_snap_b_pending,
                     w_wr_snap_id,
                     w_rd_snap_valid, w_rd_snap_id,
                     w_rd_snap_issued };

endmodule : axi_frontend_macro
