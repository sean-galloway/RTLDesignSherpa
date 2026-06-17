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
//   Wraps:
//     - addr_mapper_fub  (×2 — one for AW, one for AR; both combinational)
//     - wr_cmd_cam_fub
//     - rd_cmd_cam_fub
//     - wr2rd_forward_fub
//
//   AW path:  aw_addr → addr_mapper_aw → wr_cmd_cam.push
//   AR path:  ar_addr → addr_mapper_ar → wr2rd_forward
//                                          ├── fwd_*    (snarf hit)
//                                          └── rd_cmd_cam.push (miss)
//
//   The macro is the testable unit for the AXI-ingress side of the
//   controller. It does NOT include the AXI4 slave protocol engine
//   (axi4_slave_fub) — TBs drive the post-AXI decoded interface
//   directly. When axi4_slave_fub lands, it will sit above this macro.
//
// Documentation:
//   docs/ddr2_lpddr2_mas/ch01_overview/01_architecture.md (datapath)
//   docs/ddr2_lpddr2_mas/ch02_blocks/03_addr_mapper.md
//   docs/ddr2_lpddr2_mas/ch02_blocks/04_rd_cmd_cam.md
//   docs/ddr2_lpddr2_mas/ch02_blocks/05_wr_cmd_cam.md
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_frontend_macro
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int AXI_ID_WIDTH         = 4,
    parameter int NUM_RANKS            = 1,
    parameter int NUM_BANKS            = 8,
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BURST_LEN_WIDTH      = 8,
    parameter int W_BUF_PTR_WIDTH      = 7,
    parameter int BYTE_OFFSET_WIDTH    = 3,
    parameter int WR_CAM_DEPTH         = 16,
    parameter int RD_CAM_DEPTH         = 16,
    parameter bit SYNTH_ROW_MAJOR       = 1'b1,
    parameter bit SYNTH_BANK_INTERLEAVE = 1'b1,
    parameter bit SYNTH_XOR_HASH        = 1'b0,

    // Aliases
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // CSR (live)
    input  addr_map_scheme_e     scheme_active_i,
    input  logic [7:0]           xor_seed_i,

    //=========================================================================
    // AW intake (decoded address mapping done inside)
    //=========================================================================
    input  logic                 aw_valid_i,
    output logic                 aw_ready_o,
    input  logic [AW-1:0]        aw_addr_i,
    input  logic [IW-1:0]        aw_id_i,
    input  logic [BLW-1:0]       aw_len_i,           // beats
    input  logic [WPW-1:0]       aw_w_buf_ptr_i,     // allocated externally
    input  logic [WPW-1:0]       aw_strb_ptr_i,
    input  logic                 aw_full_strb_i,     // 1 = no partial-byte writes
    output logic [WSL-1:0]       aw_slot_o,

    //=========================================================================
    // AR intake (decoded inside; routed to forward OR rd CAM)
    //=========================================================================
    input  logic                 ar_valid_i,
    output logic                 ar_ready_o,
    input  logic [AW-1:0]        ar_addr_i,
    input  logic [IW-1:0]        ar_id_i,
    input  logic [BLW-1:0]       ar_len_i,           // beats

    // Forwarded read path output (when AR matched a pending write)
    output logic                 fwd_valid_o,
    input  logic                 fwd_ready_i,
    output logic [IW-1:0]        fwd_id_o,
    output logic [WPW-1:0]       fwd_w_buf_ptr_o,
    output logic [BLW-1:0]       fwd_len_o,
    output logic [WSL-1:0]       fwd_src_slot_o,

    // Direct rd-CAM slot exposed for verification
    output logic [RSL-1:0]       rd_slot_o,

    //=========================================================================
    // Scheduler query (per-(rank,bank), with row for row-hit check)
    //=========================================================================
    input  logic [RKW-1:0]                  q_rank_i,
    input  logic [BKW-1:0]                  q_bank_i,
    input  logic [RW-1:0]                   q_row_i,
    output logic [WR_CAM_DEPTH-1:0]         wr_match_pending_o,
    output logic [WR_CAM_DEPTH-1:0]         wr_match_rowhit_o,
    output logic [RD_CAM_DEPTH-1:0]         rd_match_pending_o,
    output logic [RD_CAM_DEPTH-1:0]         rd_match_rowhit_o,

    //=========================================================================
    // Scheduler "mark issued" strobes
    //=========================================================================
    input  logic                 wr_issued_we_i,
    input  logic [WSL-1:0]       wr_issued_slot_i,
    input  logic                 rd_issued_we_i,
    input  logic [RSL-1:0]       rd_issued_slot_i,

    //=========================================================================
    // Write data-path beat pull (to wr CAM)
    //=========================================================================
    input  logic                 beat_pull_strb_i,
    input  logic [WSL-1:0]       beat_pull_slot_i,
    output logic [WPW-1:0]       beat_pull_ptr_o,
    output logic [WPW-1:0]       beat_pull_strb_ptr_o,
    output logic                 beat_pull_last_o,

    //=========================================================================
    // Write completion (b_complete from xbank_timers)
    //=========================================================================
    input  logic                 b_complete_strb_i,
    input  logic [WSL-1:0]       b_complete_slot_i,
    output logic                 wr_entry_complete_o,
    output logic [WSL-1:0]       wr_entry_complete_slot_o,
    output logic [IW-1:0]        wr_entry_complete_id_o,

    //=========================================================================
    // Read beat arrival (from rd_data_path)
    //=========================================================================
    input  logic                 rd_beat_we_i,
    input  logic [RSL-1:0]       rd_beat_slot_i,
    output logic                 rd_entry_complete_o,
    output logic [RSL-1:0]       rd_entry_complete_slot_o,
    output logic [IW-1:0]        rd_entry_complete_id_o,

    //=========================================================================
    // Telemetry / debug
    //=========================================================================
    output logic [WSL:0]         dbg_wr_cam_occ_o,
    output logic [RSL:0]         dbg_rd_cam_occ_o,
    output logic                 dbg_forward_hit_o,
    output logic                 dbg_forward_miss_o
);

    //=========================================================================
    // AW-side address mapper
    //=========================================================================
    logic [RKW-1:0] w_aw_rank;
    logic [BKW-1:0] w_aw_bank;
    logic [RW-1:0]  w_aw_row;
    logic [CW-1:0]  w_aw_col;

    addr_mapper_fub #(
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
        .axi_addr_i      (aw_addr_i),
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

    addr_mapper_fub #(
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
        .axi_addr_i      (ar_addr_i),
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

    // Per-write "full-strb" hint, tracked alongside the CAM in the macro
    // (the real axi4_slave_fub will source this from its wstrb buffer)
    logic [WR_CAM_DEPTH-1:0] r_full_strb;
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_full_strb <= '0;
        end else if (aw_valid_i && aw_ready_o) begin
            r_full_strb[aw_slot_o] <= aw_full_strb_i;
        end
    end)

    wr_cmd_cam_fub #(
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

        .push_valid_i            (aw_valid_i),
        .push_ready_o            (aw_ready_o),
        .push_id_i               (aw_id_i),
        .push_rank_i             (w_aw_rank),
        .push_bank_i             (w_aw_bank),
        .push_row_i              (w_aw_row),
        .push_col_i              (w_aw_col),
        .push_len_i              (aw_len_i),
        .push_w_buf_ptr_i        (aw_w_buf_ptr_i),
        .push_strb_ptr_i         (aw_strb_ptr_i),
        .push_slot_o             (aw_slot_o),

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
        .entry_complete_o        (wr_entry_complete_o),
        .entry_complete_slot_o   (wr_entry_complete_slot_o),
        .entry_complete_id_o     (wr_entry_complete_id_o),

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

    wr2rd_forward_fub #(
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

        .ar_valid_i          (ar_valid_i),
        .ar_ready_o          (ar_ready_o),
        .ar_id_i             (ar_id_i),
        .ar_rank_i           (w_ar_rank),
        .ar_bank_i           (w_ar_bank),
        .ar_row_i            (w_ar_row),
        .ar_col_i            (w_ar_col),
        .ar_len_i            (ar_len_i),

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

        .fwd_valid_o         (fwd_valid_o),
        .fwd_ready_i         (fwd_ready_i),
        .fwd_id_o            (fwd_id_o),
        .fwd_w_buf_ptr_o     (fwd_w_buf_ptr_o),
        .fwd_len_o           (fwd_len_o),
        .fwd_src_slot_o      (fwd_src_slot_o),

        .dbg_forward_hit_o   (dbg_forward_hit_o),
        .dbg_forward_miss_o  (dbg_forward_miss_o)
    );

    //=========================================================================
    // rd_cmd_cam
    //=========================================================================
    // Read-CAM snapshot — exposed for future scheduler integration
    logic [RD_CAM_DEPTH-1:0]                       w_rd_snap_valid;
    logic [RD_CAM_DEPTH-1:0][IW-1:0]               w_rd_snap_id;
    logic [RD_CAM_DEPTH-1:0][CW-1:0]               w_rd_snap_col;
    logic [RD_CAM_DEPTH-1:0][BLW-1:0]              w_rd_snap_len;
    logic [RD_CAM_DEPTH-1:0]                       w_rd_snap_issued;

    rd_cmd_cam_fub #(
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
        .push_slot_o             (rd_slot_o),

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
        .snap_col_o              (w_rd_snap_col),
        .snap_len_o              (w_rd_snap_len),
        .snap_issued_o           (w_rd_snap_issued),

        .dbg_occupancy_o         (dbg_rd_cam_occ_o)
    );

    // Tie unused snapshot consumers for downstream FUBs (not used at macro level).
    // These will feed the scheduler / rd_data_path / xbank_timers when those land.
    wire unused = |{ w_wr_snap_col,    w_wr_snap_strb_ptr,
                     w_wr_snap_issued, w_wr_snap_b_pending,
                     w_wr_snap_id,
                     w_rd_snap_valid,  w_rd_snap_id,
                     w_rd_snap_col,    w_rd_snap_len,
                     w_rd_snap_issued };

endmodule : axi_frontend_macro
