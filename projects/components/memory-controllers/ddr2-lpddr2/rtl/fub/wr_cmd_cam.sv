// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wr_cmd_cam
// Purpose: Write-side content-addressable storage of in-flight write commands.
//
// Description:
//   One slot per in-flight write burst. Holds the DRAM-layer decoded
//   tuple (rank, bank, row, col_start, burst_len) plus per-burst
//   metadata the data path needs (w_buf_ptr, strb_ptr) and a small
//   amount of progress state (beats_issued, b_pending).
//
//   Pure flag-and-counter design; no FSM. Match lines are parallel
//   comparators feeding the scheduler's per-(rank,bank) ready vector.
//
//   Slot index also serves as the AXI ID echo lookup for the
//   wr2rd_forward (write→read snarf path) and the rd_data_path.
//
// Documentation:
//   docs/ddr2_lpddr2_mas/ch02_blocks/05_wr_cmd_cam.md
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wr_cmd_cam
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH      = 16,
    parameter int AXI_ID_WIDTH      = 4,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BURST_LEN_WIDTH   = 8,
    parameter int W_BUF_PTR_WIDTH   = 7,

    // Short aliases
    parameter int CD = WR_CAM_DEPTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int RW = ROW_WIDTH,
    parameter int CW = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int SLW = $clog2(CD)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // Push (from axi4_slave / addr_mapper)
    input  logic                 push_valid_i,
    output logic                 push_ready_o,
    input  logic [IW-1:0]        push_id_i,
    input  logic [RKW-1:0]       push_rank_i,
    input  logic [BKW-1:0]       push_bank_i,
    input  logic [RW-1:0]        push_row_i,
    input  logic [CW-1:0]        push_col_i,
    input  logic [BLW-1:0]       push_len_i,         // beats (NOT len-1)
    input  logic [WPW-1:0]       push_w_buf_ptr_i,
    input  logic [WPW-1:0]       push_strb_ptr_i,
    input  logic [3:0]           push_qos_i,         // AXI awqos
    output logic [SLW-1:0]       push_slot_o,        // which slot took it

    // Scheduler query — per-(rank,bank) match vector
    input  logic [RKW-1:0]       q_rank_i,
    input  logic [BKW-1:0]       q_bank_i,
    input  logic [RW-1:0]        q_row_i,
    output logic [CD-1:0]        match_pending_o,    // valid AND not-yet-issued AND (rank,bank) match
    output logic [CD-1:0]        match_rowhit_o,     // match_pending AND row match

    // Scheduler "mark issued" strobe
    input  logic                 issued_we_i,
    input  logic [SLW-1:0]       issued_slot_i,

    // Per-slot beat-pull interface (to wr_data_path)
    input  logic                 beat_pull_strb_i,
    input  logic [SLW-1:0]       beat_pull_slot_i,
    output logic [WPW-1:0]       beat_pull_ptr_o,
    output logic [WPW-1:0]       beat_pull_strb_ptr_o,
    output logic                 beat_pull_last_o,

    // b_complete from xbank_timers → entry-complete
    input  logic                 b_complete_strb_i,
    input  logic [SLW-1:0]       b_complete_slot_i,
    output logic                 entry_complete_o,
    output logic [SLW-1:0]       entry_complete_slot_o,
    output logic [IW-1:0]        entry_complete_id_o,

    // Snapshot to wr2rd_forward (combinational read of all slots)
    output logic [CD-1:0]                       snap_valid_o,
    output logic [CD-1:0][RKW-1:0]              snap_rank_o,
    output logic [CD-1:0][BKW-1:0]              snap_bank_o,
    output logic [CD-1:0][RW-1:0]               snap_row_o,
    output logic [CD-1:0][CW-1:0]               snap_col_o,
    output logic [CD-1:0][BLW-1:0]              snap_len_o,
    output logic [CD-1:0][WPW-1:0]              snap_w_buf_ptr_o,
    output logic [CD-1:0][WPW-1:0]              snap_strb_ptr_o,
    output logic [CD-1:0]                       snap_issued_o,
    output logic [CD-1:0]                       snap_b_pending_o,
    output logic [CD-1:0][3:0]                  snap_qos_o,

    // Slot-to-AXI-ID lookup for completion routing
    output logic [CD-1:0][IW-1:0]               snap_id_o,

    // Telemetry
    output logic [SLW:0]         dbg_occupancy_o
);

    // Per-slot storage (distributed flops)
    logic [CD-1:0]               r_valid;
    logic [CD-1:0][IW-1:0]       r_id;
    logic [CD-1:0][RKW-1:0]      r_rank;
    logic [CD-1:0][BKW-1:0]      r_bank;
    logic [CD-1:0][RW-1:0]       r_row;
    logic [CD-1:0][CW-1:0]       r_col;
    logic [CD-1:0][BLW-1:0]      r_len;
    logic [CD-1:0][BLW-1:0]      r_beats_issued;
    logic [CD-1:0][WPW-1:0]      r_w_buf_ptr;
    logic [CD-1:0][WPW-1:0]      r_strb_ptr;
    logic [CD-1:0][3:0]          r_qos;
    logic [CD-1:0]               r_issued;
    logic [CD-1:0]               r_b_pending;

    // Free-slot priority encoder
    logic [SLW-1:0] w_free_slot;
    logic           w_has_free;
    always_comb begin
        w_free_slot = '0;
        w_has_free  = 1'b0;
        for (int unsigned i = 0; i < CD; i++) begin
            if (!r_valid[i] && !w_has_free) begin
                w_free_slot = SLW'(i);
                w_has_free  = 1'b1;
            end
        end
    end

    assign push_ready_o = w_has_free;
    assign push_slot_o  = w_free_slot;

    // Push and lifecycle
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_valid        <= '0;
            r_issued       <= '0;
            r_b_pending    <= '0;
            r_beats_issued <= '0;
        end else begin
            // Push
            if (push_valid_i && push_ready_o) begin
                r_valid       [w_free_slot] <= 1'b1;
                r_id          [w_free_slot] <= push_id_i;
                r_rank        [w_free_slot] <= push_rank_i;
                r_bank        [w_free_slot] <= push_bank_i;
                r_row         [w_free_slot] <= push_row_i;
                r_col         [w_free_slot] <= push_col_i;
                r_len         [w_free_slot] <= push_len_i;
                r_w_buf_ptr   [w_free_slot] <= push_w_buf_ptr_i;
                r_strb_ptr    [w_free_slot] <= push_strb_ptr_i;
                r_qos         [w_free_slot] <= push_qos_i;
                r_beats_issued[w_free_slot] <= '0;
                r_issued      [w_free_slot] <= 1'b0;
                r_b_pending   [w_free_slot] <= 1'b0;
            end

            // Mark issued
            if (issued_we_i) begin
                r_issued[issued_slot_i] <= 1'b1;
            end

            // Beat pull progresses beats_issued; last beat sets b_pending
            if (beat_pull_strb_i) begin
                r_beats_issued[beat_pull_slot_i]
                    <= r_beats_issued[beat_pull_slot_i] + 1'b1;
                if (beat_pull_last_o) begin
                    r_b_pending[beat_pull_slot_i] <= 1'b1;
                end
            end

            // b_complete clears the slot
            if (b_complete_strb_i) begin
                r_valid    [b_complete_slot_i] <= 1'b0;
                r_issued   [b_complete_slot_i] <= 1'b0;
                r_b_pending[b_complete_slot_i] <= 1'b0;
            end
        end
    end)

    // Beat-pull combinational outputs
    assign beat_pull_ptr_o      = r_w_buf_ptr[beat_pull_slot_i]
                                + WPW'(r_beats_issued[beat_pull_slot_i]);
    assign beat_pull_strb_ptr_o = r_strb_ptr [beat_pull_slot_i]
                                + WPW'(r_beats_issued[beat_pull_slot_i]);
    assign beat_pull_last_o     = (r_beats_issued[beat_pull_slot_i] + 1'b1
                                   == r_len[beat_pull_slot_i]);

    // Scheduler match vectors.
    //
    // `match_pending_o` is the "needs servicing" signal — must be set
    // for every valid+unissued slot. The scheduler's QoS picker scans
    // ALL slots and picks the best one; q_rank/q_bank are not yet
    // driven by the scheduler (they're tied to 0 in this revision),
    // so a (rank, bank) gate here used to hide every non-bank-0 write.
    // The (rank, bank, row) reachability gate moves into
    // `match_rowhit_o` where it's actually intended.
    for (genvar i = 0; i < CD; i++) begin : g_match
        assign match_pending_o[i] = r_valid[i] && !r_issued[i];
        assign match_rowhit_o [i] = match_pending_o[i]
                                 && (r_rank[i] == q_rank_i)
                                 && (r_bank[i] == q_bank_i)
                                 && (r_row [i] == q_row_i);
    end

    // Snapshot outputs
    assign snap_valid_o      = r_valid;
    assign snap_rank_o       = r_rank;
    assign snap_bank_o       = r_bank;
    assign snap_row_o        = r_row;
    assign snap_col_o        = r_col;
    assign snap_len_o        = r_len;
    assign snap_w_buf_ptr_o  = r_w_buf_ptr;
    assign snap_strb_ptr_o   = r_strb_ptr;
    assign snap_issued_o     = r_issued;
    assign snap_b_pending_o  = r_b_pending;
    assign snap_qos_o        = r_qos;
    assign snap_id_o         = r_id;

    // Entry-complete strobe — drives axi4_slave B emit + txn_queue clear
    assign entry_complete_o      = b_complete_strb_i;
    assign entry_complete_slot_o = b_complete_slot_i;
    assign entry_complete_id_o   = r_id[b_complete_slot_i];

    // Telemetry
    always_comb begin
        dbg_occupancy_o = '0;
        for (int unsigned i = 0; i < CD; i++) begin
            if (r_valid[i]) dbg_occupancy_o = dbg_occupancy_o + (SLW+1)'(1);
        end
    end

endmodule : wr_cmd_cam
