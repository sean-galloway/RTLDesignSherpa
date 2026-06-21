// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rd_cmd_cam
// Purpose: Read-side content-addressable storage of in-flight read commands.
//
// Description:
//   One slot per in-flight read burst. Holds the DRAM-layer decoded
//   tuple (rank, bank, row, col_start, burst_len) plus per-burst
//   progress (beats_returned, issued). Slot index identifies the
//   burst for rd_data_path's CL-aligned tagging.
//
//   Pure flag-and-counter design; no FSM. Match lines are parallel
//   comparators feeding the scheduler's per-(rank,bank) ready vector.
//
//   No w_buf_ptr / strb_ptr fields (those are write-only). Beat
//   counting is per-slot and clears the entry when the last beat
//   has been returned through the AXI R channel.
//
// Documentation:
//   docs/ddr2_lpddr2_mas/ch02_blocks/04_rd_cmd_cam.md
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rd_cmd_cam
    import ddr2_lpddr2_pkg::*;
#(
    parameter int RD_CAM_DEPTH      = 16,
    parameter int AXI_ID_WIDTH      = 4,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BURST_LEN_WIDTH   = 8,

    parameter int CD  = RD_CAM_DEPTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int SLW = $clog2(CD)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // Push (from axi4_slave / addr_mapper, unless intercepted by wr2rd_forward)
    input  logic                 push_valid_i,
    output logic                 push_ready_o,
    input  logic [IW-1:0]        push_id_i,
    input  logic [RKW-1:0]       push_rank_i,
    input  logic [BKW-1:0]       push_bank_i,
    input  logic [RW-1:0]        push_row_i,
    input  logic [CW-1:0]        push_col_i,
    input  logic [BLW-1:0]       push_len_i,         // beats (NOT len-1)
    output logic [SLW-1:0]       push_slot_o,

    // Scheduler query
    input  logic [RKW-1:0]       q_rank_i,
    input  logic [BKW-1:0]       q_bank_i,
    input  logic [RW-1:0]        q_row_i,
    output logic [CD-1:0]        match_pending_o,
    output logic [CD-1:0]        match_rowhit_o,

    // Scheduler "mark issued" strobe
    input  logic                 issued_we_i,
    input  logic [SLW-1:0]       issued_slot_i,

    // Beat-arrived strobe from rd_data_path (per-slot AXI R beat emitted)
    input  logic                 beat_we_i,
    input  logic [SLW-1:0]       beat_slot_i,

    // Entry complete (last beat) → drives axi4_slave R last + txn_queue clear
    output logic                 entry_complete_o,
    output logic [SLW-1:0]       entry_complete_slot_o,
    output logic [IW-1:0]        entry_complete_id_o,

    // Snapshot for downstream (slot → id lookup; col/len for issue)
    output logic [CD-1:0]                       snap_valid_o,
    output logic [CD-1:0][IW-1:0]               snap_id_o,
    output logic [CD-1:0][CW-1:0]               snap_col_o,
    output logic [CD-1:0][BLW-1:0]              snap_len_o,
    output logic [CD-1:0]                       snap_issued_o,

    // Telemetry
    output logic [SLW:0]         dbg_occupancy_o
);

    logic [CD-1:0]               r_valid;
    logic [CD-1:0][IW-1:0]       r_id;
    logic [CD-1:0][RKW-1:0]      r_rank;
    logic [CD-1:0][BKW-1:0]      r_bank;
    logic [CD-1:0][RW-1:0]       r_row;
    logic [CD-1:0][CW-1:0]       r_col;
    logic [CD-1:0][BLW-1:0]      r_len;
    logic [CD-1:0][BLW-1:0]      r_beats_returned;
    logic [CD-1:0]               r_issued;

    // Free slot pick
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

    // entry_complete fires when the slot's last beat strobe arrived
    logic w_entry_complete_strb;
    assign w_entry_complete_strb = beat_we_i
                                && (r_beats_returned[beat_slot_i] + 1'b1
                                    == r_len[beat_slot_i]);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_valid          <= '0;
            r_issued         <= '0;
            r_beats_returned <= '0;
        end else begin
            // Push
            if (push_valid_i && push_ready_o) begin
                r_valid         [w_free_slot] <= 1'b1;
                r_id            [w_free_slot] <= push_id_i;
                r_rank          [w_free_slot] <= push_rank_i;
                r_bank          [w_free_slot] <= push_bank_i;
                r_row           [w_free_slot] <= push_row_i;
                r_col           [w_free_slot] <= push_col_i;
                r_len           [w_free_slot] <= push_len_i;
                r_beats_returned[w_free_slot] <= '0;
                r_issued        [w_free_slot] <= 1'b0;
            end

            // Mark issued
            if (issued_we_i) begin
                r_issued[issued_slot_i] <= 1'b1;
            end

            // Beat arrived
            if (beat_we_i) begin
                r_beats_returned[beat_slot_i]
                    <= r_beats_returned[beat_slot_i] + 1'b1;

                if (w_entry_complete_strb) begin
                    r_valid [beat_slot_i] <= 1'b0;
                    r_issued[beat_slot_i] <= 1'b0;
                end
            end
        end
    end)

    // Match vectors
    for (genvar i = 0; i < CD; i++) begin : g_match
        assign match_pending_o[i] = r_valid[i] && !r_issued[i]
                                 && (r_rank[i] == q_rank_i)
                                 && (r_bank[i] == q_bank_i);
        assign match_rowhit_o [i] = match_pending_o[i]
                                 && (r_row[i] == q_row_i);
    end

    // Snapshot
    assign snap_valid_o   = r_valid;
    assign snap_id_o      = r_id;
    assign snap_col_o     = r_col;
    assign snap_len_o     = r_len;
    assign snap_issued_o  = r_issued;

    // Entry complete
    assign entry_complete_o      = w_entry_complete_strb;
    assign entry_complete_slot_o = beat_slot_i;
    assign entry_complete_id_o   = r_id[beat_slot_i];

    // Telemetry
    always_comb begin
        dbg_occupancy_o = '0;
        for (int unsigned i = 0; i < CD; i++) begin
            if (r_valid[i]) dbg_occupancy_o = dbg_occupancy_o + (SLW+1)'(1);
        end
    end

endmodule : rd_cmd_cam
