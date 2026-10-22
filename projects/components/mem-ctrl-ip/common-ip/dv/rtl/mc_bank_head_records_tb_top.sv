// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// FUB testbench top for mc_bank_head_records: cocotb drives a backend's
// per-entry vectors directly and reads the records back as flat per-bank
// fields (one vector per record field), so the Python model needs no struct
// packing knowledge.
`timescale 1ns / 1ps
`include "reset_defs.svh"

module mc_bank_head_records_tb_top
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES = 8,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1
) (
    input  logic                                clk,
    input  logic                                rst_n,
    input  logic [NUM_ENTRIES-1:0]              sch_valid,
    input  logic [NUM_ENTRIES-1:0]              sch_pend,
    input  logic [NUM_ENTRIES*BKW-1:0]          sch_bank,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    sch_row,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    sch_col,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  sch_older,
    input  logic [NUM_ENTRIES-1:0]              sch_age_exceed,
    input  logic [NUM_BANKS-1:0]                bank_row_active,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0]      bank_open_row,

    output logic [NUM_BANKS-1:0]                head_vld,
    output logic [NUM_BANKS*MC_HEAD_ROW_W-1:0]  head_row,
    output logic [NUM_BANKS*MC_HEAD_COL_W-1:0]  head_col,
    output logic [NUM_BANKS*MC_HEAD_SLOT_W-1:0] head_slot,
    output logic [NUM_BANKS-1:0]                head_behind_empty,
    output logic [NUM_BANKS-1:0]                head_behind_same_row,
    output logic [NUM_BANKS-1:0]                head_age_exceed,
    output logic [NUM_BANKS-1:0]                head_hit,
    output logic [NUM_BANKS-1:0]                head2_vld,
    output logic [NUM_BANKS*MC_HEAD_ROW_W-1:0]  head2_row,
    output logic [NUM_BANKS*MC_HEAD_COL_W-1:0]  head2_col,
    output logic [NUM_BANKS*MC_HEAD_SLOT_W-1:0] head2_slot,
    output logic [NUM_BANKS-1:0]                head2_behind_empty,
    output logic [NUM_BANKS-1:0]                head2_behind_same_row,
    output logic [NUM_BANKS-1:0]                head2_age_exceed,
    output logic [NUM_BANKS-1:0]                head2_hit
);

    mc_head_rec_t [NUM_BANKS-1:0] w_head, w_head2;

    mc_bank_head_records #(
        .NUM_ENTRIES (NUM_ENTRIES),
        .NUM_BANKS   (NUM_BANKS),
        .ROW_WIDTH   (ROW_WIDTH),
        .COL_WIDTH   (COL_WIDTH)
    ) u_dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .sch_valid_i      (sch_valid),
        .sch_pend_i       (sch_pend),
        .sch_bank_i       (sch_bank),
        .sch_row_i        (sch_row),
        .sch_col_i        (sch_col),
        .sch_older_i      (sch_older),
        .sch_age_exceed_i (sch_age_exceed),
        .bank_row_active_i(bank_row_active),
        .bank_open_row_i  (bank_open_row),
        .head_o           (w_head),
        .head2_o          (w_head2)
    );

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            head_vld[b]                                       = w_head[b].vld;
            head_row [b*MC_HEAD_ROW_W  +: MC_HEAD_ROW_W]      = w_head[b].row;
            head_col [b*MC_HEAD_COL_W  +: MC_HEAD_COL_W]      = w_head[b].col;
            head_slot[b*MC_HEAD_SLOT_W +: MC_HEAD_SLOT_W]     = w_head[b].slot;
            head_behind_empty[b]                              = w_head[b].behind_empty;
            head_behind_same_row[b]                           = w_head[b].behind_same_row;
            head_age_exceed[b]                                = w_head[b].age_exceed;
            head_hit[b]                                       = w_head[b].hit;
            head2_vld[b]                                      = w_head2[b].vld;
            head2_row [b*MC_HEAD_ROW_W  +: MC_HEAD_ROW_W]     = w_head2[b].row;
            head2_col [b*MC_HEAD_COL_W  +: MC_HEAD_COL_W]     = w_head2[b].col;
            head2_slot[b*MC_HEAD_SLOT_W +: MC_HEAD_SLOT_W]    = w_head2[b].slot;
            head2_behind_empty[b]                             = w_head2[b].behind_empty;
            head2_behind_same_row[b]                          = w_head2[b].behind_same_row;
            head2_age_exceed[b]                               = w_head2[b].age_exceed;
            head2_hit[b]                                      = w_head2[b].hit;
        end
    end

endmodule : mc_bank_head_records_tb_top
