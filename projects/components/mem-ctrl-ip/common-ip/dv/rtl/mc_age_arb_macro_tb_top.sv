// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// TB top for the aged-fifo + matrix-arbiter macro test
// (common-ip/dv/tests/macro/test_mc_age_arb.py).  Two age fifos (bank A /
// bank B) and one small matrix arbiter, ports exposed flat for the cocotb
// driver.
//
`timescale 1ns / 1ps

module mc_age_arb_macro_tb_top
#(
    parameter int SLOT_W = 3,
    parameter int ROW_W  = 14,
    parameter int COL_W  = 10,
    parameter int ID_W   = 8,
    parameter int AGE_W  = 6,
    parameter int DEPTH  = 8,
    parameter int NARB   = 4
)(
    input  logic aclk,
    input  logic aresetn,

    // fifo A (bank A)
    input  logic              a_push,
    input  logic [SLOT_W-1:0] a_push_slot,
    input  logic [ROW_W-1:0]  a_push_row,
    input  logic [COL_W-1:0]  a_push_col,
    input  logic [ID_W-1:0]   a_push_id,
    input  logic              a_push_last,
    input  logic              a_push_bank_open,
    input  logic [ROW_W-1:0]  a_push_bank_row,
    input  logic              a_push_close_pol,
    output logic              a_full,
    output logic              a_head_vld,
    output logic [SLOT_W-1:0] a_head_slot,
    output logic [ROW_W-1:0]  a_head_row,
    output logic              a_head_act,
    output logic [AGE_W-1:0]  a_head_age,
    output logic              a_head2_vld,
    output logic [AGE_W-1:0]  a_head2_age,
    input  logic              a_pop,

    // fifo B (bank B)
    input  logic              b_push,
    input  logic [SLOT_W-1:0] b_push_slot,
    input  logic [ROW_W-1:0]  b_push_row,
    input  logic              b_push_bank_open,
    input  logic [ROW_W-1:0]  b_push_bank_row,
    output logic              b_head_vld,
    output logic              b_head_act,
    output logic [AGE_W-1:0]  b_head_age,
    input  logic              b_pop,

    // shared decrement strobe (every pick)
    input  logic              decr,

    // matrix arbiter (NARB requesters)
    input  logic [NARB-1:0]   arb_req,
    output logic [NARB-1:0]   arb_gnt,
    input  logic              arb_upd
);

    logic a_empty_unused, a_one_unused, b_empty_unused, b_one_unused, b_full_unused;

    mc_age_fifo #(.SLOT_W(SLOT_W), .ROW_W(ROW_W), .COL_W(COL_W), .ID_W(ID_W),
                  .AGE_W(AGE_W), .DEPTH(DEPTH)) u_fifo_a (
        .aclk(aclk), .aresetn(aresetn),
        .push_i(a_push), .push_slot_i(a_push_slot), .push_row_i(a_push_row),
        .push_col_i(a_push_col), .push_id_i(a_push_id), .push_last_i(a_push_last),
        .push_bank_open_i(a_push_bank_open), .push_bank_row_i(a_push_bank_row),
        .push_close_pol_i(a_push_close_pol), .full_o(a_full),
        .decr_i(decr),
        .head_vld_o(a_head_vld), .head_slot_o(a_head_slot), .head_row_o(a_head_row),
        .head_col_o(), .head_id_o(), .head_last_o(),
        .head_act_o(a_head_act), .head_age_o(a_head_age),
        .head2_vld_o(a_head2_vld), .head2_slot_o(), .head2_row_o(),
        .head2_col_o(), .head2_id_o(), .head2_last_o(),
        .head2_age_o(a_head2_age), .head2_act_o(),
        .pop_i(a_pop), .empty_o(a_empty_unused), .one_o(a_one_unused));

    mc_age_fifo #(.SLOT_W(SLOT_W), .ROW_W(ROW_W), .COL_W(COL_W), .ID_W(ID_W),
                  .AGE_W(AGE_W), .DEPTH(DEPTH)) u_fifo_b (
        .aclk(aclk), .aresetn(aresetn),
        .push_i(b_push), .push_slot_i(b_push_slot), .push_row_i(b_push_row),
        .push_col_i('0), .push_id_i('0), .push_last_i(1'b0),
        .push_bank_open_i(b_push_bank_open), .push_bank_row_i(b_push_bank_row),
        .push_close_pol_i(1'b0), .full_o(b_full_unused),
        .decr_i(decr),
        .head_vld_o(b_head_vld), .head_slot_o(), .head_row_o(),
        .head_col_o(), .head_id_o(), .head_last_o(),
        .head_act_o(b_head_act), .head_age_o(b_head_age),
        .head2_vld_o(), .head2_slot_o(), .head2_row_o(),
        .head2_col_o(), .head2_id_o(), .head2_last_o(),
        .head2_age_o(), .head2_act_o(),
        .pop_i(b_pop), .empty_o(b_empty_unused), .one_o(b_one_unused));

    mc_matrix_arbiter #(.N(NARB)) u_arb (
        .aclk(aclk), .aresetn(aresetn),
        .req_i(arb_req), .gnt_o(arb_gnt), .upd_i(arb_upd));

endmodule : mc_age_arb_macro_tb_top
