// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// FUB testbench top for mc_xddr2_init_sequencer: port-for-port wrapper so
// cocotb drives the DUT directly. Enum ports cross as raw logic (memtype as
// 3-bit code, init_cmd_op as 5-bit code) with the casts here.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_xddr2_init_sequencer_tb_top
    import mc_common_pkg::*;
#(
    parameter int ROW_WIDTH = 14,
    parameter int NUM_BANKS = 8,
    parameter int BKW       = $clog2(NUM_BANKS)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  logic [2:0]           memtype,
    input  logic [15:0]          t_init_wait,
    input  logic [15:0]          t_dll_wait,
    input  logic [7:0]           t_mrd_wait,
    input  logic [7:0]           t_rp_wait,
    input  logic [7:0]           t_rfc_wait,
    input  logic [15:0]          mr0,
    input  logic [15:0]          mr1,
    input  logic [15:0]          mr2,
    input  logic [15:0]          mr3,
    input  logic [7:0]           lp_mr1_op,
    input  logic [7:0]           lp_mr2_op,
    input  logic [7:0]           lp_mr3_op,
    input  logic                 init_restart,
    input  logic                 dfi_init_complete,

    output logic                 dfi_init_start,
    output logic                 init_cmd_valid,
    output logic [4:0]           init_cmd_op,
    output logic [BKW-1:0]       init_cmd_bank,
    output logic [ROW_WIDTH-1:0] init_cmd_row,
    output logic                 mr_seq_we,
    output logic [4:0]           mr_seq_index,
    output logic [15:0]          mr_seq_data,
    output logic                 init_busy,
    output logic                 init_done,
    output logic [4:0]           init_state
);

    mc_xddr2_init_sequencer #(
        .ROW_WIDTH (ROW_WIDTH),
        .NUM_BANKS (NUM_BANKS)
    ) u_dut (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .memtype_i          (memtype_e'(memtype)),
        .t_init_wait_i      (t_init_wait),
        .t_dll_wait_i       (t_dll_wait),
        .t_mrd_wait_i       (t_mrd_wait),
        .t_rp_wait_i        (t_rp_wait),
        .t_rfc_wait_i       (t_rfc_wait),
        .mr0_i              (mr0),
        .mr1_i              (mr1),
        .mr2_i              (mr2),
        .mr3_i              (mr3),
        .lp_mr1_op_i        (lp_mr1_op),
        .lp_mr2_op_i        (lp_mr2_op),
        .lp_mr3_op_i        (lp_mr3_op),
        .init_restart_i     (init_restart),
        .dfi_init_start_o   (dfi_init_start),
        .dfi_init_complete_i(dfi_init_complete),
        .mr_seq_we_o        (mr_seq_we),
        .mr_seq_index_o     (mr_seq_index),
        .mr_seq_data_o      (mr_seq_data),
        .init_cmd_valid_o   (init_cmd_valid),
        .init_cmd_op_o      (init_cmd_op),
        .init_cmd_bank_o    (init_cmd_bank),
        .init_cmd_row_o     (init_cmd_row),
        .zqcl_req_o         (),
        .zqcl_grant_i       (1'b0),
        .init_busy_o        (init_busy),
        .init_done_o        (init_done),
        .init_state_o       (init_state)
    );

endmodule : mc_xddr2_init_sequencer_tb_top
