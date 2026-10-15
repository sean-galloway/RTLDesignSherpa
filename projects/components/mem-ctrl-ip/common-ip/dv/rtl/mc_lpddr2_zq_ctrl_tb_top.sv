// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// FUB testbench top for mc_lpddr2_zq_ctrl: port-for-port wrapper so cocotb
// drives the ZQ controller directly (demand included — the policy under test
// is unreachable from mc_training_plane, which ties demand to 0; ISSUE-021).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_lpddr2_zq_ctrl_tb_top
    import mc_common_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  logic        zq_en,
    input  logic        init_done,
    input  logic [2:0]  memtype,
    input  logic [31:0] t_zqcs_interval,
    input  logic [15:0] t_zqcs,
    input  logic [15:0] t_zqcl,
    input  logic        zq_defer_en,
    input  logic [12:0] overdue_max,
    input  logic        demand,

    output logic        zq_req,
    input  logic        zq_grant,
    output logic [4:0]  zq_op,
    output logic [2:0]  zq_bank,
    output logic [17:0] zq_row,
    output logic        zq_is_zqcl,
    output logic        cal_busy,
    output logic [15:0] zqcs_total,
    output logic        obs_overdue
);

    mc_lpddr2_zq_ctrl u_dut (
        .mc_clk            (mc_clk),
        .mc_rst_n          (mc_rst_n),
        .zq_en_i           (zq_en),
        .init_done_i       (init_done),
        .memtype_i         (memtype_e'(memtype)),
        .t_zqcs_interval_i (t_zqcs_interval),
        .t_zqcs_i          (t_zqcs),
        .t_zqcl_i          (t_zqcl),
        .zq_defer_en_i     (zq_defer_en),
        .overdue_max_i     (overdue_max),
        .demand_i          (demand),
        .zq_req_o          (zq_req),
        .zq_grant_i        (zq_grant),
        .zq_op_o           (zq_op),
        .zq_bank_o         (zq_bank),
        .zq_row_o          (zq_row),
        .zq_is_zqcl_o      (zq_is_zqcl),
        .cal_busy_o        (cal_busy),
        .obs_zqcs_total_o  (zqcs_total),
        .obs_overdue_o     (obs_overdue)
    );

endmodule : mc_lpddr2_zq_ctrl_tb_top
