// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Macro testbench top for mc_training_plane: port-for-port wrapper so cocotb
// drives the plane directly. Two clock domains (mc_clk / dfi_clk). Enum ports
// cross as raw logic (memtype 3-bit, trn_cmd_op 5-bit).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_training_plane_tb_top
    import mc_common_pkg::*;
#(
    parameter int ROW_WIDTH      = 18,
    parameter int NUM_BANKS      = 8,
    parameter int CAL_DATA_WIDTH = 128,
    parameter int BKW            = $clog2(NUM_BANKS)
) (
    input  logic                      mc_clk,
    input  logic                      mc_rst_n,
    input  logic                      dfi_clk,
    input  logic                      dfi_rstn,

    input  logic [2:0]                memtype,
    input  logic                      init_done,
    input  logic                      demand,
    input  logic                      zq_en,
    input  logic                      zq_defer_en,
    input  logic [31:0]               zq_interval,
    input  logic [15:0]               t_zqcs,
    input  logic [15:0]               t_zqcl,
    input  logic [12:0]               zq_overdue_max,
    input  logic                      cal_start,
    input  logic                      cal_abort,
    input  logic [15:0]               t_mrr,
    input  logic [15:0]               t_readout,

    output logic                      trn_cmd_req,
    input  logic                      trn_cmd_grant,
    output logic [4:0]                trn_cmd_op,
    output logic [BKW-1:0]            trn_cmd_bank,
    output logic [ROW_WIDTH-1:0]      trn_cmd_row,
    output logic                      trn_cmd_mrr,

    output logic                      cal_expect,
    input  logic [CAL_DATA_WIDTH-1:0] cal_data,
    input  logic                      cal_valid,

    output logic                      cal_busy,
    output logic                      cal_done,
    output logic                      cal_err,
    output logic [CAL_DATA_WIDTH-1:0] mrr32_data,
    output logic [CAL_DATA_WIDTH-1:0] mrr40_data,
    output logic                      zq_busy,
    output logic                      zq_overdue,
    output logic [15:0]               zqcs_total
);

    mc_training_plane #(
        .ROW_WIDTH      (ROW_WIDTH),
        .CAL_DATA_WIDTH (CAL_DATA_WIDTH)
    ) u_dut (
        .mc_clk           (mc_clk),
        .mc_rst_n         (mc_rst_n),
        .init_done_i      (init_done),
        .memtype_i        (memtype_e'(memtype)),
        .demand_i         (demand),
        .zq_en_i          (zq_en),
        .zq_defer_en_i    (zq_defer_en),
        .zq_interval_i    (zq_interval),
        .t_zqcs_i         (t_zqcs),
        .t_zqcl_i         (t_zqcl),
        .zq_overdue_max_i (zq_overdue_max),
        .cal_start_i      (cal_start),
        .cal_abort_i      (cal_abort),
        .t_mrr_i          (t_mrr),
        .t_readout_i      (t_readout),
        .trn_cmd_req_o    (trn_cmd_req),
        .trn_cmd_grant_i  (trn_cmd_grant),
        .trn_cmd_op_o     (trn_cmd_op),
        .trn_cmd_bank_o   (trn_cmd_bank),
        .trn_cmd_row_o    (trn_cmd_row),
        .trn_cmd_mrr_o    (trn_cmd_mrr),
        .dfi_clk          (dfi_clk),
        .dfi_rstn         (dfi_rstn),
        .cal_expect_o     (cal_expect),
        .cal_data_i       (cal_data),
        .cal_valid_i      (cal_valid),
        .cal_busy_o       (cal_busy),
        .cal_done_o       (cal_done),
        .cal_err_o        (cal_err),
        .mrr32_data_o     (mrr32_data),
        .mrr40_data_o     (mrr40_data),
        .zq_busy_o        (zq_busy),
        .zq_overdue_o     (zq_overdue),
        .zqcs_total_o     (zqcs_total)
    );

endmodule : mc_training_plane_tb_top
