// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_training_layer
// Purpose: Pumice-specific wrapper around the common mc_training_layer shell.
//          Owns the common LPDDR2 training FUBs (mc_lpddr2_zq_ctrl,
//          mc_lpddr2_dq_cal) and maps the generic 2-slot maintenance-command stream onto the
//          scheduler's native {req,grant,op,bank,row,mrr} port.
//
//          Slot 0 = ZQ calibration (highest priority). Slot 1 = LPDDR2 DQ cal.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/uarch/PUMICE_TRAINING_LAYER_UARCH.md
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_training_layer
    import pumice_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int DFI_DATA_WIDTH = 128
) (
    input  logic                      mc_clk,
    input  logic                      mc_rst_n,

    // ----- run-time enable / build guard ------------------------------------
    input  logic                      init_done_i,
    input  memtype_e                  memtype_i,

    // ----- CSR controls -----------------------------------------------------
    input  logic                      zq_en_i,
    input  logic                      zq_defer_en_i,
    input  logic [31:0]               zq_interval_i,
    input  logic [15:0]               t_zqcs_i,
    input  logic [15:0]               t_zqcl_i,
    input  logic [12:0]               zq_overdue_max_i,

    input  logic                      cal_start_i,
    input  logic                      cal_abort_i,
    input  logic [15:0]               t_mrr_i,
    input  logic [15:0]               t_readout_i,

    // ----- maintenance-class command channel to the scheduler ---------------
    output logic                      trn_cmd_req_o,
    input  logic                      trn_cmd_grant_i,
    output dram_op_e                  trn_cmd_op_o,
    output logic [2:0]                trn_cmd_bank_o,
    output logic [17:0]               trn_cmd_row_o,
    output logic                      trn_cmd_mrr_o,

    // ----- DFI-layer calibration sideband (dfi_clk domain) ------------------
    input  logic                      dfi_clk,
    input  logic                      dfi_rstn,
    output logic                      cal_expect_o,   // to rd_aligner
    input  logic [DFI_DATA_WIDTH-1:0] cal_data_i,     // from rd_aligner
    input  logic                      cal_valid_i,

    // ----- telemetry / status -----------------------------------------------
    output logic                      cal_busy_o,
    output logic                      cal_done_o,     // sticky
    output logic                      cal_err_o,      // sticky
    output logic [DFI_DATA_WIDTH-1:0] mrr32_data_o,
    output logic [DFI_DATA_WIDTH-1:0] mrr40_data_o,
    output logic                      zq_busy_o,
    output logic                      zq_overdue_o,
    output logic [15:0]               zqcs_total_o
);

    //=========================================================================
    // Internal nets (declared early for FUB wiring)
    //=========================================================================
    logic        w_zq_req, w_zq_grant;
    dram_op_e    w_zq_op;
    logic [2:0]  w_zq_bank;
    logic [17:0] w_zq_row;

    logic        w_lp_req, w_lp_grant;
    logic [2:0]  w_lp_bank;
    logic [17:0] w_lp_row;
    logic        w_lp_busy, w_lp_done, w_lp_err;
    logic        w_lp_expect;
    logic [DFI_DATA_WIDTH-1:0] w_lp_mrr32_data, w_lp_mrr40_data;
    logic        w_lp_mrr32_valid, w_lp_mrr40_valid;

    // Common-shell slot buses (2 slots, slot 0 highest priority)
    logic [1:0]  w_slot_req;
    logic [1:0]  w_slot_grant;
    dram_op_e [1:0] w_slot_op;
    logic [1:0][2:0]  w_slot_bank;
    logic [1:0][17:0] w_slot_row;
    logic [1:0][0:0]  w_slot_extra;

    // Synchronized calibration data returned from the DFI layer
    logic [DFI_DATA_WIDTH-1:0] w_cal_data_sync;
    logic                      w_cal_valid_sync;

    //=========================================================================
    // Rock-side training FUBs
    //=========================================================================
    mc_lpddr2_zq_ctrl u_zq (
        .mc_clk            (mc_clk),
        .mc_rst_n          (mc_rst_n),
        .zq_en_i           (zq_en_i),
        .init_done_i       (init_done_i),
        .memtype_i         (memtype_i),
        .t_zqcs_interval_i (zq_interval_i),
        .t_zqcs_i          (t_zqcs_i),
        .t_zqcl_i          (t_zqcl_i),
        .zq_defer_en_i     (zq_defer_en_i),
        .overdue_max_i     (zq_overdue_max_i),
        .demand_i          (1'b0),
        .zq_req_o          (w_zq_req),
        .zq_grant_i        (w_zq_grant),
        .zq_op_o           (w_zq_op),
        .zq_bank_o         (w_zq_bank),
        .zq_row_o          (w_zq_row),
        .zq_is_zqcl_o      (),
        .cal_busy_o        (zq_busy_o),
        .obs_zqcs_total_o  (zqcs_total_o),
        .obs_overdue_o     (zq_overdue_o)
    );

    mc_lpddr2_dq_cal #(
        .DFI_DATA_WIDTH(DFI_DATA_WIDTH)
    ) u_lp_cal (
        .mc_clk          (mc_clk),
        .mc_rst_n        (mc_rst_n),
        .cal_start_i     (cal_start_i),
        .cal_abort_i     (cal_abort_i),
        .init_done_i     (init_done_i),
        .memtype_i       (memtype_i),
        .t_mrr_i         (t_mrr_i),
        .t_readout_i     (t_readout_i),
        .cmd_req_o       (w_lp_req),
        .cmd_grant_i     (w_lp_grant),
        .cmd_op_o        (),
        .cmd_bank_o      (w_lp_bank),
        .cmd_row_o       (w_lp_row),
        .cmd_mrr_o       (),
        .cal_expect_o    (w_lp_expect),
        .cal_data_i      (w_cal_data_sync),
        .cal_data_valid_i(w_cal_valid_sync),
        .mrr32_data_o    (w_lp_mrr32_data),
        .mrr40_data_o    (w_lp_mrr40_data),
        .mrr32_valid_o   (w_lp_mrr32_valid),
        .mrr40_valid_o   (w_lp_mrr40_valid),
        .cal_busy_o      (w_lp_busy),
        .cal_done_o      (w_lp_done),
        .cal_err_o       (w_lp_err)
    );

    //=========================================================================
    // Slot assignment: ZQ = slot 0, lp_cal = slot 1.
    // ZQ is periodic maintenance; lp_cal is a firmware-initiated one-shot.
    //=========================================================================
    assign w_slot_req  = {w_lp_req,  w_zq_req};
    assign w_slot_op   = {OP_MRS,    w_zq_op};
    assign w_slot_bank = {w_lp_bank, w_zq_bank};
    assign w_slot_row  = {w_lp_row,  w_zq_row};
    assign w_slot_extra= {1'b1,      1'b0};   // lp_cal drives MRR, ZQ does not

    assign w_zq_grant  = w_slot_grant[0];
    assign w_lp_grant  = w_slot_grant[1];

    //=========================================================================
    // Common training shell
    //=========================================================================
    mc_training_layer #(
        .NUM_SLOTS      (2),
        .BKW            (3),
        .ROW_WIDTH      (18),
        .EXTRA_WIDTH    (1),
        .CAL_DATA_WIDTH (DFI_DATA_WIDTH)
    ) u_shell (
        .mc_clk          (mc_clk),
        .mc_rst_n        (mc_rst_n),
        .slot_req_i      (w_slot_req),
        .slot_grant_o    (w_slot_grant),
        .slot_op_i       (w_slot_op),
        .slot_bank_i     (w_slot_bank),
        .slot_row_i      (w_slot_row),
        .slot_extra_i    (w_slot_extra),
        .trn_cmd_req_o   (trn_cmd_req_o),
        .trn_cmd_grant_i (trn_cmd_grant_i),
        .trn_cmd_op_o    (trn_cmd_op_o),
        .trn_cmd_bank_o  (trn_cmd_bank_o),
        .trn_cmd_row_o   (trn_cmd_row_o),
        .trn_cmd_extra_o (trn_cmd_mrr_o),
        .dfi_clk         (dfi_clk),
        .dfi_rstn        (dfi_rstn),
        .cal_expect_i    (w_lp_expect),
        .cal_expect_o    (cal_expect_o),
        .cal_data_i      (cal_data_i),
        .cal_valid_i     (cal_valid_i),
        .cal_data_o      (w_cal_data_sync),
        .cal_valid_o     (w_cal_valid_sync)
    );

    //=========================================================================
    // Outputs
    //=========================================================================
    assign cal_busy_o    = zq_busy_o || w_lp_busy;
    assign cal_done_o    = w_lp_done;
    assign cal_err_o     = w_lp_err;
    assign mrr32_data_o  = w_lp_mrr32_data;
    assign mrr40_data_o  = w_lp_mrr40_data;

endmodule : pumice_training_layer
