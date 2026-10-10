// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_training_layer
// Purpose: Macro-tier training orchestration for LPDDR2. Holds the ZQ
//          calibration controller, the DQ-cal one-shot sequencer, the one-
//          active command mux onto a single maintenance-class channel, and
//          the mc_clk <-> dfi_clk CDC for the read-aligner calibration
//          sideband.
//
//          Run gating (init_done && memtype==LPDDR2) lives inside the two FUBs;
//          this layer is a passive wiring and arbitration shell.
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
    logic        w_zq_req, w_zq_grant, w_zq_busy, w_zq_overdue;
    logic [15:0] w_zq_total;
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

    logic [DFI_DATA_WIDTH-1:0] w_cal_data_sync;
    logic                      w_cal_valid_sync;

    //=========================================================================
    // FUB instances
    //=========================================================================
    pumice_zq_ctrl u_zq (
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
        .demand_i          (1'b0),          // unused in this FUB; layer gates below
        .zq_req_o          (w_zq_req),
        .zq_grant_i        (w_zq_grant),
        .zq_op_o           (w_zq_op),
        .zq_bank_o         (w_zq_bank),
        .zq_row_o          (w_zq_row),
        .zq_is_zqcl_o      (),
        .cal_busy_o        (w_zq_busy),
        .obs_zqcs_total_o  (w_zq_total),
        .obs_overdue_o     (w_zq_overdue)
    );

    pumice_lp_cal #(
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
    // One-active arbitration. Priority: ZQ > lp_cal.
    // ZQ is periodic maintenance; lp_cal is a firmware-initiated one-shot.
    //=========================================================================
    logic w_zq_select;
    assign w_zq_select = w_zq_req;

    assign trn_cmd_req_o = w_zq_select ? w_zq_req
                         :             w_lp_req;
    assign trn_cmd_op_o  = w_zq_select ? w_zq_op  : OP_MRS;
    assign trn_cmd_bank_o= w_zq_select ? w_zq_bank: w_lp_bank;
    assign trn_cmd_row_o = w_zq_select ? w_zq_row : w_lp_row;
    assign trn_cmd_mrr_o = ~w_zq_select;   // ZQ is MRW, lp_cal is MRR

    assign w_zq_grant    = trn_cmd_grant_i && w_zq_select;
    assign w_lp_grant    = trn_cmd_grant_i && !w_zq_select;

    //=========================================================================
    // CDC: mc_clk -> dfi_clk for cal_expect.
    // The pulse arms the read-aligner sideband. Use sync_pulse so a single
    // mc_clk assertion produces a single dfi_clk pulse.
    //=========================================================================
    sync_pulse #(.SYNC_STAGES(3)) u_expect_sync (
        .i_src_clk   (mc_clk),
        .i_src_rst_n (mc_rst_n),
        .i_pulse     (w_lp_expect),
        .i_dst_clk   (dfi_clk),
        .i_dst_rst_n (dfi_rstn),
        .o_pulse     (cal_expect_o)
    );

    //=========================================================================
    // CDC: dfi_clk -> mc_clk for captured calibration data.
    // Data is held stable by the rd_aligner until the next cal_expect arms,
    // so a multi-flop synchronizer is sufficient. Valid is a single pulse
    // delivered by sync_pulse.
    //=========================================================================
    cdc_synchronizer #(.WIDTH(DFI_DATA_WIDTH), .FLOP_COUNT(3)) u_data_sync (
        .clk      (mc_clk),
        .rst_n    (mc_rst_n),
        .async_in (cal_data_i),
        .sync_out (w_cal_data_sync)
    );

    sync_pulse #(.SYNC_STAGES(3)) u_valid_sync (
        .i_src_clk   (dfi_clk),
        .i_src_rst_n (dfi_rstn),
        .i_pulse     (cal_valid_i),
        .i_dst_clk   (mc_clk),
        .i_dst_rst_n (mc_rst_n),
        .o_pulse     (w_cal_valid_sync)
    );

    //=========================================================================
    // Outputs
    //=========================================================================
    assign cal_busy_o    = w_zq_busy || w_lp_busy;
    assign cal_done_o    = w_lp_done;
    assign cal_err_o     = w_lp_err;
    assign mrr32_data_o  = w_lp_mrr32_data;
    assign mrr40_data_o  = w_lp_mrr40_data;
    assign zq_busy_o     = w_zq_busy;
    assign zq_overdue_o  = w_zq_overdue;
    assign zqcs_total_o  = w_zq_total;

endmodule : pumice_training_layer
