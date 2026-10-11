// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scoria_training_layer
// Purpose: Scoria-specific wrapper around the common mc_training_layer shell.
//          Owns the rock-side training FUBs (scoria_zq_ctrl, scoria_wrlvl_ifc).
//          ZQ calibration is the only command-channel source, so it occupies
//          slot 0 of the shell; slot 1 is tied off. Write-leveling owns the
//          DFI training pins directly and does not use the command channel.
//
//          The shell's generic maintenance-command output is unused in scoria;
//          the scheduler keeps its native zq_req_i/zq_grant_o port.
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scoria_training_layer
    import scoria_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
#(
    parameter int NUM_CS = 1,
    parameter int CSW    = (NUM_CS > 1) ? $clog2(NUM_CS) : 1
)(
    input  logic             mc_clk,
    input  logic             mc_rst_n,

    // ----- run-time enable / build guard ------------------------------------
    input  logic             init_done_i,
    input  memtype_e         memtype_i,

    // ----- ZQ calibration CSR controls --------------------------------------
    input  logic             zq_enable_i,
    input  logic [31:0]      zq_interval_i,
    input  logic [15:0]      t_zqcs_i,
    input  logic [1:0]       zq_placement_i,
    input  logic [12:0]      zq_overdue_max_i,

    // ----- ZQ command channel to the scheduler ------------------------------
    output logic             zq_req_o,
    input  logic             zq_grant_i,

    // ----- ZQ telemetry -----------------------------------------------------
    output logic             zq_busy_o,
    output logic [15:0]      zq_total_o,
    output logic [31:0]      zq_interval_cnt_o,
    output logic             zq_overdue_o,

    // ----- write-leveling mode and CSR controls -----------------------------
    input  logic             wrlvl_en_i,
    input  logic             wrlvl_strobe_i,
    input  logic [3:0]       wrlvl_cs_sel_i,
    input  logic [15:0]      t_wldqsen_i,
    input  logic [15:0]      t_wlmrd_i,
    input  logic [15:0]      t_wlmrd_max_i,
    input  logic [15:0]      t_wlo_i,
    input  logic [15:0]      t_wloe_i,

    // ----- DFI training pins (controller -> PHY) ----------------------------
    output logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_o,
    input  logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_i,
    output logic [NUM_CS-1:0] dfi_phy_wrlvl_cs_n_o,
    output logic              dfi_wrlvl_strobe_o,
    input  logic              wrlvl_prime_dq_i,

    // ----- write-leveling telemetry -----------------------------------------
    output logic              wrlvl_result_valid_o,
    output logic              wrlvl_result_o,
    output logic [15:0]       wrlvl_attempts_o,
    output logic [15:0]       wrlvl_flips_o,
    output logic              wrlvl_timeout_o,
    output logic              wrlvl_ever_done_o,
    output logic [2:0]        wrlvl_state_o
);

    //=========================================================================
    // Internal nets
    //=========================================================================
    logic        w_zq_req, w_zq_grant;
    logic [1:0]  w_slot_req;
    logic [1:0]  w_slot_grant;
    dram_op_e [1:0] w_slot_op;
    logic [1:0][2:0]  w_slot_bank;
    logic [1:0][13:0] w_slot_row;
    logic [1:0][0:0]  w_slot_extra;

    //=========================================================================
    // Rock-side training FUBs
    //=========================================================================
    logic w_zq_run;
    assign w_zq_run = zq_enable_i && init_done_i && (memtype_i == MEMTYPE_DDR3);

    scoria_zq_ctrl u_zq (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .enable_i           (w_zq_run),
        .t_zqcs_interval_i  (zq_interval_i),
        .t_zqcs_i           (t_zqcs_i),
        .demand_i           (1'b0),          // scoria_zq_ctrl does not use demand
        .placement_i        (zq_placement_i),
        .overdue_max_i      (zq_overdue_max_i),
        .zq_req_o           (w_zq_req),
        .zq_grant_i         (w_zq_grant),
        .obs_busy_o         (zq_busy_o),
        .obs_zqcs_total_o   (zq_total_o),
        .obs_interval_cnt_o (zq_interval_cnt_o),
        .obs_overdue_o      (zq_overdue_o)
    );

    scoria_wrlvl_ifc #(
        .NUM_CS(NUM_CS),
        .CSW   (CSW)
    ) u_wrlvl (
        .mc_clk                (mc_clk),
        .mc_rst_n              (mc_rst_n),
        .wrlvl_en_i            (wrlvl_en_i),
        .strobe_i              (wrlvl_strobe_i),
        .cs_sel_i              (CSW'(wrlvl_cs_sel_i)),
        .t_wldqsen_i           (t_wldqsen_i),
        .t_wlmrd_i             (t_wlmrd_i),
        .t_wlmrd_max_i         (t_wlmrd_max_i),
        .t_wlo_i               (t_wlo_i),
        .t_wloe_i              (t_wloe_i),
        .dfi_phylvl_req_cs_n_o (dfi_phylvl_req_cs_n_o),
        .dfi_phylvl_ack_cs_n_i (dfi_phylvl_ack_cs_n_i),
        .dfi_phy_wrlvl_cs_n_o  (dfi_phy_wrlvl_cs_n_o),
        .dfi_wrlvl_strobe_o    (dfi_wrlvl_strobe_o),
        .prime_dq_i            (wrlvl_prime_dq_i),
        .result_valid_o        (wrlvl_result_valid_o),
        .result_o              (wrlvl_result_o),
        .obs_attempts_o        (wrlvl_attempts_o),
        .obs_flips_o           (wrlvl_flips_o),
        .obs_timeout_o         (wrlvl_timeout_o),
        .obs_ever_done_o       (wrlvl_ever_done_o),
        .obs_state_o           (wrlvl_state_o)
    );

    //=========================================================================
    // Slot assignment: ZQ = slot 0, slot 1 tied off.
    //=========================================================================
    assign w_slot_req   = {1'b0,      w_zq_req};
    assign w_slot_op    = {OP_NOP,    OP_ZQCS};
    assign w_slot_bank  = '{default: '0};
    assign w_slot_row   = '{default: '0};
    assign w_slot_extra = '{default: '0};

    assign w_zq_grant   = w_slot_grant[0];
    assign zq_req_o     = w_zq_req;

    //=========================================================================
    // Common training shell (generic output unused; cal-data CDC tied off).
    //=========================================================================
    mc_training_shell #(
        .NUM_SLOTS      (2),
        .BKW            (3),
        .ROW_WIDTH      (14),
        .EXTRA_WIDTH    (1),
        .CAL_DATA_WIDTH (1)
    ) u_shell (
        .mc_clk          (mc_clk),
        .mc_rst_n        (mc_rst_n),
        .slot_req_i      (w_slot_req),
        .slot_grant_o    (w_slot_grant),
        .slot_op_i       (w_slot_op),
        .slot_bank_i     (w_slot_bank),
        .slot_row_i      (w_slot_row),
        .slot_extra_i    (w_slot_extra),
        .trn_cmd_req_o   (),
        .trn_cmd_grant_i (zq_grant_i),
        .trn_cmd_op_o    (),
        .trn_cmd_bank_o  (),
        .trn_cmd_row_o   (),
        .trn_cmd_extra_o (),
        .dfi_clk         (mc_clk),
        .dfi_rstn        (mc_rst_n),
        .cal_expect_i    (1'b0),
        .cal_expect_o    (),
        .cal_data_i      ('0),
        .cal_valid_i     (1'b0),
        .cal_data_o      (),
        .cal_valid_o     ()
    );

endmodule : scoria_training_layer
