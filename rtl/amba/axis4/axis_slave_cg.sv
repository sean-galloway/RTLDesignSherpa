// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis_slave_cg
// Purpose: Axis Slave Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axis_slave_cg
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,    // Minimum 1 bit for zero-width signals
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI4-Stream Interface (Input Side)
    input  logic [DW-1:0]              s_axis_tdata,
    input  logic [SW-1:0]              s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW_WIDTH-1:0]        s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     s_axis_tdest,
    input  logic [UW_WIDTH-1:0]        s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,

    // Master AXI4-Stream Interface (Output Side to memory or backend)
    output logic [DW-1:0]              fub_axis_tdata,
    output logic [SW-1:0]              fub_axis_tstrb,
    output logic                       fub_axis_tlast,
    output logic [IW_WIDTH-1:0]        fub_axis_tid,
    output logic [DESTW_WIDTH-1:0]     fub_axis_tdest,
    output logic [UW_WIDTH-1:0]        fub_axis_tuser,
    output logic                       fub_axis_tvalid,
    input  logic                       fub_axis_tready,

    // Clock gating status
    output logic                       cg_gating,
    output logic                       cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signal from base module
    logic int_tready;
    logic int_busy;

    // OR all user-side valid signals (following AXI4 pattern)
    assign user_valid = s_axis_tvalid || fub_axis_tready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = fub_axis_tvalid;

    // Force ready signal to 0 when clock gating is active (following AXI4 pattern)
    assign s_axis_tready = cg_gating ? 1'b0 : int_tready;

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    // Instantiate the base AXI4-Stream slave module with gated clock
    axis_slave #(
        .AXIS_DATA_WIDTH      (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH        (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH      (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH      (AXIS_USER_WIDTH),
        .SKID_DEPTH           (SKID_DEPTH)
    ) i_axis_slave (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),

        // Slave AXI4-Stream Interface (Input Side)
        .s_axis_tdata         (s_axis_tdata),
        .s_axis_tstrb         (s_axis_tstrb),
        .s_axis_tlast         (s_axis_tlast),
        .s_axis_tid           (s_axis_tid),
        .s_axis_tdest         (s_axis_tdest),
        .s_axis_tuser         (s_axis_tuser),
        .s_axis_tvalid        (s_axis_tvalid),
        .s_axis_tready        (int_tready),      // Connect to internal signal

        // Master AXI4-Stream Interface (Output Side)
        .fub_axis_tdata       (fub_axis_tdata),
        .fub_axis_tstrb       (fub_axis_tstrb),
        .fub_axis_tlast       (fub_axis_tlast),
        .fub_axis_tid         (fub_axis_tid),
        .fub_axis_tdest       (fub_axis_tdest),
        .fub_axis_tuser       (fub_axis_tuser),
        .fub_axis_tvalid      (fub_axis_tvalid),
        .fub_axis_tready      (fub_axis_tready),

        .busy                 (int_busy)
    );

endmodule : axis_slave_cg
