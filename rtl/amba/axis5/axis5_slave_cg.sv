// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis5_slave_cg
// Purpose: AXI5-Stream Slave module with clock gating and AMBA5 extensions
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// AXIS5 Extensions:
// - TWAKEUP: Wake-up signaling for power management
// - TPARITY: Optional parity for TDATA integrity
// - Clock gating for power savings
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis5_slave_cg
#(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    parameter bit ENABLE_WAKEUP      = 1,
    parameter bit ENABLE_PARITY      = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int PW       = SW,
    parameter int ICW      = CG_IDLE_COUNT_WIDTH,
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    parameter int PW_WIDTH = ENABLE_PARITY ? PW : 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Clock gating configuration
    input  logic                       i_cg_enable,
    input  logic [ICW-1:0]             i_cg_idle_count,

    // Slave AXI5-Stream Interface (Input Side)
    input  logic [DW-1:0]              s_axis_tdata,
    input  logic [SW-1:0]              s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW_WIDTH-1:0]        s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     s_axis_tdest,
    input  logic [UW_WIDTH-1:0]        s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,
    input  logic                       s_axis_twakeup,
    input  logic [PW_WIDTH-1:0]        s_axis_tparity,

    // Master AXI5-Stream Interface (Output Side to backend/FUB)
    output logic [DW-1:0]              fub_axis5_tdata,
    output logic [SW-1:0]              fub_axis5_tstrb,
    output logic                       fub_axis5_tlast,
    output logic [IW_WIDTH-1:0]        fub_axis5_tid,
    output logic [DESTW_WIDTH-1:0]     fub_axis5_tdest,
    output logic [UW_WIDTH-1:0]        fub_axis5_tuser,
    output logic                       fub_axis5_tvalid,
    input  logic                       fub_axis5_tready,
    output logic                       fub_axis5_twakeup,
    output logic [PW_WIDTH-1:0]        fub_axis5_tparity,

    // Status outputs
    output logic                       busy,
    output logic                       parity_error,
    output logic                       axis_clock_gating
);

    // Internal gated clock
    logic gated_clk;
    logic r_wakeup;

    // Internal busy signal from core
    logic core_busy;

    // Wakeup logic - keep clock active when:
    // 1. Input has valid data
    // 2. Core is busy
    // 3. Backend has pending data
    // 4. Wakeup signal is asserted
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn)
            r_wakeup <= 1'b1;
        else
            r_wakeup <= s_axis_tvalid || core_busy || fub_axis5_tvalid || s_axis_twakeup;
    )

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) u_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (i_cg_enable),
        .cfg_cg_idle_count   (i_cg_idle_count),
        .user_valid          (r_wakeup),
        .axi_valid           (1'b0),
        .clk_out             (gated_clk),
        .gating              (axis_clock_gating),
        /* verilator lint_off PINCONNECTEMPTY */
        .idle                ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Core AXIS5 slave instance
    axis5_slave #(
        .SKID_DEPTH       (SKID_DEPTH),
        .AXIS_DATA_WIDTH  (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH    (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH  (AXIS_USER_WIDTH),
        .ENABLE_WAKEUP    (ENABLE_WAKEUP),
        .ENABLE_PARITY    (ENABLE_PARITY)
    ) u_axis5_slave (
        .aclk              (gated_clk),
        .aresetn           (aresetn),

        .s_axis_tdata      (s_axis_tdata),
        .s_axis_tstrb      (s_axis_tstrb),
        .s_axis_tlast      (s_axis_tlast),
        .s_axis_tid        (s_axis_tid),
        .s_axis_tdest      (s_axis_tdest),
        .s_axis_tuser      (s_axis_tuser),
        .s_axis_tvalid     (s_axis_tvalid),
        .s_axis_tready     (s_axis_tready),
        .s_axis_twakeup    (s_axis_twakeup),
        .s_axis_tparity    (s_axis_tparity),

        .fub_axis_tdata    (fub_axis5_tdata),
        .fub_axis_tstrb    (fub_axis5_tstrb),
        .fub_axis_tlast    (fub_axis5_tlast),
        .fub_axis_tid      (fub_axis5_tid),
        .fub_axis_tdest    (fub_axis5_tdest),
        .fub_axis_tuser    (fub_axis5_tuser),
        .fub_axis_tvalid   (fub_axis5_tvalid),
        .fub_axis_tready   (fub_axis5_tready),
        .fub_axis_twakeup  (fub_axis5_twakeup),
        .fub_axis_tparity  (fub_axis5_tparity),

        .busy              (core_busy),
        .parity_error      (parity_error)
    );

    assign busy = core_busy;

endmodule : axis5_slave_cg
