// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_slave_wr_cg
// Purpose: Axil4 Slave Wr Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axil4_slave_wr_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Width of idle counter

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI-Lite Interface (Input Side)
    // Write address channel (AW)
    input  logic [AW-1:0]              s_axil_awaddr,
    input  logic [2:0]                 s_axil_awprot,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              s_axil_wdata,
    input  logic [DW/8-1:0]            s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,

    // Write response channel (B)
    output logic [1:0]                 s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    // Master AXI-Lite Interface (Output Side to memory or backend)
    // Write address channel (AW)
    output logic [AW-1:0]              fub_awaddr,
    output logic [2:0]                 fub_awprot,
    output logic                       fub_awvalid,
    input  logic                       fub_awready,

    // Write data channel (W)
    output logic [DW-1:0]              fub_wdata,
    output logic [DW/8-1:0]            fub_wstrb,
    output logic                       fub_wvalid,
    input  logic                       fub_wready,

    // Write response channel (B)
    input  logic [1:0]                 fub_bresp,
    input  logic                       fub_bvalid,
    output logic                       fub_bready,

    // Clock gating status
    output logic                       cg_gating,
    output logic                       cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals from base module
    logic int_awready;
    logic int_wready;
    logic int_bready;
    logic int_busy;

    // OR all user-side valid signals (slave receives from AXI, sends to backend)
    assign user_valid = s_axil_awvalid || s_axil_wvalid || s_axil_bready || int_busy;

    // OR all AXI-side valid signals (backend sends, slave sends to AXI)
    assign axi_valid = fub_awvalid || fub_wvalid || fub_bvalid || s_axil_bvalid;

    // Force ready signals to 0 when clock gating is active
    assign s_axil_awready = cg_gating ? 1'b0 : int_awready;
    assign s_axil_wready = cg_gating ? 1'b0 : int_wready;
    assign fub_bready = cg_gating ? 1'b0 : int_bready;

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

    // Instantiate the base AXI-Lite slave write module with gated clock
    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B)
    ) i_axil_slave_wr (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),

        // Slave AXI-Lite Interface (Input Side)
        .s_axil_awaddr        (s_axil_awaddr),
        .s_axil_awprot        (s_axil_awprot),
        .s_axil_awvalid       (s_axil_awvalid),
        .s_axil_awready       (int_awready),     // Connect to internal signal

        .s_axil_wdata         (s_axil_wdata),
        .s_axil_wstrb         (s_axil_wstrb),
        .s_axil_wvalid        (s_axil_wvalid),
        .s_axil_wready        (int_wready),      // Connect to internal signal

        .s_axil_bresp         (s_axil_bresp),
        .s_axil_bvalid        (s_axil_bvalid),
        .s_axil_bready        (s_axil_bready),

        // Master AXI-Lite Interface (Output Side)
        .fub_awaddr           (fub_awaddr),
        .fub_awprot           (fub_awprot),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (fub_awready),

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (fub_wready),

        .fub_bresp            (fub_bresp),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (int_bready),      // Connect to internal signal

        .busy                 (int_busy)
    );

endmodule : axil4_slave_wr_cg
