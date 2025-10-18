// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_master_wr_cg
// Purpose: Axil4 Master Wr Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axil4_master_wr_cg
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
    input  logic                       aclk,
    input  logic                       aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI-Lite Interface (Input Side)
    // Write address channel (AW)
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [2:0]                 fub_awprot,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [1:0]                 fub_bresp,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Master AXI-Lite Interface (Output Side)
    // Write address channel (AW)
    output logic [AW-1:0]              m_axil_awaddr,
    output logic [2:0]                 m_axil_awprot,
    output logic                       m_axil_awvalid,
    input  logic                       m_axil_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axil_wdata,
    output logic [DW/8-1:0]            m_axil_wstrb,
    output logic                       m_axil_wvalid,
    input  logic                       m_axil_wready,

    // Write response channel (B)
    input  logic [1:0]                 m_axil_bresp,
    input  logic                       m_axil_bvalid,
    output logic                       m_axil_bready,

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

    // OR all user-side valid signals
    assign user_valid = fub_awvalid || fub_wvalid || fub_bready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = m_axil_awvalid || m_axil_wvalid || m_axil_bvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_awready = cg_gating ? 1'b0 : int_awready;
    assign fub_wready = cg_gating ? 1'b0 : int_wready;
    assign m_axil_bready = cg_gating ? 1'b0 : int_bready;

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

    // Instantiate the base AXI-Lite master write module with gated clock
    axil4_master_wr #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW        (SKID_DEPTH_AW),
        .SKID_DEPTH_W         (SKID_DEPTH_W),
        .SKID_DEPTH_B         (SKID_DEPTH_B)
    ) i_axil_master_wr (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),

        // Slave AXI-Lite Interface (Input Side)
        .fub_awaddr           (fub_awaddr),
        .fub_awprot           (fub_awprot),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (int_awready),     // Connect to internal signal

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (int_wready),      // Connect to internal signal

        .fub_bresp            (fub_bresp),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Master AXI-Lite Interface (Output Side)
        .m_axil_awaddr        (m_axil_awaddr),
        .m_axil_awprot        (m_axil_awprot),
        .m_axil_awvalid       (m_axil_awvalid),
        .m_axil_awready       (m_axil_awready),

        .m_axil_wdata         (m_axil_wdata),
        .m_axil_wstrb         (m_axil_wstrb),
        .m_axil_wvalid        (m_axil_wvalid),
        .m_axil_wready        (m_axil_wready),

        .m_axil_bresp         (m_axil_bresp),
        .m_axil_bvalid        (m_axil_bvalid),
        .m_axil_bready        (int_bready),      // Connect to internal signal

        .busy                 (int_busy)
    );

endmodule : axil4_master_wr_cg
