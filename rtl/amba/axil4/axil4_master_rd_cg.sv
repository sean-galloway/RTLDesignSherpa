// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_master_rd_cg
// Purpose: Axil4 Master Rd Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axil4_master_rd_cg
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

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
    // Read address channel (AR)
    input  logic [AW-1:0]              fub_araddr,
    input  logic [2:0]                 fub_arprot,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

    // Master AXI-Lite Interface (Output Side)
    // Read address channel (AR)
    output logic [AW-1:0]              m_axil_araddr,
    output logic [2:0]                 m_axil_arprot,
    output logic                       m_axil_arvalid,
    input  logic                       m_axil_arready,

    // Read data channel (R)
    input  logic [DW-1:0]              m_axil_rdata,
    input  logic [1:0]                 m_axil_rresp,
    input  logic                       m_axil_rvalid,
    output logic                       m_axil_rready,

    // Clock gating status
    output logic                       cg_gating,         // Active gating indicator
    output logic                       cg_idle            // All buffers empty indicator
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals from base module
    logic int_arready;
    logic int_rready;
    logic int_busy;

    // OR all user-side valid signals
    assign user_valid = fub_arvalid || fub_rready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = m_axil_arvalid || m_axil_rvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_arready = cg_gating ? 1'b0 : int_arready;
    assign m_axil_rready = cg_gating ? 1'b0 : int_rready;

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

    // Instantiate the base AXI-Lite master read module with gated clock
    axil4_master_rd #(
        .AXIL_ADDR_WIDTH      (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH      (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR        (SKID_DEPTH_AR),
        .SKID_DEPTH_R         (SKID_DEPTH_R)
    ) i_axil_master_rd (
        .aclk                 (gated_aclk),      // Use gated clock
        .aresetn              (aresetn),

        // Slave AXI-Lite Interface (Input Side)
        .fub_araddr           (fub_araddr),
        .fub_arprot           (fub_arprot),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (int_arready),     // Connect to internal signal

        .fub_rdata            (fub_rdata),
        .fub_rresp            (fub_rresp),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),

        // Master AXI-Lite Interface (Output Side)
        .m_axil_araddr        (m_axil_araddr),
        .m_axil_arprot        (m_axil_arprot),
        .m_axil_arvalid       (m_axil_arvalid),
        .m_axil_arready       (m_axil_arready),

        .m_axil_rdata         (m_axil_rdata),
        .m_axil_rresp         (m_axil_rresp),
        .m_axil_rvalid        (m_axil_rvalid),
        .m_axil_rready        (int_rready),      // Connect to internal signal

        .busy                 (int_busy)
    );

endmodule : axil4_master_rd_cg
