// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_cg
// Purpose: Axi4 Master Wr Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_master_wr_cg
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4   // Width of idle counter
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_axi_awid,
    input  logic [AW-1:0]              fub_axi_awaddr,
    input  logic [7:0]                 fub_axi_awlen,
    input  logic [2:0]                 fub_axi_awsize,
    input  logic [1:0]                 fub_axi_awburst,
    input  logic                       fub_axi_awlock,
    input  logic [3:0]                 fub_axi_awcache,
    input  logic [2:0]                 fub_axi_awprot,
    input  logic [3:0]                 fub_axi_awqos,
    input  logic [3:0]                 fub_axi_awregion,
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

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
    assign user_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_awvalid || m_axi_wvalid || m_axi_bvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_axi_awready = cg_gating ? 1'b0 : int_awready;
    assign fub_axi_wready = cg_gating ? 1'b0 : int_wready;
    assign m_axi_bready = cg_gating ? 1'b0 : int_bready;

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

    // Instantiate the base AXI master write module with gated clock
    axi4_master_wr #(
        .AXI_ID_WIDTH             (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH           (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH           (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH           (AXI_USER_WIDTH),
        .SKID_DEPTH_AW            (SKID_DEPTH_AW),
        .SKID_DEPTH_W             (SKID_DEPTH_W),
        .SKID_DEPTH_B             (SKID_DEPTH_B)
    ) i_axi_master_wr (
        .aclk                     (gated_aclk),      // Use gated clock
        .aresetn                  (aresetn),

        // Slave AXI Interface    (Input Side)
        .fub_axi_awid             (fub_axi_awid),
        .fub_axi_awaddr           (fub_axi_awaddr),
        .fub_axi_awlen            (fub_axi_awlen),
        .fub_axi_awsize           (fub_axi_awsize),
        .fub_axi_awburst          (fub_axi_awburst),
        .fub_axi_awlock           (fub_axi_awlock),
        .fub_axi_awcache          (fub_axi_awcache),
        .fub_axi_awprot           (fub_axi_awprot),
        .fub_axi_awqos            (fub_axi_awqos),
        .fub_axi_awregion         (fub_axi_awregion),
        .fub_axi_awuser           (fub_axi_awuser),
        .fub_axi_awvalid          (fub_axi_awvalid),
        .fub_axi_awready          (int_awready),     // Connect to internal signal

        .fub_axi_wdata            (fub_axi_wdata),
        .fub_axi_wstrb            (fub_axi_wstrb),
        .fub_axi_wlast            (fub_axi_wlast),
        .fub_axi_wuser            (fub_axi_wuser),
        .fub_axi_wvalid           (fub_axi_wvalid),
        .fub_axi_wready           (int_wready),      // Connect to internal signal

        .fub_axi_bid              (fub_axi_bid),
        .fub_axi_bresp            (fub_axi_bresp),
        .fub_axi_buser            (fub_axi_buser),
        .fub_axi_bvalid           (fub_axi_bvalid),
        .fub_axi_bready           (fub_axi_bready),

        // Master AXI Interface   (Output Side)
        .m_axi_awid               (m_axi_awid),
        .m_axi_awaddr             (m_axi_awaddr),
        .m_axi_awlen              (m_axi_awlen),
        .m_axi_awsize             (m_axi_awsize),
        .m_axi_awburst            (m_axi_awburst),
        .m_axi_awlock             (m_axi_awlock),
        .m_axi_awcache            (m_axi_awcache),
        .m_axi_awprot             (m_axi_awprot),
        .m_axi_awqos              (m_axi_awqos),
        .m_axi_awregion           (m_axi_awregion),
        .m_axi_awuser             (m_axi_awuser),
        .m_axi_awvalid            (m_axi_awvalid),
        .m_axi_awready            (m_axi_awready),

        .m_axi_wdata              (m_axi_wdata),
        .m_axi_wstrb              (m_axi_wstrb),
        .m_axi_wlast              (m_axi_wlast),
        .m_axi_wuser              (m_axi_wuser),
        .m_axi_wvalid             (m_axi_wvalid),
        .m_axi_wready             (m_axi_wready),

        .m_axi_bid                (m_axi_bid),
        .m_axi_bresp              (m_axi_bresp),
        .m_axi_buser              (m_axi_buser),
        .m_axi_bvalid             (m_axi_bvalid),
        .m_axi_bready             (int_bready),      // Connect to internal signal

        .busy                     (int_busy)
    );

endmodule : axi4_master_wr_cg
