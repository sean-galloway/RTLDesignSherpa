// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_rd_cg
// Purpose: Axi4 Slave Rd Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_slave_rd_cg
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short params and calculations
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4   // Width of idle counter
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]                s_axi_arid,
    input  logic [AW-1:0]                s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [3:0]                   s_axi_arregion,
    input  logic [UW-1:0]                s_axi_aruser,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,

    // Master AXI Interface (Output Side to memory or backend)
    // Read address channel (AR)
    output logic [IW-1:0]                fub_axi_arid,
    output logic [AW-1:0]                fub_axi_araddr,
    output logic [7:0]                   fub_axi_arlen,
    output logic [2:0]                   fub_axi_arsize,
    output logic [1:0]                   fub_axi_arburst,
    output logic                         fub_axi_arlock,
    output logic [3:0]                   fub_axi_arcache,
    output logic [2:0]                   fub_axi_arprot,
    output logic [3:0]                   fub_axi_arqos,
    output logic [3:0]                   fub_axi_arregion,
    output logic [UW-1:0]                fub_axi_aruser,
    output logic                         fub_axi_arvalid,
    input  logic                         fub_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,

    // Clock gating status
    output logic                         cg_gating,
    output logic                         cg_idle
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

    // OR all user-side valid signals (slave receives from AXI, sends to backend)
    assign user_valid = s_axi_arvalid || s_axi_rready || int_busy;

    // OR all AXI-side valid signals (backend sends, slave sends to AXI)
    assign axi_valid = fub_axi_arvalid || fub_axi_rvalid || s_axi_rvalid;

    // Force ready signals to 0 when clock gating is active
    assign s_axi_arready = cg_gating ? 1'b0 : int_arready;
    assign fub_axi_rready = cg_gating ? 1'b0 : int_rready;

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

    // Instantiate the base AXI slave read module with gated clock
    axi4_slave_rd #(
        .AXI_ID_WIDTH             (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH           (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH           (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH           (AXI_USER_WIDTH),
        .SKID_DEPTH_AR            (SKID_DEPTH_AR),
        .SKID_DEPTH_R             (SKID_DEPTH_R)
    ) i_axi_slave_rd (
        .aclk                     (gated_aclk),      // Use gated clock
        .aresetn                  (aresetn),

        // Slave AXI Interface    (Input Side)
        .s_axi_arid               (s_axi_arid),
        .s_axi_araddr             (s_axi_araddr),
        .s_axi_arlen              (s_axi_arlen),
        .s_axi_arsize             (s_axi_arsize),
        .s_axi_arburst            (s_axi_arburst),
        .s_axi_arlock             (s_axi_arlock),
        .s_axi_arcache            (s_axi_arcache),
        .s_axi_arprot             (s_axi_arprot),
        .s_axi_arqos              (s_axi_arqos),
        .s_axi_arregion           (s_axi_arregion),
        .s_axi_aruser             (s_axi_aruser),
        .s_axi_arvalid            (s_axi_arvalid),
        .s_axi_arready            (int_arready),     // Connect to internal signal

        .s_axi_rid                (s_axi_rid),
        .s_axi_rdata              (s_axi_rdata),
        .s_axi_rresp              (s_axi_rresp),
        .s_axi_rlast              (s_axi_rlast),
        .s_axi_ruser              (s_axi_ruser),
        .s_axi_rvalid             (s_axi_rvalid),
        .s_axi_rready             (s_axi_rready),

        // Master AXI Interface   (Output Side)
        .fub_axi_arid             (fub_axi_arid),
        .fub_axi_araddr           (fub_axi_araddr),
        .fub_axi_arlen            (fub_axi_arlen),
        .fub_axi_arsize           (fub_axi_arsize),
        .fub_axi_arburst          (fub_axi_arburst),
        .fub_axi_arlock           (fub_axi_arlock),
        .fub_axi_arcache          (fub_axi_arcache),
        .fub_axi_arprot           (fub_axi_arprot),
        .fub_axi_arqos            (fub_axi_arqos),
        .fub_axi_arregion         (fub_axi_arregion),
        .fub_axi_aruser           (fub_axi_aruser),
        .fub_axi_arvalid          (fub_axi_arvalid),
        .fub_axi_arready          (fub_axi_arready),

        .fub_axi_rid              (fub_axi_rid),
        .fub_axi_rdata            (fub_axi_rdata),
        .fub_axi_rresp            (fub_axi_rresp),
        .fub_axi_rlast            (fub_axi_rlast),
        .fub_axi_ruser            (fub_axi_ruser),
        .fub_axi_rvalid           (fub_axi_rvalid),
        .fub_axi_rready           (int_rready),      // Connect to internal signal

        .busy                     (int_busy)
    );

endmodule : axi4_slave_rd_cg
