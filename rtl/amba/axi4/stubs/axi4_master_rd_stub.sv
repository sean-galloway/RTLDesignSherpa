// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd_stub
// Purpose: Axi4 Master Rd Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_master_rd_stub
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

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
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]    m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]  m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]  m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]    m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]  m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]  m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Stub Outputs/Inputs
    // AR interface
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,
    output logic [2:0]                 fub_axi_ar_count,
    input  logic [ARSize-1:0]          fub_axi_ar_pkt,

    // R interface
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,
    output logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize), .INSTANCE_NAME("AR-Phase")) inst_ar_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_arvalid),
        .wr_ready               (fub_axi_arready),
        .wr_data                (fub_axi_ar_pkt),
        .rd_valid               (m_axi_arvalid),
        .rd_ready               (m_axi_arready),
        .rd_data                ({m_axi_arid,m_axi_araddr,m_axi_arlen,m_axi_arsize,m_axi_arburst,
                                    m_axi_arlock,m_axi_arcache,m_axi_arprot,m_axi_arqos,
                                    m_axi_arregion,m_axi_aruser}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                 (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_R), .DATA_WIDTH(RSize), .INSTANCE_NAME("R-Phase")) inst_r_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_rvalid),
        .wr_ready               (m_axi_rready),
        .wr_data                ({m_axi_rid,m_axi_rdata,m_axi_rresp,m_axi_rlast,m_axi_ruser}),
        .rd_valid               (fub_axi_rvalid),
        .rd_ready               (fub_axi_rready),
        .rd_data                (fub_axi_r_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                 (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi4_master_rd_stub
