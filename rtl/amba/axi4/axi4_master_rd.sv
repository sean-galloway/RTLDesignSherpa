// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd
// Purpose: Axi4 Master Rd module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_master_rd
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

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [3:0]                 fub_axi_arregion,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Status outputs for clock gating
    output logic                       busy
);

    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;

    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;

    // Busy signal indicates activity in the buffers
    assign busy = (int_ar_count > 0) || (int_r_count > 0) ||
                    fub_axi_arvalid || m_axi_rvalid;

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize),
        .INSTANCE_NAME("AR_SKID")
    ) ar_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_arvalid),
        .wr_ready               (fub_axi_arready),
        .wr_data                ({fub_axi_arid, fub_axi_araddr, fub_axi_arlen, fub_axi_arsize,
                                    fub_axi_arburst, fub_axi_arlock, fub_axi_arcache, fub_axi_arprot,
                                    fub_axi_arqos, fub_axi_arregion, fub_axi_aruser}),
        .rd_valid               (int_skid_arvalid),
        .rd_ready               (int_skid_arready),
        .rd_count               (int_ar_count),
        .rd_data                (int_ar_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AR signals from SKID buffer
    assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
            m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
            m_axi_arregion, m_axi_aruser} = int_ar_pkt;
    assign m_axi_arvalid = int_skid_arvalid;
    assign int_skid_arready = m_axi_arready;

    // Instantiate R channel for read data back
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize),
        .INSTANCE_NAME("R_SKID")
    ) r_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_rvalid),
        .wr_ready               (m_axi_rready),
        .wr_data                ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
        .rd_valid               (int_skid_rvalid),
        .rd_ready               (int_skid_rready),
        .rd_count               (int_r_count),
        .rd_data                ({fub_axi_rid, fub_axi_rdata, fub_axi_rresp, fub_axi_rlast, fub_axi_ruser}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_axi_rvalid = int_skid_rvalid;
    assign int_skid_rready = fub_axi_rready;

endmodule : axi4_master_rd
