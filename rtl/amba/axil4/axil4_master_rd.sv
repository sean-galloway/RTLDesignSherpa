// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_master_rd
// Purpose: Axil4 Master Rd module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axil4_master_rd
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int ARSize   = AW+3,  // addr + prot
    parameter int RSize    = DW+2   // data + resp
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

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
                fub_arvalid || m_axil_rvalid;

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize),
        .INSTANCE_NAME("AXIL_AR_SKID")
    ) ar_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_arvalid),
        .wr_ready               (fub_arready),
        .wr_data                ({fub_araddr, fub_arprot}),
        .rd_valid               (int_skid_arvalid),
        .rd_ready               (int_skid_arready),
        .rd_count               (int_ar_count),
        .rd_data                (int_ar_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AR signals from SKID buffer
    assign {m_axil_araddr, m_axil_arprot} = int_ar_pkt;
    assign m_axil_arvalid = int_skid_arvalid;
    assign int_skid_arready = m_axil_arready;

    // Instantiate R channel for read data back
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize),
        .INSTANCE_NAME("AXIL_R_SKID")
    ) r_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axil_rvalid),
        .wr_ready               (m_axil_rready),
        .wr_data                ({m_axil_rdata, m_axil_rresp}),
        .rd_valid               (int_skid_rvalid),
        .rd_ready               (int_skid_rready),
        .rd_count               (int_r_count),
        .rd_data                ({fub_rdata, fub_rresp}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_rvalid = int_skid_rvalid;
    assign int_skid_rready = fub_rready;

endmodule : axil4_master_rd
