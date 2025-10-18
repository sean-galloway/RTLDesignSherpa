// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_rd_stub
// Purpose: Axi4 Slave Rd Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
//`include "axi_params.svh"

// Generic Slave stub
module axi4_slave_rd_stub
#(
    parameter int SKID_DEPTH_AR          = 2,
    parameter int SKID_DEPTH_R           = 4,

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
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Read address channel (AR)
    input  logic [IW-1:0]              s_axi_arid,
    input  logic [AW-1:0]              s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [UW-1:0]              s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              s_axi_rid,
    output logic [DW-1:0]              s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [UW-1:0]              s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Stub Outputs/Inputs
    // AR interface
    output logic                       fub_axi_arvalid,
    input  logic                       fub_axi_arready,
    output logic [3:0]                 fub_axi_ar_count,
    output logic [ARSize-1:0]          fub_axi_ar_pkt,

    // R interface
    input  logic                       fub_axi_rvalid,
    output logic                       fub_axi_rready,
    input  logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize)) inst_ar_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_arvalid),
        .wr_ready               (s_axi_arready),
        .wr_data                ({s_axi_arid,s_axi_araddr,s_axi_arlen,s_axi_arsize,s_axi_arburst,
                                    s_axi_arlock,s_axi_arcache,s_axi_arprot,s_axi_arqos,
                                    s_axi_arregion,s_axi_aruser}),
        .rd_valid               (fub_axi_arvalid),
        .rd_ready               (fub_axi_arready),
        .rd_count               (fub_axi_ar_count),
        .rd_data                (fub_axi_ar_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_R), .DATA_WIDTH(RSize)) inst_r_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_rvalid),
        .wr_ready               (fub_axi_rready),
        .wr_data                (fub_axi_r_pkt),
        .rd_valid               (s_axi_rvalid),
        .rd_ready               (s_axi_rready),
        .rd_data                ({s_axi_rid,s_axi_rdata,s_axi_rresp,s_axi_rlast,s_axi_ruser}),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count               (),
        .count                 ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi4_slave_rd_stub
