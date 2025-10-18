// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_wr_stub
// Purpose: Axi4 Slave Wr Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Generic Slave stub
module axi4_slave_wr_stub
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
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
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Write address channel (AW)
    input  logic [IW-1:0]              s_axi_awid,
    input  logic [AW-1:0]              s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [UW-1:0]              s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              s_axi_wdata,
    input  logic [SW-1:0]              s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [UW-1:0]              s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [UW-1:0]              s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Stub Outputs/Inputs
    // AW interface
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,
    output logic [3:0]                 fub_axi_aw_count,
    output logic [AWSize-1:0]          fub_axi_aw_pkt,

    // W interface
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,
    output logic [WSize-1:0]           fub_axi_w_pkt,

    // B interface
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,
    input  logic [BSize-1:0]           fub_axi_b_pkt

);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AW), .DATA_WIDTH(AWSize)) inst_aw_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_awvalid),
        .wr_ready               (s_axi_awready),
        .wr_data                ({s_axi_awid,s_axi_awaddr,s_axi_awlen,s_axi_awsize,s_axi_awburst,
                                    s_axi_awlock,s_axi_awcache,s_axi_awprot,s_axi_awqos,
                                    s_axi_awregion,s_axi_awuser}),
        .rd_valid               (fub_axi_awvalid),
        .rd_ready               (fub_axi_awready),
        .rd_count               (fub_axi_aw_count),
        .rd_data                (fub_axi_aw_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                 ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_W), .DATA_WIDTH(WSize)) inst_w_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_wvalid),
        .wr_ready               (s_axi_wready),
        .wr_data                ({s_axi_wdata,s_axi_wstrb,s_axi_wlast,s_axi_wuser}),
        .rd_valid               (fub_axi_wvalid),
        .rd_ready               (fub_axi_wready),
        .rd_data                (fub_axi_w_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count               (),
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_B), .DATA_WIDTH(BSize)) inst_b_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_bvalid),
        .wr_ready               (fub_axi_bready),
        .wr_data                (fub_axi_b_pkt),
        .rd_valid               (s_axi_bvalid),
        .rd_ready               (s_axi_bready),
        .rd_data                ({s_axi_bid,s_axi_bresp,s_axi_buser}),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count               (),
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi4_slave_wr_stub
