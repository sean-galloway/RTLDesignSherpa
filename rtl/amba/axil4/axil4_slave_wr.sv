// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_slave_wr
// Purpose: Axil4 Slave Wr module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axil4_slave_wr
#(
    // AXI-Lite parameters
    parameter int AXIL_ADDR_WIDTH    = 32,
    parameter int AXIL_DATA_WIDTH    = 32,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,

    // Derived parameters
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int AWSize   = AW+3,        // addr + prot
    parameter int WSize    = DW+(DW/8),   // data + strb
    parameter int BSize    = 2            // resp only
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

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

    // Status outputs for clock gating
    output logic                       busy
);

    // Internal connections for skid buffers
    logic [3:0]                int_aw_count;
    logic [AWSize-1:0]         int_aw_pkt;
    logic                      int_skid_awvalid;
    logic                      int_skid_awready;

    logic [3:0]                int_w_count;
    logic [WSize-1:0]          int_w_pkt;
    logic                      int_skid_wvalid;
    logic                      int_skid_wready;

    logic [3:0]                int_b_count;
    logic [BSize-1:0]          int_b_pkt;
    logic                      int_skid_bvalid;
    logic                      int_skid_bready;

    // Busy signal indicates activity in the buffers
    assign busy = (int_aw_count > 0) || (int_w_count > 0) || (int_b_count > 0) ||
                    s_axil_awvalid || s_axil_wvalid || fub_bvalid;

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize),
        .INSTANCE_NAME("AXIL_AW_SKID")
    ) i_aw_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axil_awvalid),
        .wr_ready               (s_axil_awready),
        .wr_data                ({s_axil_awaddr, s_axil_awprot}),
        .rd_valid               (int_skid_awvalid),
        .rd_ready               (int_skid_awready),
        .rd_count               (int_aw_count),
        .rd_data                (int_aw_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AW signals from SKID buffer
    assign {fub_awaddr, fub_awprot} = int_aw_pkt;
    assign fub_awvalid = int_skid_awvalid;
    assign int_skid_awready = fub_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize),
        .INSTANCE_NAME("AXIL_W_SKID")
    ) i_w_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axil_wvalid),
        .wr_ready               (s_axil_wready),
        .wr_data                ({s_axil_wdata, s_axil_wstrb}),
        .rd_valid               (int_skid_wvalid),
        .rd_ready               (int_skid_wready),
        .rd_count               (int_w_count),
        .rd_data                (int_w_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack W signals from SKID buffer
    assign {fub_wdata, fub_wstrb} = int_w_pkt;
    assign fub_wvalid = int_skid_wvalid;
    assign int_skid_wready = fub_wready;

    // Instantiate B channel for write response back to master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize),
        .INSTANCE_NAME("AXIL_B_SKID")
    ) i_b_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_bvalid),
        .wr_ready               (fub_bready),
        .wr_data                (fub_bresp),
        .rd_valid               (int_skid_bvalid),
        .rd_ready               (int_skid_bready),
        .rd_count               (int_b_count),
        .rd_data                (s_axil_bresp),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign s_axil_bvalid = int_skid_bvalid;
    assign int_skid_bready = s_axil_bready;

endmodule : axil4_slave_wr
