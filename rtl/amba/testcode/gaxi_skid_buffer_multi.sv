// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_skid_buffer_multi
// Purpose: Gaxi Skid Buffer Multi module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

module gaxi_skid_buffer_multi #(
    parameter integer ADDR_WIDTH = 4,
    parameter integer CTRL_WIDTH = 4,
    parameter integer DATA_WIDTH = 8,
    parameter integer DEPTH = 2,
    parameter integer AW = ADDR_WIDTH,
    parameter integer CW = CTRL_WIDTH,
    parameter integer DW = DATA_WIDTH
)(
    input  logic                axi_aclk,
    input  logic                axi_aresetn,
    // Write channel
    input  logic                wr_valid,
    output logic                wr_ready,
    input  logic [AW-1:0]       wr_addr,
    input  logic [CW-1:0]       wr_ctrl,
    input  logic [DW-1:0]       wr_data0,
    input  logic [DW-1:0]       wr_data1,
    // Read channel
    output logic                rd_valid,
    input  logic                rd_ready,
    output logic [AW-1:0]       rd_addr,
    output logic [CW-1:0]       rd_ctrl,
    output logic [DW-1:0]       rd_data0,
    output logic [DW-1:0]       rd_data1
);

    // Instantiate the original skid buffer
    gaxi_skid_buffer #(.DATA_WIDTH(AW+CW+DW+DW), .DEPTH(DEPTH)) u_gaxi_skid_buffer (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (wr_valid),
        .wr_ready    (wr_ready),
        .wr_data     ({wr_addr, wr_ctrl, wr_data1, wr_data0}),
        .rd_valid    (rd_valid),
        .rd_ready    (rd_ready),
        .rd_data     ({rd_addr, rd_ctrl, rd_data1, rd_data0}),
        .count      (),
        .rd_count    ()
    );

endmodule : gaxi_skid_buffer_multi
