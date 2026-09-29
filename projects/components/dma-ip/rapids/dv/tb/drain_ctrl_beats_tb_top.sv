// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: drain_ctrl_beats_tb_top
// Purpose: DV wrapper for drain_ctrl_beats. The wr side is a pure valid/ready
//          strobe with no payload, but a GAXI producer BFM must bind at least
//          one payload field, so this wrapper adds one unused 1-bit input for
//          the BFM to drive. Everything else passes straight through. Same
//          reason as alloc_ctrl_beats_tb_top -- see that file.
`timescale 1ns / 1ps
module drain_ctrl_beats_tb_top #(
    parameter int DEPTH            = 512,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter int REGISTERED       = 1,
    parameter int D  = DEPTH,
    parameter int AW = $clog2(D)
) (
    input  logic                axi_aclk,
    input  logic                axi_aresetn,
    input  logic                wr_valid,
    input  logic                wr_pad,        // BFM payload placeholder (unused)
    output logic                wr_ready,
    input  logic                rd_valid,
    input  logic [7:0]          rd_size,
    output logic                rd_ready,
    output logic [AW:0]         data_available,
    output logic                wr_full,
    output logic                wr_almost_full,
    output logic                rd_empty,
    output logic                rd_almost_empty
);
    logic w_unused;
    assign w_unused = wr_pad;

    drain_ctrl_beats #(
        .DEPTH            (DEPTH),
        .ALMOST_WR_MARGIN (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN (ALMOST_RD_MARGIN),
        .REGISTERED       (REGISTERED)
    ) u_dut (
        .axi_aclk        (axi_aclk),
        .axi_aresetn     (axi_aresetn),
        .wr_valid        (wr_valid),
        .wr_ready        (wr_ready),
        .rd_valid        (rd_valid),
        .rd_size         (rd_size),
        .rd_ready        (rd_ready),
        .data_available  (data_available),
        .wr_full         (wr_full),
        .wr_almost_full  (wr_almost_full),
        .rd_empty        (rd_empty),
        .rd_almost_empty (rd_almost_empty)
    );

endmodule : drain_ctrl_beats_tb_top
