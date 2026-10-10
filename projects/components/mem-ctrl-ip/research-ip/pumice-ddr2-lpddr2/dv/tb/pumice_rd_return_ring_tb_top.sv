// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_rd_return_ring_tb_top
// Purpose: DV wrapper for pumice_rd_return_ring. The ring's alloc handshake
//          carries no payload INTO the DUT (the DUT hands the ticket OUT), and
//          the GAXI producer BFM must bind at least one payload field, so this
//          wrapper adds one unused 1-bit input for the BFM to drive. Everything
//          else passes straight through.
`timescale 1ns / 1ps
module pumice_rd_return_ring_tb_top #(
    parameter int DEPTH               = 32,
    parameter int AXI_DATA_WIDTH      = 64,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int TW  = $clog2(DEPTH),
    parameter int OCW = $clog2(DEPTH + 1)
) (
    input  logic                aclk,
    input  logic                aresetn,
    input  logic                alloc_valid_i,
    input  logic                alloc_req_i,       // BFM payload placeholder (unused)
    output logic                alloc_ready_o,
    output logic [TW-1:0]       alloc_ticket_o,
    input  logic                issue_valid_i,
    output logic                issue_ready_o,
    input  logic [TW-1:0]       issue_ticket_i,
    input  logic                dfi_ret_valid_i,
    output logic                dfi_ret_ready_o,
    input  logic [DW-1:0]       dfi_ret_data_i,
    input  logic [1:0]          dfi_ret_resp_i,
    input  logic                dfi_ret_last_i,
    output logic                drain_valid_o,
    input  logic                drain_ready_i,
    output logic [DW-1:0]       drain_data_o,
    output logic [1:0]          drain_resp_o,
    output logic                drain_last_o,
    output logic [OCW-1:0]      occ_o,
    output logic                busy_o
);
    logic w_unused;
    assign w_unused = alloc_req_i;

    pumice_rd_return_ring #(
        .DEPTH              (DEPTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_BEATS_PER_BURST(AXI_BEATS_PER_BURST)
    ) u_dut (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .alloc_valid_i   (alloc_valid_i),
        .alloc_ready_o   (alloc_ready_o),
        .alloc_ticket_o  (alloc_ticket_o),
        .issue_valid_i   (issue_valid_i),
        .issue_ready_o   (issue_ready_o),
        .issue_ticket_i  (issue_ticket_i),
        .dfi_ret_valid_i (dfi_ret_valid_i),
        .dfi_ret_ready_o (dfi_ret_ready_o),
        .dfi_ret_data_i  (dfi_ret_data_i),
        .dfi_ret_resp_i  (dfi_ret_resp_i),
        .dfi_ret_last_i  (dfi_ret_last_i),
        .drain_valid_o   (drain_valid_o),
        .drain_ready_i   (drain_ready_i),
        .drain_data_o    (drain_data_o),
        .drain_resp_o    (drain_resp_o),
        .drain_last_o    (drain_last_o),
        .occ_o           (occ_o),
        .busy_o          (busy_o)
    );
endmodule : pumice_rd_return_ring_tb_top
