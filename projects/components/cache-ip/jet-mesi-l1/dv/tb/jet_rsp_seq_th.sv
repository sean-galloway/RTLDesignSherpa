// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_rsp_seq_th
// Purpose:
//   Test harness wrapper for jet_rsp_seq.  Pure pass-through: every DUT port
//   is exposed at the top under the same name so the cocotb TB drives pins
//   directly, and the J4 parameters forward so -G overrides reach the DUT.
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

module jet_rsp_seq_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int RSP_DEPTH = jet_pkg::RSP_DEPTH,
    parameter int BUS_WIDTH = l1_pkg::AMBER_BUS_WIDTH,
    parameter int SEQ_W     = jet_pkg::SEQ_W
)(
    input  logic                 clk,
    input  logic                 rst_n,

    // Tag alloc (front end)
    input  logic                 tag_req_i,
    output logic                 tag_gnt_o,
    output logic [SEQ_W-1:0]     tag_o,

    // Deposit
    input  logic                 cpl_i,
    input  logic [SEQ_W-1:0]     cpl_tag_i,
    input  logic [BUS_WIDTH-1:0] cpl_data_i,

    // Release (GAXI response channel)
    output logic                 rsp_valid_o,
    output logic [BUS_WIDTH-1:0] rsp_data_o,
    input  logic                 rsp_ready_i
);

    jet_rsp_seq #(
        .RSP_DEPTH (RSP_DEPTH),
        .BUS_WIDTH (BUS_WIDTH),
        .SEQ_W     (SEQ_W)
    ) u_rsp_seq (.*);

endmodule : jet_rsp_seq_th
