// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_wb_buffer_th
// Purpose:
//   Test harness wrapper for jet_wb_buffer.  Pure pass-through: every DUT
//   port is exposed at the top under the same name so the cocotb TB drives
//   pins directly, and the J5/geometry parameters forward so -G overrides
//   reach the DUT.
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

module jet_wb_buffer_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    parameter int LINE_W       = AMBER_ADDR_WIDTH - $clog2(AMBER_LINE_BYTES),
    parameter int ADDR_WIDTH   = AMBER_ADDR_WIDTH,
    parameter int LINE_BYTES   = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH    = AMBER_BUS_WIDTH,
    localparam int STRB_W      = BUS_WIDTH / 8,
    localparam int FILL_BEATS  = LINE_BYTES / STRB_W,
    localparam int BEAT_W      = $clog2(FILL_BEATS),
    localparam int LINE_WIDTH  = LINE_BYTES * 8,
    localparam int SLOT_W      = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int OCC_W       = $clog2(VICTIM_DEPTH + 1)
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // Capture
    input  logic                     cap_i,
    input  logic [LINE_W-1:0]        cap_line_i,
    input  logic                     cap_beat_i,
    input  logic [BUS_WIDTH-1:0]     cap_beat_data_i,
    output logic                     cap_gnt_o,
    output logic [SLOT_W-1:0]        cap_slot_o,
    output logic                     wb_full_o,

    // Drain side: l1_victim-shaped head
    output logic                     drain_valid_o,
    output logic [ADDR_WIDTH-1:0]    drain_addr_o,
    output logic [LINE_WIDTH-1:0]    drain_data_o,
    input  logic                     drain_done_i,

    // Snarf
    input  logic [LINE_W-1:0]        sn_line_i,
    output logic                     sn_hit_o,
    output logic [LINE_WIDTH-1:0]    sn_data_o,
    output logic                     sn_bresp_cycle_o,
    input  logic [1:0]               sn_eff_i,

    // Occupancy
    output logic [OCC_W-1:0]         wb_occupancy_o
);

    jet_wb_buffer #(
        .VICTIM_DEPTH (VICTIM_DEPTH),
        .LINE_W       (LINE_W),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .LINE_BYTES   (LINE_BYTES),
        .BUS_WIDTH    (BUS_WIDTH)
    ) u_wb_buffer (.*);

endmodule : jet_wb_buffer_th
