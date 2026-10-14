// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis4_master
// Purpose: HIVE-C AXI4-Stream CDA descriptor master
//          Injects 256-bit RAPIDS DMA descriptors toward the delta fabric.
//          One descriptor = one beat; tuser=PKT_CDA, tdest=RAPIDS virtual tile.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_has/ch04_interfaces/02_packet_formats.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

// HIVE-C AXI4-Stream CDA descriptor master.
//
// Accepts one 256-bit descriptor at a time from descriptor_gen and drives it
// onto the AXIS interface into the hive_c_clk->delta_clk CDC FIFO.  Sidebands
// are constant per the HIVE/Delta contract:
//   tuser[1:0] = 2'b01 (PKT_CDA)
//   tdest      = 8'd16 (RAPIDS virtual tile)
//   tlast      = 1'b1  (single-beat packet)
//
// At most one beat is in flight: s_ready is high only when idle, and once
// m_axis_tvalid is asserted it and tdata remain stable until m_axis_tready.

module hive_axis_cda_master (
    input  logic         clk,
    input  logic         rst_n,

    // Descriptor input (from descriptor_gen queue); one descriptor = one beat
    input  logic [255:0] s_desc,
    input  logic         s_valid,
    output logic         s_ready,

    // CDA AXIS master toward delta (CDC FIFO sits AFTER this module at integration)
    output logic [255:0] m_axis_tdata,
    output logic         m_axis_tvalid,
    input  logic         m_axis_tready,
    output logic [1:0]   m_axis_tuser,   // constant 2'b01 (PKT_CDA)
    output logic [7:0]   m_axis_tdest,   // constant 8'd16 (RAPIDS virtual tile)
    output logic         m_axis_tlast    // constant 1 (single-beat packets)
);

    // Sideband constants per HIVE HAS §4.2 and top-level interface contract.
    localparam logic [1:0] PKT_CDA = 2'b01;
    localparam logic [7:0] RAPIDS_VTILE = 8'd16;

    // One-bit state: 0 = idle, can accept a descriptor; 1 = beat in flight.
    logic r_busy;
    logic [255:0] r_desc;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_busy  <= 1'b0;
            r_desc  <= '0;
        end else begin
            if (!r_busy && s_valid) begin
                // Accept the descriptor and present it on the AXIS interface.
                r_busy <= 1'b1;
                r_desc <= s_desc;
            end else if (r_busy && m_axis_tready) begin
                // Handshake completes; return to idle.
                r_busy <= 1'b0;
            end
        end
    )

    // Outputs
    assign s_ready      = !r_busy;
    assign m_axis_tvalid = r_busy;
    assign m_axis_tdata  = r_desc;
    assign m_axis_tuser  = PKT_CDA;
    assign m_axis_tdest  = RAPIDS_VTILE;
    assign m_axis_tlast  = 1'b1;

endmodule : hive_axis_cda_master
