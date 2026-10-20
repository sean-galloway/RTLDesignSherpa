// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_mem_in
// Purpose: Input operand memory with per-line source-coordinate tag
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cell_mem_in #(
    parameter int LINE_W   = 32,
    parameter int COORD_W  = 4,
    parameter int IN_DEPTH = 32
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Write port: driven by the rx demux
    input  logic              wr_valid,
    output logic              wr_ready,
    input  logic [$clog2(IN_DEPTH)-1:0] wr_addr,
    input  logic [LINE_W-1:0]           wr_data,
    input  logic [cell_pkg::COORD_BITS-1:0] wr_src_coord,

    // Read port: driven by the future execution FSM
    input  logic              rd_valid,
    output logic              rd_ready,
    input  logic [$clog2(IN_DEPTH)-1:0] rd_addr,
    output logic [LINE_W-1:0]           rd_data,
    output logic [cell_pkg::COORD_BITS-1:0] rd_src_coord,

    // Occupancy / status
    output logic              o_empty,
    output logic              o_full,
    output logic [$clog2(IN_DEPTH+1)-1:0] o_occupancy
);

    import cell_pkg::*;

    localparam int ADDR_W = $clog2(IN_DEPTH);
    localparam int OCC_W  = $clog2(IN_DEPTH + 1);
    localparam int COORD_BITS_LP = COORD_BITS;

    // -------------------------------------------------------------------------
    // Memory arrays
    // -------------------------------------------------------------------------
    logic [LINE_W-1:0]         mem_data [IN_DEPTH];
    logic [COORD_BITS_LP-1:0]  mem_tag  [IN_DEPTH];

    // -------------------------------------------------------------------------
    // Write port
    // -------------------------------------------------------------------------
    assign wr_ready = !o_full;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
        end else begin
            if (wr_valid && wr_ready) begin
                mem_data[wr_addr] <= wr_data;
                mem_tag[wr_addr]  <= wr_src_coord;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Read port (registered read)
    // -------------------------------------------------------------------------
    assign rd_ready = 1'b1;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_data      <= '0;
            rd_src_coord <= '0;
        end else begin
            if (rd_valid) begin
                rd_data      <= mem_data[rd_addr];
                rd_src_coord <= mem_tag[rd_addr];
            end
        end
    )

    // -------------------------------------------------------------------------
    // Occupancy counter: incremented on writes, decremented on reads.
    // This is a simple line counter, not a FIFO pointer; the rx demux and
    // execution FSM manage addresses independently.
    // -------------------------------------------------------------------------
    logic [OCC_W-1:0] occupancy;
    logic             write_fire;
    logic             read_fire;

    assign write_fire = wr_valid && wr_ready;
    assign read_fire  = rd_valid && rd_ready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            occupancy <= '0;
        end else begin
            case ({write_fire, read_fire})
                2'b10: occupancy <= (occupancy < OCC_W'(IN_DEPTH)) ?
                                     occupancy + 1'b1 : occupancy;
                2'b01: occupancy <= (occupancy > '0) ?
                                     occupancy - 1'b1 : occupancy;
                default: occupancy <= occupancy;
            endcase
        end
    )

    assign o_occupancy = occupancy;
    assign o_empty     = (occupancy == '0);
    assign o_full      = (occupancy == OCC_W'(IN_DEPTH));

endmodule : cell_mem_in
