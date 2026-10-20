// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_mem_out
// Purpose: Result memory, write port for FSM, read port for packetizer
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cell_mem_out #(
    parameter int LINE_W    = 32,
    parameter int OUT_DEPTH = 32
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Write port: driven by the future execution FSM
    input  logic              wr_valid,
    output logic              wr_ready,
    input  logic [$clog2(OUT_DEPTH)-1:0] wr_addr,
    input  logic [LINE_W-1:0]            wr_data,

    // Read port: driven by the future packetizer
    input  logic              rd_valid,
    output logic              rd_ready,
    input  logic [$clog2(OUT_DEPTH)-1:0] rd_addr,
    output logic [LINE_W-1:0]            rd_data,

    // Occupancy / status
    output logic              o_empty,
    output logic              o_full,
    output logic [$clog2(OUT_DEPTH+1)-1:0] o_occupancy
);

    localparam int ADDR_W = $clog2(OUT_DEPTH);
    localparam int OCC_W  = $clog2(OUT_DEPTH + 1);

    // -------------------------------------------------------------------------
    // Memory array
    // -------------------------------------------------------------------------
    logic [LINE_W-1:0] mem_data [OUT_DEPTH];

    // -------------------------------------------------------------------------
    // Write port
    // -------------------------------------------------------------------------
    assign wr_ready = !o_full;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
        end else begin
            if (wr_valid && wr_ready) begin
                mem_data[wr_addr] <= wr_data;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Read port (registered read)
    // -------------------------------------------------------------------------
    assign rd_ready = 1'b1;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_data <= '0;
        end else begin
            if (rd_valid) begin
                rd_data <= mem_data[rd_addr];
            end
        end
    )

    // -------------------------------------------------------------------------
    // Occupancy counter
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
                2'b10: occupancy <= (occupancy < OCC_W'(OUT_DEPTH)) ?
                                     occupancy + 1'b1 : occupancy;
                2'b01: occupancy <= (occupancy > '0) ?
                                     occupancy - 1'b1 : occupancy;
                default: occupancy <= occupancy;
            endcase
        end
    )

    assign o_occupancy = occupancy;
    assign o_empty     = (occupancy == '0);
    assign o_full      = (occupancy == OCC_W'(OUT_DEPTH));

endmodule : cell_mem_out
