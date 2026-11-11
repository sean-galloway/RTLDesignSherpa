// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: hpdcache_sram_wbyteenable_1rw
// Purpose:
//   The reference rig's implementation of the HPDcache 1RW SRAM macro with
//   write byte enables (see hpdcache_sram_1rw.sv for why the vendored
//   behavioural model is not used on the FPGA). Flat entry vector, per-byte
//   write enable, NO_CHANGE read -- the Vivado byte-write block RAM
//   template. cache-ip common-ip TASK-003.
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module hpdcache_sram_wbyteenable_1rw
#(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2**ADDR_SIZE,
    parameter int unsigned NDATA = 1
)
(
    input  logic                              clk,
    input  logic                              rst_n,
    input  logic                              cs,
    input  logic                              we,
    input  logic [ADDR_SIZE-1:0]              addr,
    input  logic [NDATA-1:0][DATA_SIZE-1:0]   wdata,
    input  logic [NDATA-1:0][DATA_SIZE/8-1:0] wbyteenable,
    output logic [NDATA-1:0][DATA_SIZE-1:0]   rdata
);
    localparam int unsigned W  = NDATA * DATA_SIZE;
    localparam int unsigned NB = W / 8;

    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused_rst;
    assign w_unused_rst = rst_n;   // block RAM has no reset
    /* verilator lint_on UNUSEDSIGNAL */

    logic [W-1:0]  w_wdata;
    logic [NB-1:0] w_be;
    assign w_wdata = W'(wdata);
    assign w_be    = NB'(wbyteenable);

    logic [W-1:0] r_mem [DEPTH];
    logic [W-1:0] r_rdata;

    always_ff @(posedge clk) begin
        if (cs) begin
            if (we) begin
                for (int b = 0; b < NB; b++) begin
                    if (w_be[b]) r_mem[addr][b*8 +: 8] <= w_wdata[b*8 +: 8];
                end
            end else begin
                r_rdata <= r_mem[addr];
            end
        end
    end
    assign rdata = r_rdata;
endmodule : hpdcache_sram_wbyteenable_1rw
