// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: hpdcache_sram_1rw
// Purpose:
//   The reference rig's implementation of the HPDcache 1RW SRAM macro
//   (vendor/cv-hpdcache keeps these macros technology-specific: a
//   behavioural model under macros/behav and a blackbox under
//   macros/blackbox). Same ports and the same NO_CHANGE semantics as the
//   behavioural model -- a read returns the word a cycle later, a write
//   cycle leaves rdata as it was -- but the array is a flat vector per
//   entry, which Vivado maps to block RAM. Upstream's model types the entry
//   as a two-dimensional packed array; Vivado reports that as a "RAM from
//   Record/Structs" and builds it from registers (ref bin 1: 283,782
//   flip-flops, placer refused). cache-ip common-ip TASK-003.
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module hpdcache_sram_1rw
#(
    parameter int unsigned ADDR_SIZE = 0,
    parameter int unsigned DATA_SIZE = 0,
    parameter int unsigned DEPTH = 2**ADDR_SIZE,
    parameter int unsigned NDATA = 1
)
(
    input  logic                            clk,
    input  logic                            rst_n,
    input  logic                            cs,
    input  logic                            we,
    input  logic [ADDR_SIZE-1:0]            addr,
    input  logic [NDATA-1:0][DATA_SIZE-1:0] wdata,
    output logic [NDATA-1:0][DATA_SIZE-1:0] rdata
);
    localparam int unsigned W = NDATA * DATA_SIZE;

    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused_rst;
    assign w_unused_rst = rst_n;   // block RAM has no reset
    /* verilator lint_on UNUSEDSIGNAL */

    logic [W-1:0] r_mem [DEPTH];
    logic [W-1:0] r_rdata;

    always_ff @(posedge clk) begin
        if (cs) begin
            if (we) r_mem[addr] <= W'(wdata);
            else    r_rdata     <= r_mem[addr];
        end
    end
    assign rdata = r_rdata;
endmodule : hpdcache_sram_1rw
