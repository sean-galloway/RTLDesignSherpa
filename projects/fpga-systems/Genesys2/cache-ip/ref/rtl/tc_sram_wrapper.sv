// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tc_sram_wrapper
// Purpose:
//   House stand-in for CVA6's common/local/util/tc_sram_wrapper.sv (the thin
//   wrapper its sram.sv instantiates around the technology cell tc_sram).
//   Same parameters and ports, plain packed vectors instead of `parameter
//   type` ports: Vivado 2025.1 synthesizes upstream's typed-port wrapper to an
//   EMPTY module with no message (ref cva6 bin 1: 37 unresolved black boxes,
//   "design tc_sram_wrapper has an empty top module" in isolation), while the
//   same cell synthesizes alone. cache-ip common-ip TASK-003.
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module tc_sram_wrapper #(
    parameter int unsigned NumWords     = 32'd1024,
    parameter int unsigned DataWidth    = 32'd128,
    parameter int unsigned ByteWidth    = 32'd8,
    parameter int unsigned NumPorts     = 32'd2,
    parameter int unsigned Latency      = 32'd1,
    parameter              SimInit      = "none",
    parameter bit          PrintSimCfg  = 1'b0,
    parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
    parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth
) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    input  logic [NumPorts-1:0]                  req_i,
    input  logic [NumPorts-1:0]                  we_i,
    input  logic [NumPorts-1:0][AddrWidth-1:0]   addr_i,
    input  logic [NumPorts-1:0][DataWidth-1:0]   wdata_i,
    input  logic [NumPorts-1:0][BeWidth-1:0]     be_i,
    output logic [NumPorts-1:0][DataWidth-1:0]   rdata_o
);
    tc_sram #(
        .NumWords   (NumWords),
        .DataWidth  (DataWidth),
        .ByteWidth  (ByteWidth),
        .NumPorts   (NumPorts),
        .Latency    (Latency),
        .SimInit    (SimInit),
        .PrintSimCfg(PrintSimCfg)
    ) i_tc_sram (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .req_i  (req_i),
        .we_i   (we_i),
        .be_i   (be_i),
        .wdata_i(wdata_i),
        .addr_i (addr_i),
        .rdata_o(rdata_o)
    );
endmodule : tc_sram_wrapper
