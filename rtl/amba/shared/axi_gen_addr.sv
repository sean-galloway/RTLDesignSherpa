// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_gen_addr
// Purpose: Axi Gen Addr module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi_gen_addr
#(
    parameter int AW  = 32,
    parameter int DW  = 32,
    parameter int ODW = 32, // ouptput data width
    parameter int LEN = 8
)(
    input  logic [AW-1:0]  curr_addr,
    input  logic [2:0]     size,
    input  logic [1:0]     burst,
    input  logic [LEN-1:0] len,
    output logic [AW-1:0]  next_addr,
    output logic [AW-1:0]  next_addr_align
);

localparam int ODWBYTES = ODW / 8;

logic [AW-1:0] increment_pre;
logic [AW-1:0] increment;
logic [AW-1:0] wrap_mask;
logic [AW-1:0] aligned_addr;
logic [AW-1:0] wrap_addr;

// Compute clog2(len+1) for WRAP burst wrap-mask calculation.
// Standard AXI WRAP lengths are 2, 4, 8, 16 beats (len=1,3,7,15),
// but we support the full LEN-bit range for generality.
//
// Implementation: find the position of the highest set bit in (len+1)
// using a casez priority mux. The fixed 17-bit vector ensures all
// bit indices are valid; bits above LEN are structurally zero and
// the corresponding arms are optimized away in synthesis.
logic [16:0] len_plus1;
logic [4:0]  len_log2;

assign len_plus1 = 17'({1'b0, len}) + 17'd1;

always_comb begin
    casez (len_plus1)
        17'b1_????_????_????_????: len_log2 = 5'd16;
        17'b0_1???_????_????_????: len_log2 = 5'd15;
        17'b0_01??_????_????_????: len_log2 = 5'd14;
        17'b0_001?_????_????_????: len_log2 = 5'd13;
        17'b0_0001_????_????_????: len_log2 = 5'd12;
        17'b0_0000_1???_????_????: len_log2 = 5'd11;
        17'b0_0000_01??_????_????: len_log2 = 5'd10;
        17'b0_0000_001?_????_????: len_log2 = 5'd9;
        17'b0_0000_0001_????_????: len_log2 = 5'd8;
        17'b0_0000_0000_1???_????: len_log2 = 5'd7;
        17'b0_0000_0000_01??_????: len_log2 = 5'd6;
        17'b0_0000_0000_001?_????: len_log2 = 5'd5;
        17'b0_0000_0000_0001_????: len_log2 = 5'd4;
        17'b0_0000_0000_0000_1???: len_log2 = 5'd3;
        17'b0_0000_0000_0000_01??: len_log2 = 5'd2;
        17'b0_0000_0000_0000_001?: len_log2 = 5'd1;
        17'b0_0000_0000_0000_0001: len_log2 = 5'd0;
        default:                   len_log2 = 5'd0;
    endcase
end

always_comb begin
    // calculate the increment; scale the increment if there is a difference between the two data widths
    increment_pre = (1 << size);
    increment     = increment_pre;
    if (DW != ODW) begin
        if (AW'(increment_pre) > AW'(ODWBYTES))
            increment = AW'(ODWBYTES);
    end

    // Calculate the wrap mask based on size and len
    wrap_mask = (1 << (32'(size) + 32'(len_log2))) - 1;

    // Calculate the aligned address
    aligned_addr = (curr_addr + increment) & ~(increment - 1);

    // Calculate the wrap address
    wrap_addr = (curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask);
end

always_comb begin
    casez (burst)
        2'b00: next_addr = curr_addr;               // FIXED burst
        2'b01: next_addr = curr_addr + increment;   // INCR burst
        2'b10: next_addr = wrap_addr;                 // WRAP burst
        default: next_addr = curr_addr + increment; // Default to INCR burst
    endcase
end

// Calculate the aligned address
wire [AW-1:0] w_alignment_mask = AW'(ODWBYTES) - 1;

assign next_addr_align = next_addr & ~w_alignment_mask;

endmodule : axi_gen_addr
