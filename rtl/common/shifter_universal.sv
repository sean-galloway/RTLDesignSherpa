// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: shifter_universal
// Purpose: Shifter Universal module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module shifter_universal #(
    parameter int WIDTH = 4
) (
    input                    clk,
    input                    rst_n,
    input        [      1:0] select,      // select operation
                                          // 00 = o_pdata = o_pdata (hold)
                                          // 01 = right shift
                                          // 10 = left shift
                                          // 11 = o_pdata = i_pdata (load)
    input        [WIDTH-1:0] i_pdata,     // parallel data in
    input                    i_sdata_lt,  // serial left data in
    input                    i_sdata_rt,  // serial right data in
    output logic [WIDTH-1:0] o_pdata,     // parallel data out
    output logic             o_sdata_lt,  // serial left data out (bit shifted out during left shift)
    output logic             o_sdata_rt   // serial right data out (bit shifted out during right shift)
);

    logic [WIDTH-1:0] w_pdata;
    logic             w_sdata_lt;
    logic             w_sdata_rt;

    // Combinational logic for next state calculation
    always_comb begin
        // Default values - hold current state
        w_pdata = o_pdata;
        w_sdata_lt = 1'b0;  // No bit shifted out by default
        w_sdata_rt = 1'b0;  // No bit shifted out by default

        casez (select)
            2'b00: begin  // Hold (Do nothing)
                w_pdata = o_pdata;
                w_sdata_lt = 1'b0;  // No shift, no output
                w_sdata_rt = 1'b0;  // No shift, no output
            end

            2'b01: begin  // Right Shift
                w_pdata = {i_sdata_rt, o_pdata[WIDTH-1:1]};
                w_sdata_lt = 1'b0;                    // Left output not used in right shift
                w_sdata_rt = o_pdata[0];              // Bit being shifted out to the right
            end

            2'b10: begin  // Left Shift
                w_pdata = {o_pdata[WIDTH-2:0], i_sdata_lt};
                w_sdata_lt = o_pdata[WIDTH-1];        // Bit being shifted out to the left
                w_sdata_rt = 1'b0;                    // Right output not used in left shift
            end

            2'b11: begin  // Parallel Load
                w_pdata = i_pdata;
                w_sdata_lt = 1'b0;  // No shift, no output
                w_sdata_rt = 1'b0;  // No shift, no output
            end

            default: begin  // Handle X cases - hold current value
                w_pdata = o_pdata;
                w_sdata_lt = 1'b0;
                w_sdata_rt = 1'b0;
            end
        endcase
    end

    // Sequential logic - update outputs on clock edge
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            o_pdata    <= '0;
            o_sdata_lt <= 1'b0;
            o_sdata_rt <= 1'b0;
        end else begin
            o_pdata    <= w_pdata;
            o_sdata_lt <= w_sdata_lt;
            o_sdata_rt <= w_sdata_rt;
        end
    )


endmodule : shifter_universal
