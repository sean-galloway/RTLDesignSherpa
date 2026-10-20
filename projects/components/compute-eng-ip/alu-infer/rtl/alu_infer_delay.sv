// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_delay
// Purpose: Fixed-depth valid + payload delay line that carries a row's tag
//          and data through its natural latency
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - DEPTH = 0 is a wire.  The line never stalls: every row result has a
//     tag-FIFO entry reserved at issue, so nothing downstream can refuse it.
//   - Registers placed after a combinational row are retiming candidates;
//     the integration flow moves them into the row's logic.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_delay #(
    parameter int W     = 32,
    parameter int DEPTH = 0
) (
    input  logic         clk,
    input  logic         aresetn,
    input  logic         i_valid,
    input  logic [W-1:0] i_data,
    output logic         o_valid,
    output logic [W-1:0] o_data
);

    generate
        if (DEPTH == 0) begin : gen_wire
            assign o_valid = i_valid;
            assign o_data  = i_data;
        end else begin : gen_regs
            logic         r_valid [DEPTH];
            logic [W-1:0] r_data  [DEPTH];

            `ALWAYS_FF_RST(clk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    for (int i = 0; i < DEPTH; i++) begin
                        r_valid[i] <= 1'b0;
                        r_data[i]  <= '0;
                    end
                end else begin
                    r_valid[0] <= i_valid;
                    r_data[0]  <= i_data;
                    for (int i = 1; i < DEPTH; i++) begin
                        r_valid[i] <= r_valid[i-1];
                        r_data[i]  <= r_data[i-1];
                    end
                end
            )

            assign o_valid = r_valid[DEPTH-1];
            assign o_data  = r_data[DEPTH-1];
        end
    endgenerate

endmodule : alu_infer_delay
