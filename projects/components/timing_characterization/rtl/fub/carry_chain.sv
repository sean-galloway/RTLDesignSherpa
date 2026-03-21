// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: carry_chain
// Purpose: Ripple-Carry Adder Chain for Timing Characterization
//
// Description:
//   Parameterizable ripple-carry adder between input and output flip-flops.
//   Used to measure carry-chain propagation delay, which tests dedicated
//   fast-carry logic on FPGAs (CARRY4 on Xilinx, carry chain in Intel ALMs)
//   versus generic LUT paths.
//
//   Structure:
//     r_input_a[WIDTH-1:0] ---\
//                               RIPPLE ADDER (WIDTH bits) --> r_out_flops[WIDTH:0]
//     r_input_b[WIDTH-1:0] ---/
//
//   The critical path is the carry propagation through WIDTH full-adder stages.
//
// Parameters:
//   WIDTH - Bit width of the adder (critical path = WIDTH carry delays)
//           Valid range: 2 to 1024
//
// Notes:
//   - Synthesis preservation attributes prevent optimization
//   - The '+' operator infers ripple-carry logic; tools map to dedicated carry
//   - Output is WIDTH+1 bits (includes carry-out)
//   - Critical path = WIDTH carry-chain delays
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module carry_chain #(
    parameter int WIDTH = 64
) (
    // Clock and Reset
    input  logic              clk,
    input  logic              rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic [WIDTH-1:0]  i_data_a,
    input  logic [WIDTH-1:0]  i_data_b,
    output logic [WIDTH:0]    o_data
);

    //=========================================================================
    // Input Flip-Flops
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH-1:0] r_input_a;

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH-1:0] r_input_b;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_input_a <= '0;
            r_input_b <= '0;
        end else begin
            r_input_a <= i_data_a;
            r_input_b <= i_data_b;
        end
    )

    //=========================================================================
    // Ripple-Carry Adder (Combinational)
    //=========================================================================
    // The '+' operator produces a ripple-carry adder. Synthesis tools will
    // map this to dedicated carry-chain resources on FPGAs.

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH:0] w_sum;

    assign w_sum = {1'b0, r_input_a} + {1'b0, r_input_b};

    //=========================================================================
    // Output Flip-Flops
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH:0] r_out_flops;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_flops <= '0;
        end else begin
            r_out_flops <= w_sum;
        end
    )

    assign o_data = r_out_flops;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (WIDTH >= 2) else $fatal(1, "WIDTH must be >= 2");
    end
    `endif

endmodule : carry_chain
