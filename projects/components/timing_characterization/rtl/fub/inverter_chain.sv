// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: inverter_chain
// Purpose: Inverter Chain for Timing Characterization
//
// Description:
//   Parameterizable chain of inverters between input and output flip-flops.
//   Used to measure pure gate propagation delay (no fan-in) at various
//   frequencies and across different technology targets.
//
//   The chain is a simple linear sequence of inversions:
//     r_input_flop -> INV -> INV -> ... -> INV -> r_out_flop
//
//   The critical path is NUM_INVERTERS gate delays from input flop
//   to output flop.
//
// Parameters:
//   NUM_INVERTERS - Number of inverters in the chain (critical path depth)
//                   Valid range: 1 to 1024
//
// Notes:
//   - Synthesis preservation attributes prevent optimization of the chain
//   - Even number of inverters: output matches input polarity
//   - Odd number of inverters: output is inverted from input
//   - Critical path = NUM_INVERTERS inverter delays
//   - All flops use reset macros per repository standards
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module inverter_chain #(
    parameter int NUM_INVERTERS = 64
) (
    // Clock and Reset
    input  logic clk,
    input  logic rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic i_data,
    output logic o_data
);

    //=========================================================================
    // Input Flip-Flop
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic r_input_flop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_input_flop <= 1'b0;
        end else begin
            r_input_flop <= i_data;
        end
    )

    //=========================================================================
    // Inverter Chain (Combinational)
    //=========================================================================
    // Linear chain of inverters. Each node declares its own wire inside
    // the generate block to avoid Verilator UNOPTFLAT warnings.

    genvar g;
    generate
        for (g = 0; g < NUM_INVERTERS; g++) begin : gen_inv_chain

            `ifdef XILINX
                (* dont_touch = "true" *)
            `elsif INTEL
                /* synthesis preserve */
            `endif
            logic w_node;

            if (g == 0) begin : gen_first
                assign w_node = ~r_input_flop;
            end else begin : gen_rest
                assign w_node = ~gen_inv_chain[g-1].w_node;
            end

        end
    endgenerate

    //=========================================================================
    // Output Flip-Flop
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic r_out_flop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_flop <= 1'b0;
        end else begin
            r_out_flop <= gen_inv_chain[NUM_INVERTERS-1].w_node;
        end
    )

    assign o_data = r_out_flop;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (NUM_INVERTERS >= 1) else $fatal(1, "NUM_INVERTERS must be >= 1");
    end
    `endif

endmodule : inverter_chain
