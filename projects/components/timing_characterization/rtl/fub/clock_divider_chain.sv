// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: clock_divider_chain
// Purpose: Clock Divider Chain for Timing Characterization
//
// Description:
//   Wraps the existing clock_divider module from rtl/common/ to
//   characterize clock division timing. Cascades NUM_STAGES clock
//   dividers in series, where each stage divides by a configurable
//   power-of-2 ratio based on its pickoff point.
//
//   Structure:
//     clk --> divider[0] --> divider[1] --> ... --> divider[N-1] --> o_divided_clks
//
//   Each stage uses the divided output of the previous stage as input,
//   creating a cascaded frequency reduction chain. The timing
//   characterization interest is in the clock tree insertion delay
//   and the counter/mux path within each divider stage.
//
// Parameters:
//   NUM_STAGES    - Number of cascaded clock divider stages (default: 4)
//   COUNTER_WIDTH - Counter width per stage (default: 16)
//   PICKOFF       - Pickoff point per stage (default: 1, divide by 4)
//
// Notes:
//   - Uses clock_divider from rtl/common/clock_divider.sv
//   - Each stage produces one divided clock output
//   - Stage 0 divides the input clk; stage N divides stage N-1's output
//   - All stages share the same rst_n
//   - The pickoff point is fixed at elaboration time
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module clock_divider_chain #(
    parameter int NUM_STAGES    = 4,
    parameter int COUNTER_WIDTH = 16,
    parameter int PICKOFF       = 1    // Each stage divides by 2^(PICKOFF+1)
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    //=========================================================================
    // Output Interface
    //=========================================================================
    output logic [NUM_STAGES-1:0]   o_divided_clks
);

    // PO_WIDTH must be > $clog2(COUNTER_WIDTH) per clock_divider requirements
    localparam int PO_WIDTH = 8;

    //=========================================================================
    // Cascaded Clock Divider Stages
    //=========================================================================

    genvar g;
    generate
        for (g = 0; g < NUM_STAGES; g++) begin : gen_div_stage

            logic w_stage_clk_in;
            logic w_stage_clk_out;

            // First stage uses input clock; subsequent stages use prior output
            if (g == 0) begin : gen_first
                assign w_stage_clk_in = clk;
            end else begin : gen_cascade
                assign w_stage_clk_in = gen_div_stage[g-1].w_stage_clk_out;
            end

            // Fixed pickoff point for this stage
            logic [PO_WIDTH-1:0] w_pickoff;
            assign w_pickoff = PO_WIDTH'(PICKOFF);

            clock_divider #(
                .N             (1),
                .PO_WIDTH      (PO_WIDTH),
                .COUNTER_WIDTH (COUNTER_WIDTH)
            ) u_divider (
                .clk            (w_stage_clk_in),
                .rst_n          (rst_n),
                .pickoff_points (w_pickoff),
                .divided_clk    (w_stage_clk_out)
            );

            assign o_divided_clks[g] = w_stage_clk_out;

        end
    endgenerate

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (NUM_STAGES >= 1) else $fatal(1, "NUM_STAGES must be >= 1");
        assert (PICKOFF < COUNTER_WIDTH) else $fatal(1, "PICKOFF must be < COUNTER_WIDTH");
    end
    `endif

endmodule : clock_divider_chain
