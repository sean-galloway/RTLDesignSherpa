// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sort
// Purpose: //   Pipelined sorting network for multiple values using odd-even transposition
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: sort
//==============================================================================
// Description:
//   Pipelined sorting network for multiple values using odd-even transposition
//   sort algorithm. Sorts NUM_VALS values in ascending order over NUM_VALS
//   pipeline stages. Each stage performs parallel comparisons and swaps.
//   Fully pipelined for high throughput with deterministic latency.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   NUM_VALS:
//     Description: Number of values to sort
//     Type: int
//     Range: 2 to 16
//     Default: 5
//     Constraints: Determines pipeline depth (NUM_VALS stages)
//
//   Derived Parameters (localparam - computed automatically):
//     STAGES: Number of pipeline stages (equal to NUM_VALS)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Pipelined operation: NUM_VALS clock cycles latency
//   - Input: Concatenated values [NUM_VALS*SIZE-1:0] (value 0 at LSB)
//   - Output: Sorted ascending order (smallest at LSB)
//   - Throughput: One sort result per clock cycle (fully pipelined)
//   - Algorithm: Odd-even transposition sort (compare-swap network)
//   - Resource usage: O(NUM_VALS^2) comparators, O(NUM_VALS^2 * SIZE) registers
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - None (standalone sorting implementation)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_sort.py
//   Run: pytest val/common/test_sort.py -v
//
//==============================================================================

`include "reset_defs.svh"
module sort #(
    parameter int NUM_VALS = 5,
    parameter int SIZE     = 16
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic [NUM_VALS*SIZE-1:0] data,
    input  logic                     valid_in,    // Start sorting when asserted
    output logic [NUM_VALS*SIZE-1:0] sorted,
    output logic                     done
);

    // Calculate number of pipeline stages needed
    // For odd-even sort: NUM_VALS stages gives us enough passes
    localparam int STAGES = NUM_VALS;

    // Pipeline registers for data (flopped signals start with r_)
    logic [NUM_VALS*SIZE-1:0] r_stage_data [1:STAGES];
    logic r_stage_valid [1:STAGES];

    // Wire signals for combinational logic (wires start with w_)
    logic [SIZE-1:0] w_values [STAGES+1][NUM_VALS];
    logic [SIZE-1:0] w_next_values [1:STAGES][NUM_VALS];

    // Input stage wires (not registered)
    logic [NUM_VALS*SIZE-1:0] w_stage_data_0;
    logic w_stage_valid_0;

    // Input stage assignments
    assign w_stage_data_0 = data;
    assign w_stage_valid_0 = valid_in;

    // Unpack input into wire arrays
    generate
        for (genvar i = 0; i < NUM_VALS; i++) begin : g_unpack_input
            assign w_values[0][i] = w_stage_data_0[i*SIZE +: SIZE];
        end
    endgenerate

    // Unpack pipeline stage data into wire arrays
    generate
        for (genvar stage = 1; stage <= STAGES; stage++) begin : g_unpack_stages
            for (genvar i = 0; i < NUM_VALS; i++) begin : g_unpack_stage_data
                assign w_values[stage][i] = r_stage_data[stage][i*SIZE +: SIZE];
            end
        end
    endgenerate

    // Pipeline stages implementing odd-even sort
    generate
        for (genvar stage = 1; stage <= STAGES; stage++) begin : g_pipeline_stages

            // Determine if this is an odd or even pass
            localparam bit IS_ODD_PASS = ((stage-1) % 2) == 0;

            // Combinational logic for compare-and-swap (wires)
            always_comb begin
                // Default: pass through values unchanged
                for (int i = 0; i < NUM_VALS; i++) begin
                    w_next_values[stage][i] = w_values[stage-1][i];
                end

                // Perform compare-and-swap operations
                if (IS_ODD_PASS) begin
                    // Odd pass: compare (0,1), (2,3), (4,5), etc.
                    for (int i = 0; i < NUM_VALS-1; i += 2) begin
                        if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                            w_next_values[stage][i]   = w_values[stage-1][i+1];
                            w_next_values[stage][i+1] = w_values[stage-1][i];
                        end
                    end
                end else begin
                    // Even pass: compare (1,2), (3,4), (5,6), etc.
                    for (int i = 1; i < NUM_VALS-1; i += 2) begin
                        if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                            w_next_values[stage][i]   = w_values[stage-1][i+1];
                            w_next_values[stage][i+1] = w_values[stage-1][i];
                        end
                    end
                end
            end

            // Flop the results (r_ registers)
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_stage_data[stage] <= '0;
                    r_stage_valid[stage] <= 1'b0;
                end else begin
                    // Propagate valid signal
                    if (stage == 1) begin
                        r_stage_valid[stage] <= w_stage_valid_0;
                    end else begin
                        r_stage_valid[stage] <= r_stage_valid[stage-1];
                    end

                    // Pack sorted values back to data bus
                    for (int i = 0; i < NUM_VALS; i++) begin
                        r_stage_data[stage][i*SIZE +: SIZE] <= w_next_values[stage][i];
                    end
                end
            )

        end
    endgenerate

    // Output assignments
    assign sorted = r_stage_data[STAGES];
    assign done = r_stage_valid[STAGES];

endmodule
