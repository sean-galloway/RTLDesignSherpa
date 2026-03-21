// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: nand_chain_top
// Purpose: Top-Level NAND Chain Sweep for Timing Characterization
//
// Description:
//   Instantiates multiple nand_chain FUBs with LEVELS swept from
//   MIN_LEVELS to MAX_LEVELS in increments of LEVEL_STEP. Each instance
//   receives LFSR-driven input data and produces one output bit.
//
//   Default configuration: LEVELS = 8, 12, 16, 20, ... 64
//   This creates 15 independent NAND trees, each with a different critical
//   path depth. Synthesis timing reports reveal the maximum NAND depth
//   that meets timing at the target frequency.
//
//   Each nand_chain instance uses a fixed pool of NUM_FLOPS input flops.
//   When 2^LEVELS > NUM_FLOPS, leaf NANDs reuse flops via modulo wrapping.
//   This keeps physical resource usage bounded regardless of tree depth.
//
//   Instance summary (default parameters, NUM_FLOPS=256):
//     gen_chains[0]  : LEVELS= 8,  ACTUAL_FLOPS=256, NUM_NANDS=    255
//     gen_chains[1]  : LEVELS=12,  ACTUAL_FLOPS=256, NUM_NANDS=   4095
//     gen_chains[2]  : LEVELS=16,  ACTUAL_FLOPS=256, NUM_NANDS=  65535
//     ...and so on up to LEVELS=64 (all share 256 physical flops)
//
//   The NAND tree depth (and thus the critical path) scales with LEVELS,
//   but the flop count is capped at NUM_FLOPS for all instances.
//
// Parameters:
//   MIN_LEVELS  - Smallest NAND tree depth (default: 8)
//   MAX_LEVELS  - Largest NAND tree depth (default: 64)
//   LEVEL_STEP  - Increment between instances (default: 4)
//   NUM_FLOPS   - Physical input flop count per instance (default: 256)
//
// Notes:
//   - Each nand_chain instance has dont_touch/preserve attributes internally
//   - A 32-bit LFSR drives all input flops to prevent constant propagation
//   - All outputs are brought to top-level ports to prevent output pruning
//   - Physical flop count per instance = min(2^LEVELS, NUM_FLOPS)
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module nand_chain_top #(
    // Sweep parameters
    parameter int MIN_LEVELS = 8,                      // Smallest tree depth
    parameter int MAX_LEVELS = 64,                     // Largest tree depth
    parameter int LEVEL_STEP = 4,                      // Increment between instances
    parameter int NUM_FLOPS  = 256,                    // Physical input flop count per instance

    // Derived parameters (do not override)
    parameter int NUM_INSTANCES = ((MAX_LEVELS - MIN_LEVELS) / LEVEL_STEP) + 1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic                        i_seed_valid,  // Pulse to load LFSR seed
    input  logic [31:0]                 i_seed_data,   // LFSR seed value
    output logic [NUM_INSTANCES-1:0]    o_data         // One output bit per chain instance
);

    //=========================================================================
    // LFSR - Drives All Input Flops
    //=========================================================================
    // 32-bit Galois LFSR (maximal length, polynomial x^32+x^22+x^2+x+1)
    // Provides pseudo-random toggling to prevent synthesis constant propagation.
    // Each nand_chain instance replicates the LFSR bits across its input width.

    logic [31:0] r_lfsr;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_lfsr <= 32'hDEAD_BEEF;
        end else begin
            if (i_seed_valid) begin
                r_lfsr <= i_seed_data;
            end else begin
                // Galois LFSR: x^32 + x^22 + x^2 + x + 1
                r_lfsr <= {r_lfsr[30:0], 1'b0}
                        ^ (r_lfsr[31] ? 32'h0040_0007 : 32'h0);
            end
        end
    )

    //=========================================================================
    // NAND Chain Instances
    //=========================================================================
    // Generate one nand_chain per LEVELS value from MIN_LEVELS to MAX_LEVELS
    // in steps of LEVEL_STEP.
    //
    // Each instance's i_data is driven by replicating the 32-bit LFSR output
    // to fill the ACTUAL_FLOPS width. Since all instances with LEVELS >= 8
    // and NUM_FLOPS=256 have ACTUAL_FLOPS=256, the input width is bounded.

    genvar gi;
    generate
        for (gi = 0; gi < NUM_INSTANCES; gi++) begin : gen_chains

            // Calculate LEVELS and actual flop count for this instance
            localparam int INST_LEVELS     = MIN_LEVELS + (gi * LEVEL_STEP);
            localparam int INST_NUM_LEAVES = 2**INST_LEVELS;
            localparam int INST_ACTUAL_FLOPS = (INST_NUM_LEAVES < NUM_FLOPS)
                                               ? INST_NUM_LEAVES : NUM_FLOPS;

            // Replicate LFSR across the bounded input width
            // Uses genvar loop to assign each bit from the 32-bit LFSR pattern
            logic [INST_ACTUAL_FLOPS-1:0] w_chain_input;

            for (genvar gb = 0; gb < INST_ACTUAL_FLOPS; gb++) begin : gen_input_fill
                assign w_chain_input[gb] = r_lfsr[gb % 32];
            end

            // Instantiate nand_chain FUB
            nand_chain #(
                .LEVELS     (INST_LEVELS),
                .NUM_FLOPS  (NUM_FLOPS)
            ) u_nand_chain (
                .clk        (clk),
                .rst_n      (rst_n),
                .i_data     (w_chain_input),
                .o_data     (o_data[gi])
            );

        end
    endgenerate

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (MIN_LEVELS >= 1) else $fatal(1, "MIN_LEVELS must be >= 1");
        assert (MAX_LEVELS >= MIN_LEVELS) else $fatal(1, "MAX_LEVELS must be >= MIN_LEVELS");
        assert (LEVEL_STEP >= 1) else $fatal(1, "LEVEL_STEP must be >= 1");
        assert (((MAX_LEVELS - MIN_LEVELS) % LEVEL_STEP) == 0)
            else $fatal(1, "MAX_LEVELS - MIN_LEVELS must be divisible by LEVEL_STEP");
    end
    `endif

endmodule : nand_chain_top
