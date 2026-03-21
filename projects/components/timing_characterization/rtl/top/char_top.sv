// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_top
// Purpose: Top-Level Timing Characterization Wrapper
//
// Description:
//   Configurable top-level that instantiates a selectable mix of timing
//   characterization FUBs. Feature-select parameters control which blocks
//   are included in the design, allowing targeted synthesis runs for
//   specific characterization goals.
//
//   Available features (each independently enabled):
//     EN_NAND_TREE       - NAND gate binary tree (nand_chain)
//     EN_INVERTER_CHAIN  - Inverter chain (inverter_chain)
//     EN_XOR_TREE        - XOR gate binary tree (xor_tree)
//     EN_CARRY_CHAIN     - Ripple-carry adder (carry_chain)
//     EN_MULTIPLIER      - Multiplier tree (multiplier_tree)
//     EN_MUX_TREE        - Binary mux tree (mux_tree)
//     EN_QUEUE_DEPTH     - FIFO queue depth (queue_depth)
//     EN_CLK_DIVIDER     - Clock divider chain (clock_divider_chain)
//     EN_GRAY_COUNTER    - Gray counter chain (gray_counter_chain)
//
//   A shared 32-bit LFSR drives all data inputs to prevent constant
//   propagation during synthesis. All outputs are brought to top-level
//   ports to prevent pruning.
//
// Parameters:
//   Feature enables (0=disabled, 1=enabled):
//     EN_NAND_TREE, EN_INVERTER_CHAIN, EN_XOR_TREE, EN_CARRY_CHAIN,
//     EN_MULTIPLIER, EN_MUX_TREE, EN_QUEUE_DEPTH, EN_CLK_DIVIDER,
//     EN_GRAY_COUNTER
//
//   Sizing parameters:
//     NAND_LEVELS, INVERTER_COUNT, XOR_LEVELS, CARRY_WIDTH,
//     MULT_WIDTH, MULT_TYPE, MUX_LEVELS, FIFO_DATA_WIDTH, FIFO_DEPTH,
//     CLK_DIV_STAGES, GRAY_WIDTH, NUM_FLOPS
//
// Notes:
//   - Enable only the features needed for a given synthesis run
//   - Disabled features generate no logic (conditional generate)
//   - LFSR provides pseudo-random toggling data for all enabled blocks
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module char_top #(
    //=========================================================================
    // Feature Enables (0=disabled, 1=enabled)
    //=========================================================================
    parameter int EN_NAND_TREE      = 1,
    parameter int EN_INVERTER_CHAIN = 1,
    parameter int EN_XOR_TREE       = 1,
    parameter int EN_CARRY_CHAIN    = 1,
    parameter int EN_MULTIPLIER     = 1,
    parameter int EN_MUX_TREE       = 1,
    parameter int EN_QUEUE_DEPTH    = 1,
    parameter int EN_CLK_DIVIDER    = 1,
    parameter int EN_GRAY_COUNTER   = 1,

    //=========================================================================
    // Sizing Parameters
    //=========================================================================
    // Tree/chain depth
    parameter int NAND_LEVELS     = 8,      // NAND tree depth
    parameter int INVERTER_COUNT  = 64,     // Inverter chain length
    parameter int XOR_LEVELS      = 8,      // XOR tree depth
    parameter int MUX_LEVELS      = 8,      // Mux tree depth
    parameter int NUM_FLOPS       = 256,    // Input flop pool for trees

    // Datapath width
    parameter int CARRY_WIDTH     = 64,     // Carry chain adder width
    parameter int MULT_WIDTH      = 16,     // Multiplier operand width
    parameter int MULT_TYPE       = 0,      // 0=inferred, 1=dadda, 2=wallace, 3=wallace_csa, 4=dadda_4to2
    parameter int GRAY_WIDTH      = 32,     // Gray counter width

    // FIFO sizing
    parameter int FIFO_DATA_WIDTH = 32,     // Queue data width
    parameter int FIFO_DEPTH      = 16,     // Queue depth (power of 2)

    // Clock divider
    parameter int CLK_DIV_STAGES  = 4,      // Number of cascaded divider stages
    parameter int CLK_DIV_CW      = 16,     // Counter width per stage
    parameter int CLK_DIV_PICKOFF = 1,      // Pickoff point per stage

    //=========================================================================
    // Derived Parameters (do not override)
    //=========================================================================
    parameter int NAND_ACTUAL_FLOPS = ((2**NAND_LEVELS) < NUM_FLOPS)
                                      ? (2**NAND_LEVELS) : NUM_FLOPS,
    parameter int XOR_ACTUAL_FLOPS  = ((2**XOR_LEVELS) < NUM_FLOPS)
                                      ? (2**XOR_LEVELS) : NUM_FLOPS,
    parameter int MUX_ACTUAL_FLOPS  = ((2**MUX_LEVELS) < NUM_FLOPS)
                                      ? (2**MUX_LEVELS) : NUM_FLOPS,
    parameter int MUX_NUM_MUXES     = 2**MUX_LEVELS - 1,
    parameter int MUX_ACTUAL_SEL    = (MUX_NUM_MUXES < NUM_FLOPS)
                                      ? MUX_NUM_MUXES : NUM_FLOPS,
    parameter int FIFO_AW           = $clog2(FIFO_DEPTH)
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // LFSR Seed Interface
    //=========================================================================
    input  logic                        i_seed_valid,
    input  logic [31:0]                 i_seed_data,

    //=========================================================================
    // Output Ports (prevent synthesis pruning)
    //=========================================================================
    // Each enabled feature exposes its output(s) at the top level.
    // Disabled features tie their outputs to 0.

    // NAND tree
    output logic                        o_nand,
    // Inverter chain
    output logic                        o_inverter,
    // XOR tree
    output logic                        o_xor,
    // Carry chain
    output logic [CARRY_WIDTH:0]        o_carry,
    // Multiplier
    output logic [2*MULT_WIDTH-1:0]     o_mult,
    // Mux tree
    output logic                        o_mux,
    // Queue depth
    output logic [FIFO_DATA_WIDTH-1:0]  o_queue_data,
    output logic                        o_queue_valid,
    output logic [FIFO_AW:0]            o_queue_count,
    // Clock divider chain
    output logic [CLK_DIV_STAGES-1:0]   o_clk_div,
    // Gray counter
    output logic [GRAY_WIDTH-1:0]       o_gray_bin,
    output logic [GRAY_WIDTH-1:0]       o_gray_code
);

    //=========================================================================
    // LFSR - Shared Data Source
    //=========================================================================
    // 32-bit Galois LFSR (maximal length, polynomial x^32+x^22+x^2+x+1)
    // Provides pseudo-random toggling to prevent synthesis constant propagation.

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
    // Helper: Replicate LFSR to fill a width
    //=========================================================================
    // Macro-style generate to fill w bits from the 32-bit LFSR

    // We use local functions of assigns below per feature.

    //=========================================================================
    // Feature: NAND Tree
    //=========================================================================

    generate
        if (EN_NAND_TREE != 0) begin : gen_nand

            logic [NAND_ACTUAL_FLOPS-1:0] w_nand_input;
            for (genvar b = 0; b < NAND_ACTUAL_FLOPS; b++) begin : gen_fill
                assign w_nand_input[b] = r_lfsr[b % 32];
            end

            nand_chain #(
                .LEVELS    (NAND_LEVELS),
                .NUM_FLOPS (NUM_FLOPS)
            ) u_nand_chain (
                .clk    (clk),
                .rst_n  (rst_n),
                .i_data (w_nand_input),
                .o_data (o_nand)
            );

        end else begin : gen_no_nand
            assign o_nand = 1'b0;
        end
    endgenerate

    //=========================================================================
    // Feature: Inverter Chain
    //=========================================================================

    generate
        if (EN_INVERTER_CHAIN != 0) begin : gen_inv

            inverter_chain #(
                .NUM_INVERTERS (INVERTER_COUNT)
            ) u_inverter_chain (
                .clk    (clk),
                .rst_n  (rst_n),
                .i_data (r_lfsr[0]),
                .o_data (o_inverter)
            );

        end else begin : gen_no_inv
            assign o_inverter = 1'b0;
        end
    endgenerate

    //=========================================================================
    // Feature: XOR Tree
    //=========================================================================

    generate
        if (EN_XOR_TREE != 0) begin : gen_xor

            logic [XOR_ACTUAL_FLOPS-1:0] w_xor_input;
            for (genvar b = 0; b < XOR_ACTUAL_FLOPS; b++) begin : gen_fill
                assign w_xor_input[b] = r_lfsr[b % 32];
            end

            xor_tree #(
                .LEVELS    (XOR_LEVELS),
                .NUM_FLOPS (NUM_FLOPS)
            ) u_xor_tree (
                .clk    (clk),
                .rst_n  (rst_n),
                .i_data (w_xor_input),
                .o_data (o_xor)
            );

        end else begin : gen_no_xor
            assign o_xor = 1'b0;
        end
    endgenerate

    //=========================================================================
    // Feature: Carry Chain
    //=========================================================================

    generate
        if (EN_CARRY_CHAIN != 0) begin : gen_carry

            logic [CARRY_WIDTH-1:0] w_carry_a;
            logic [CARRY_WIDTH-1:0] w_carry_b;
            for (genvar b = 0; b < CARRY_WIDTH; b++) begin : gen_fill
                assign w_carry_a[b] = r_lfsr[b % 32];
                assign w_carry_b[b] = r_lfsr[(b + 16) % 32];
            end

            carry_chain #(
                .WIDTH (CARRY_WIDTH)
            ) u_carry_chain (
                .clk      (clk),
                .rst_n    (rst_n),
                .i_data_a (w_carry_a),
                .i_data_b (w_carry_b),
                .o_data   (o_carry)
            );

        end else begin : gen_no_carry
            assign o_carry = '0;
        end
    endgenerate

    //=========================================================================
    // Feature: Multiplier Tree
    //=========================================================================

    generate
        if (EN_MULTIPLIER != 0) begin : gen_mult

            logic [MULT_WIDTH-1:0] w_mult_a;
            logic [MULT_WIDTH-1:0] w_mult_b;
            for (genvar b = 0; b < MULT_WIDTH; b++) begin : gen_fill
                assign w_mult_a[b] = r_lfsr[b % 32];
                assign w_mult_b[b] = r_lfsr[(b + 16) % 32];
            end

            multiplier_tree #(
                .MULT_TYPE (MULT_TYPE),
                .WIDTH     (MULT_WIDTH)
            ) u_multiplier (
                .clk      (clk),
                .rst_n    (rst_n),
                .i_data_a (w_mult_a),
                .i_data_b (w_mult_b),
                .o_data   (o_mult)
            );

        end else begin : gen_no_mult
            assign o_mult = '0;
        end
    endgenerate

    //=========================================================================
    // Feature: Mux Tree
    //=========================================================================

    generate
        if (EN_MUX_TREE != 0) begin : gen_mux

            logic [MUX_ACTUAL_FLOPS-1:0] w_mux_data;
            logic [MUX_ACTUAL_SEL-1:0]   w_mux_sel;
            for (genvar b = 0; b < MUX_ACTUAL_FLOPS; b++) begin : gen_fill_data
                assign w_mux_data[b] = r_lfsr[b % 32];
            end
            for (genvar b = 0; b < MUX_ACTUAL_SEL; b++) begin : gen_fill_sel
                assign w_mux_sel[b] = r_lfsr[(b + 7) % 32];
            end

            mux_tree #(
                .LEVELS    (MUX_LEVELS),
                .NUM_FLOPS (NUM_FLOPS)
            ) u_mux_tree (
                .clk    (clk),
                .rst_n  (rst_n),
                .i_data (w_mux_data),
                .i_sel  (w_mux_sel),
                .o_data (o_mux)
            );

        end else begin : gen_no_mux
            assign o_mux = 1'b0;
        end
    endgenerate

    //=========================================================================
    // Feature: Queue Depth (FIFO)
    //=========================================================================

    generate
        if (EN_QUEUE_DEPTH != 0) begin : gen_queue

            logic [FIFO_DATA_WIDTH-1:0] w_fifo_wr_data;
            for (genvar b = 0; b < FIFO_DATA_WIDTH; b++) begin : gen_fill
                assign w_fifo_wr_data[b] = r_lfsr[b % 32];
            end

            // Write whenever FIFO has space (wr_ready driven by FIFO)
            logic w_wr_ready;

            queue_depth #(
                .DATA_WIDTH (FIFO_DATA_WIDTH),
                .DEPTH      (FIFO_DEPTH)
            ) u_queue (
                .clk        (clk),
                .rst_n      (rst_n),
                .i_wr_valid (w_wr_ready),
                .o_wr_ready (w_wr_ready),
                .i_wr_data  (w_fifo_wr_data),
                .i_rd_ready (1'b1),
                .o_rd_valid (o_queue_valid),
                .o_rd_data  (o_queue_data),
                .o_count    (o_queue_count)
            );

        end else begin : gen_no_queue
            assign o_queue_data  = '0;
            assign o_queue_valid = 1'b0;
            assign o_queue_count = '0;
        end
    endgenerate

    //=========================================================================
    // Feature: Clock Divider Chain
    //=========================================================================

    generate
        if (EN_CLK_DIVIDER != 0) begin : gen_clkdiv

            clock_divider_chain #(
                .NUM_STAGES    (CLK_DIV_STAGES),
                .COUNTER_WIDTH (CLK_DIV_CW),
                .PICKOFF       (CLK_DIV_PICKOFF)
            ) u_clk_div (
                .clk            (clk),
                .rst_n          (rst_n),
                .o_divided_clks (o_clk_div)
            );

        end else begin : gen_no_clkdiv
            assign o_clk_div = '0;
        end
    endgenerate

    //=========================================================================
    // Feature: Gray Counter Chain
    //=========================================================================

    generate
        if (EN_GRAY_COUNTER != 0) begin : gen_gray

            gray_counter_chain #(
                .WIDTH (GRAY_WIDTH)
            ) u_gray_counter (
                .clk            (clk),
                .rst_n          (rst_n),
                .i_enable       (r_lfsr[0]),
                .o_counter_bin  (o_gray_bin),
                .o_counter_gray (o_gray_code)
            );

        end else begin : gen_no_gray
            assign o_gray_bin  = '0;
            assign o_gray_code = '0;
        end
    endgenerate

endmodule : char_top
