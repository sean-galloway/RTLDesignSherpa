// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: multiplier_tree
// Purpose: Multiplier Wrapper for Timing Characterization
//
// Description:
//   Parameterizable multiplier between input and output flip-flops.
//   Supports multiple multiplier implementations for comparing
//   structural vs. synthesis-inferred timing characteristics.
//
//   Structure:
//     r_input_a[N-1:0] ---\
//                           MULTIPLIER (N x N) --> r_out_flops[2*N-1:0]
//     r_input_b[N-1:0] ---/
//
//   MULT_TYPE selects the multiplier implementation:
//     0 = Inferred  (* operator, synthesis decides DSP vs. LUT)
//     1 = Dadda tree (structural, half/full adder reduction)
//     2 = Wallace tree (structural, full adder reduction)
//     3 = Wallace tree CSA (structural, carry-save adder reduction)
//     4 = Dadda 4:2 compressor (structural, 4:2 compressor reduction)
//
//   WIDTH selects the operand size. Structural multipliers are
//   available in fixed sizes; inferred supports any width.
//     Dadda tree:       8, 16, 32
//     Wallace tree:     8, 16, 32
//     Wallace CSA:      8, 16, 32
//     Dadda 4:2:        8, 11, 24
//     Inferred:         any (2 to 128)
//
//   Unsupported WIDTH/MULT_TYPE combinations fall back to inferred.
//
// Parameters:
//   MULT_TYPE - Multiplier implementation (0-4, see above)
//   WIDTH     - Operand bit width
//
// Notes:
//   - Synthesis preservation attributes prevent optimization
//   - Structural multipliers use math_adder_half, math_adder_full,
//     math_adder_carry_save, math_compressor_4to2 from rtl/common/
//   - Output is 2*WIDTH bits (full product)
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module multiplier_tree #(
    parameter int MULT_TYPE = 0,     // 0=inferred, 1=dadda, 2=wallace, 3=wallace_csa, 4=dadda_4to2
    parameter int WIDTH     = 16
) (
    // Clock and Reset
    input  logic                  clk,
    input  logic                  rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic [WIDTH-1:0]      i_data_a,
    input  logic [WIDTH-1:0]      i_data_b,
    output logic [2*WIDTH-1:0]    o_data
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
    // Multiplier (Combinational)
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [2*WIDTH-1:0] w_product;

    generate

        //---------------------------------------------------------------------
        // Type 0: Inferred (* operator)
        //---------------------------------------------------------------------
        if (MULT_TYPE == 0) begin : gen_inferred
            assign w_product = r_input_a * r_input_b;
        end

        //---------------------------------------------------------------------
        // Type 1: Dadda Tree (available: 8, 16, 32)
        //---------------------------------------------------------------------
        else if (MULT_TYPE == 1) begin : gen_dadda

            if (WIDTH == 8) begin : gen_w8
                math_multiplier_dadda_tree_008 #(.N(8)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 16) begin : gen_w16
                math_multiplier_dadda_tree_016 #(.N(16)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 32) begin : gen_w32
                math_multiplier_dadda_tree_032 #(.N(32)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else begin : gen_fallback
                // Unsupported width for Dadda tree; fall back to inferred
                assign w_product = r_input_a * r_input_b;
            end

        end

        //---------------------------------------------------------------------
        // Type 2: Wallace Tree (available: 8, 16, 32)
        //---------------------------------------------------------------------
        else if (MULT_TYPE == 2) begin : gen_wallace

            if (WIDTH == 8) begin : gen_w8
                math_multiplier_wallace_tree_008 #(.N(8)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 16) begin : gen_w16
                math_multiplier_wallace_tree_016 #(.N(16)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 32) begin : gen_w32
                math_multiplier_wallace_tree_032 #(.N(32)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else begin : gen_fallback
                assign w_product = r_input_a * r_input_b;
            end

        end

        //---------------------------------------------------------------------
        // Type 3: Wallace Tree CSA (available: 8, 16, 32)
        //---------------------------------------------------------------------
        else if (MULT_TYPE == 3) begin : gen_wallace_csa

            if (WIDTH == 8) begin : gen_w8
                math_multiplier_wallace_tree_csa_008 #(.N(8)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 16) begin : gen_w16
                math_multiplier_wallace_tree_csa_016 #(.N(16)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 32) begin : gen_w32
                math_multiplier_wallace_tree_csa_032 #(.N(32)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else begin : gen_fallback
                assign w_product = r_input_a * r_input_b;
            end

        end

        //---------------------------------------------------------------------
        // Type 4: Dadda 4:2 Compressor (available: 8, 11, 24)
        //---------------------------------------------------------------------
        else if (MULT_TYPE == 4) begin : gen_dadda_4to2

            if (WIDTH == 8) begin : gen_w8
                math_multiplier_dadda_4to2_008 #(.N(8)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 11) begin : gen_w11
                math_multiplier_dadda_4to2_011 #(.N(11)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else if (WIDTH == 24) begin : gen_w24
                math_multiplier_dadda_4to2_024 #(.N(24)) u_mult (
                    .i_multiplier   (r_input_a),
                    .i_multiplicand (r_input_b),
                    .ow_product     (w_product)
                );
            end else begin : gen_fallback
                assign w_product = r_input_a * r_input_b;
            end

        end

        //---------------------------------------------------------------------
        // Default: Inferred
        //---------------------------------------------------------------------
        else begin : gen_default
            assign w_product = r_input_a * r_input_b;
        end

    endgenerate

    //=========================================================================
    // Output Flip-Flops
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [2*WIDTH-1:0] r_out_flops;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_flops <= '0;
        end else begin
            r_out_flops <= w_product;
        end
    )

    assign o_data = r_out_flops;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (WIDTH >= 2) else $fatal(1, "WIDTH must be >= 2");
        assert (MULT_TYPE >= 0 && MULT_TYPE <= 4) else $fatal(1, "MULT_TYPE must be 0-4");
    end
    `endif

endmodule : multiplier_tree
