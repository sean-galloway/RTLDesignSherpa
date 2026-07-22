// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_carry_save
// Purpose: Math Multiplier Carry Save module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_multiplier_carry_save #(
    parameter int N = 4
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
    // Arrays for carry-save multiplication - FIXED: Use [N-1:0] instead of [N:0]
    logic [N-1:0] w_cin  [N] /*verilator isolate_assignments*/;
    logic [N-1:0] w_pin  [N] /*verilator isolate_assignments*/;
    logic [N-1:0] w_cout [N] /*verilator isolate_assignments*/;
    logic [N-1:0] w_pout [N] /*verilator isolate_assignments*/;
    logic [N-1:0] w_product;

    genvar i, j;
    generate
        for (i = 0; i < N; i++) begin : gen_row
            for (j = 0; j < N; j++) begin : gen_col
                math_multiplier_basic_cell basic_mul_cell (
                    .i_i  (i_multiplier[i]),
                    .i_j  (i_multiplicand[j]),
                    .i_c  (w_cin[i][j]),
                    .i_p  (w_pin[i][j]),
                    .ow_c (w_cout[i][j]),
                    .ow_p (w_pout[i][j])
                );
            end
        end

        // Initialize first row inputs
        for (j = 0; j < N; j++) begin : gen_first_row_init
            assign w_cin[0][j] = 1'b0;
            if (j == 0) begin
                assign w_pin[0][j] = 1'b0;
            end else begin
                assign w_pin[0][j] = 1'b0;
            end
        end

        // Connect intermediate rows
        for (i = 1; i < N; i++) begin : gen_row_connect
            for (j = 0; j < N; j++) begin : gen_col_connect
                assign w_cin[i][j] = w_cout[i-1][j];
                if (j == N-1) begin
                    assign w_pin[i][j] = 1'b0;
                end else begin
                    assign w_pin[i][j] = w_pout[i-1][j+1];
                end
            end
        end

        // Collect LSB of each row for final product
        for (i = 0; i < N; i++) begin : gen_lsb
            assign w_product[i] = w_pout[i][0];
        end
    endgenerate

    // Final addition: add the MSB carries and partial sums from last row
    logic [N-1:0] final_carries, final_partials;
    logic [N-1:0] final_sum;

    assign final_carries = w_cout[N-1][N-1:0];
    assign final_partials = {1'b0, w_pout[N-1][N-1:1]};
    assign final_sum = final_carries + final_partials;

    assign ow_product = {final_sum, w_product};

endmodule : math_multiplier_carry_save
