// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_fp32_rows
// Purpose: fp32-format function rows (LINE_W/32 lanes): add/sub, mul,
//          min/max, compare, relu, const on the IEEE 754-2008 fp32 blocks
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - The 16-bit threshold_imm is a bf16 pattern; fp32 rows widen it
//     exactly to {imm, 16'h0} for compare and const.
//   - Library FTZ default (SUBNORMAL_SUPPORT = 0), as every other row.

`timescale 1ns / 1ps

module alu_infer_fp32_rows
    import alu_infer_pkg::*;
#(
    parameter int LINE_W        = 32,
    parameter int ADDER_LATENCY = 3
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic [LINE_W-1:0] a_line,
    input  logic [LINE_W-1:0] b_line,
    input  logic [15:0]       imm,
    input  logic [4:0]        opcode,
    input  logic [1:0]        sub_op,
    input  logic              add_issue,

    output logic [LINE_W-1:0] o_comb,
    output logic [LINE_W-1:0] o_flags,
    output logic [LINE_W-1:0] o_add,
    output logic [LINE_W-1:0] o_mul
);

    localparam int NL = LINE_W / 32;

    logic [31:0]   imm32;
    logic [NL-1:0] lt;

    assign imm32 = {imm, 16'h0};

    generate
        for (genvar i = 0; i < NL; i++) begin : gen_lane
            logic [31:0] a, b, add_b, cmp_b, mn, mx, rl;

            assign a     = a_line[i*32 +: 32];
            assign b     = b_line[i*32 +: 32];
            assign add_b = (opcode == OP_SUB) ? (b ^ 32'h8000_0000) : b;
            assign cmp_b = sub_op[0] ? imm32 : b;

            math_ieee754_2008_fp32_adder #(
                .PIPE_STAGE_1(ADDER_LATENCY > 0 ? 1 : 0),
                .PIPE_STAGE_2(ADDER_LATENCY > 1 ? 1 : 0),
                .PIPE_STAGE_3(ADDER_LATENCY > 2 ? 1 : 0),
                .PIPE_STAGE_4(ADDER_LATENCY > 3 ? 1 : 0)
            ) u_adder (
                .i_clk       (clk),
                .i_rst_n     (aresetn),
                .i_a         (a),
                .i_b         (add_b),
                .i_valid     (add_issue),
                .ow_result   (o_add[i*32 +: 32]),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  (),
                .ow_valid    ()
            );

            math_ieee754_2008_fp32_multiplier u_mul (
                .i_a         (a),
                .i_b         (b),
                .ow_result   (o_mul[i*32 +: 32]),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  ()
            );

            math_fp32_min  u_min  (.i_a(a), .i_b(b), .ow_result(mn));
            math_fp32_max  u_max  (.i_a(a), .i_b(b), .ow_result(mx));
            math_fp32_relu u_relu (.i_a(a), .ow_result(rl));

            math_fp32_comparator u_cmp (
                .i_a    (a),
                .i_b    (cmp_b),
                .ow_eq  (),
                .ow_lt  (lt[i]),
                .ow_gt  (),
                .ow_le  (),
                .ow_ge  (),
                .ow_ne  (),
                .ow_unord()
            );

            always_comb begin
                case (opcode)
                    OP_MINMAX: o_comb[i*32 +: 32] = sub_op[0] ? mx : mn;
                    OP_RELU:   o_comb[i*32 +: 32] = rl;
                    OP_CONST:  o_comb[i*32 +: 32] = imm32;
                    OP_COPY:   o_comb[i*32 +: 32] = a;
                    default:   o_comb[i*32 +: 32] = 32'h0;
                endcase
            end
        end
    endgenerate

    assign o_flags = {{(LINE_W-NL){1'b0}}, lt};

endmodule : alu_infer_fp32_rows
