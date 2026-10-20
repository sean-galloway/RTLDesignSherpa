// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_bf16_rows
// Purpose: bf16-format function rows: add/sub, mul, min/max, compare, relu,
//          const -- LINE_W/16 lanes, each row on its math_bf16_* block
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-17 (as part of alu_infer_rows)
// Updated: 2026-10-20 -- split out of alu_infer_rows per element format

`timescale 1ns / 1ps

module alu_infer_bf16_rows
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
    input  logic              add_issue,     // an add/sub enters the adder row

    output logic [LINE_W-1:0] o_comb,        // copy/minmax/relu/const, at issue
    output logic [LINE_W-1:0] o_flags,       // compare mask, packed low
    output logic [LINE_W-1:0] o_add,         // ADDER_LATENCY after add_issue
    output logic [LINE_W-1:0] o_mul          // combinational product line
);

    localparam int NL = LINE_W / 16;

    logic [15:0] a [NL];
    logic [15:0] b [NL];
    logic [15:0] add_r  [NL];
    logic [15:0] mul_r  [NL];
    logic [15:0] min_r  [NL];
    logic [15:0] max_r  [NL];
    logic [15:0] relu_r [NL];
    logic [NL-1:0] lt;

    generate
        for (genvar i = 0; i < NL; i++) begin : gen_lane
            logic [15:0] add_b;
            logic [15:0] cmp_b;

            assign a[i] = a_line[i*16 +: 16];
            assign b[i] = b_line[i*16 +: 16];

            // Sub shares the adder: sign-flipped B.
            assign add_b = (opcode == OP_SUB) ? (b[i] ^ 16'h8000) : b[i];

            math_bf16_adder #(
                .PIPE_STAGE_1(ADDER_LATENCY > 0 ? 1 : 0),
                .PIPE_STAGE_2(ADDER_LATENCY > 1 ? 1 : 0),
                .PIPE_STAGE_3(ADDER_LATENCY > 2 ? 1 : 0),
                .PIPE_STAGE_4(ADDER_LATENCY > 3 ? 1 : 0)
            ) u_adder (
                .i_clk       (clk),
                .i_rst_n     (aresetn),
                .i_a         (a[i]),
                .i_b         (add_b),
                .i_valid     (add_issue),
                .ow_result   (add_r[i]),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  (),
                .ow_valid    ()
            );

            math_bf16_multiplier u_mul (
                .i_a         (a[i]),
                .i_b         (b[i]),
                .ow_result   (mul_r[i]),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  ()
            );

            math_bf16_min u_min (.i_a(a[i]), .i_b(b[i]), .ow_result(min_r[i]));
            math_bf16_max u_max (.i_a(a[i]), .i_b(b[i]), .ow_result(max_r[i]));

            // Compare: A < B, or A < threshold_imm when sub_op[0] is set.
            assign cmp_b = sub_op[0] ? imm : b[i];
            math_bf16_comparator u_cmp (
                .i_a    (a[i]),
                .i_b    (cmp_b),
                .ow_eq  (),
                .ow_lt  (lt[i]),
                .ow_gt  (),
                .ow_le  (),
                .ow_ge  (),
                .ow_ne  (),
                .ow_unord()
            );

            math_bf16_relu u_relu (.i_a(a[i]), .ow_result(relu_r[i]));

            assign o_add[i*16 +: 16] = add_r[i];
            assign o_mul[i*16 +: 16] = mul_r[i];

            always_comb begin
                case (opcode)
                    OP_MINMAX: o_comb[i*16 +: 16] = sub_op[0] ? max_r[i] : min_r[i];
                    OP_RELU:   o_comb[i*16 +: 16] = relu_r[i];
                    OP_CONST:  o_comb[i*16 +: 16] = imm;
                    OP_COPY:   o_comb[i*16 +: 16] = a[i];
                    default:   o_comb[i*16 +: 16] = 16'h0;   // compare: mask on flags only
                endcase
            end
        end
    endgenerate

    assign o_flags = {{(LINE_W-NL){1'b0}}, lt};

endmodule : alu_infer_bf16_rows
