// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_fp8_rows
// Purpose: fp8 (e4m3) function rows (LINE_W/8 lanes): add/sub, mul,
//          min/max, compare, relu, const on the math_fp8_e4m3_* blocks
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - The fp8 rows are combinational (the library blocks are); they land on
//     the combinational port.  threshold_imm[7:0] is an e4m3 pattern for
//     compare and const.

`timescale 1ns / 1ps

module alu_infer_fp8_rows
    import alu_infer_pkg::*;
#(
    parameter int LINE_W = 32
) (
    input  logic [LINE_W-1:0] a_line,
    input  logic [LINE_W-1:0] b_line,
    input  logic [15:0]       imm,
    input  logic [4:0]        opcode,
    input  logic [1:0]        sub_op,

    output logic [LINE_W-1:0] o_comb,
    output logic [LINE_W-1:0] o_flags
);

    localparam int NL = LINE_W / 8;

    logic [NL-1:0] lt;

    generate
        for (genvar i = 0; i < NL; i++) begin : gen_lane
            logic [7:0] a, b, add_b, cmp_b, sm, pr, mn, mx, rl;

            assign a     = a_line[i*8 +: 8];
            assign b     = b_line[i*8 +: 8];
            assign add_b = (opcode == OP_SUB) ? (b ^ 8'h80) : b;
            assign cmp_b = sub_op[0] ? imm[7:0] : b;

            math_fp8_e4m3_adder u_add (
                .i_a(a), .i_b(add_b), .ow_result(sm),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
            math_fp8_e4m3_multiplier u_mul (
                .i_a(a), .i_b(b), .ow_result(pr),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
            math_fp8_e4m3_min  u_min  (.i_a(a), .i_b(b), .ow_result(mn));
            math_fp8_e4m3_max  u_max  (.i_a(a), .i_b(b), .ow_result(mx));
            math_fp8_e4m3_relu u_relu (.i_a(a), .ow_result(rl));
            math_fp8_e4m3_comparator u_cmp (
                .i_a(a), .i_b(cmp_b), .ow_eq(), .ow_lt(lt[i]), .ow_gt(),
                .ow_le(), .ow_ge(), .ow_ne(), .ow_unord());

            always_comb begin
                case (opcode)
                    OP_ADD,
                    OP_SUB:    o_comb[i*8 +: 8] = sm;
                    OP_MUL:    o_comb[i*8 +: 8] = pr;
                    OP_MINMAX: o_comb[i*8 +: 8] = sub_op[0] ? mx : mn;
                    OP_RELU:   o_comb[i*8 +: 8] = rl;
                    OP_CONST:  o_comb[i*8 +: 8] = imm[7:0];
                    OP_COPY:   o_comb[i*8 +: 8] = a;
                    default:   o_comb[i*8 +: 8] = 8'h00;
                endcase
            end
        end
    endgenerate

    assign o_flags = {{(LINE_W-NL){1'b0}}, lt};

endmodule : alu_infer_fp8_rows
