// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_int8_rows
// Purpose: int8-format function rows (LINE_W/8 signed lanes): saturating
//          add/sub/mul, min/max, compare, relu, const
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - Two's-complement lanes; add, sub and mul saturate to [-128, 127]
//     (no wrap), the inference convention.  MAC accumulates in int32 in
//     alu_infer_acc, not here.

`timescale 1ns / 1ps

module alu_infer_int8_rows
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

    function automatic logic [7:0] sat8(input logic signed [16:0] x);
        if (x > 17'sd127)       return 8'h7F;
        else if (x < -17'sd128) return 8'h80;
        else                    return x[7:0];
    endfunction

    logic [NL-1:0] lt;

    generate
        for (genvar i = 0; i < NL; i++) begin : gen_lane
            logic signed [7:0]  a, b, cmp_b;
            logic signed [16:0] sum, dif, prd;

            assign a     = a_line[i*8 +: 8];
            assign b     = b_line[i*8 +: 8];
            assign cmp_b = sub_op[0] ? imm[7:0] : b;
            assign sum   = 17'(a) + 17'(b);
            assign dif   = 17'(a) - 17'(b);
            assign prd   = 17'(a) * 17'(b);
            assign lt[i] = (a < cmp_b);

            always_comb begin
                case (opcode)
                    OP_ADD:    o_comb[i*8 +: 8] = sat8(sum);
                    OP_SUB:    o_comb[i*8 +: 8] = sat8(dif);
                    OP_MUL:    o_comb[i*8 +: 8] = sat8(prd);
                    OP_MINMAX: o_comb[i*8 +: 8] = (sub_op[0] ^ (a < b)) ? a : b;
                    OP_RELU:   o_comb[i*8 +: 8] = a[7] ? 8'h00 : a;
                    OP_CONST:  o_comb[i*8 +: 8] = imm[7:0];
                    OP_COPY:   o_comb[i*8 +: 8] = a;
                    default:   o_comb[i*8 +: 8] = 8'h00;
                endcase
            end
        end
    endgenerate

    assign o_flags = {{(LINE_W-NL){1'b0}}, lt};

endmodule : alu_infer_int8_rows
