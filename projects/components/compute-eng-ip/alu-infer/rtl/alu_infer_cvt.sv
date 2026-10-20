// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_cvt
// Purpose: Element-format conversion rows (OP_CVT, OP_ALTFMT) on the
//          rtl/math converters, including the int8 quantizing drain
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - Narrowing (dst lanes narrower): the A line fills the low lanes and the
//     B line the next ones, so two source lines pack one result line.
//   - Widening (dst lanes wider): one A line yields one part of its lanes;
//     B[1:0] selects which part (halves: B[0]; fp8->fp32 quarters: B[1:0]).
//   - bf16 -> int8 quantizes with scale = threshold_imm (bf16), the library
//     math_bf16_scale_to_int8 contract; int8 -> bf16 is unscaled (multiply by
//     the dequant scale with OP_MUL afterwards).
//   - Pairs alu_infer_decode rejects (int8 <-> fp32/fp8) are not built.

`timescale 1ns / 1ps

module alu_infer_cvt
    import alu_infer_pkg::*;
#(
    parameter int LINE_W  = 32,
    parameter bit EN_INT8 = 1'b1,
    parameter bit EN_FP32 = 1'b1,
    parameter bit EN_FP8  = 1'b1
) (
    input  logic [LINE_W-1:0] a_line,
    input  logic [LINE_W-1:0] b_line,
    input  logic [15:0]       imm,
    input  logic [4:0]        opcode,
    input  logic [1:0]        src,      // func_sel fmt
    input  logic [1:0]        dst,      // func_sel sub_op
    output logic [LINE_W-1:0] o_line
);

    localparam int N16 = LINE_W / 16;
    localparam int N32 = LINE_W / 32;
    localparam int N8  = LINE_W / 8;

    logic       half;
    logic [1:0] quarter;
    assign half    = b_line[0];
    assign quarter = b_line[1:0];

    // Narrowing source picks: lane k of an n-lane destination comes from the
    // A line's lane k, or the B line's lane k - n_src.
    function automatic logic [15:0] pick16(input logic [LINE_W-1:0] a, input logic [LINE_W-1:0] b,
                                           input int k);
        return (k < N16) ? a[k*16 +: 16] : b[(k-N16)*16 +: 16];
    endfunction

    function automatic logic [31:0] pick32(input logic [LINE_W-1:0] a, input logic [LINE_W-1:0] b,
                                           input int k);
        return (k < N32) ? a[k*32 +: 32] : b[(k-N32)*32 +: 32];
    endfunction

    logic [LINE_W-1:0] bf16_to_int8, bf16_to_fp8, bf16_to_e5m2, bf16_to_fp16, fp16_to_bf16;
    logic [LINE_W-1:0] int8_to_bf16, fp8_to_bf16, e5m2_to_bf16, fp32_to_bf16;
    logic [LINE_W-1:0] bf16_to_fp32, fp32_to_fp8, fp8_to_fp32;

    generate
        // ---- narrowing into 8-bit lanes from bf16 (A then B) --------------
        for (genvar k = 0; k < N8; k++) begin : gen_n8
            logic [15:0] v;
            assign v = pick16(a_line, b_line, k);
            math_bf16_to_fp8_e5m2 u_e5 (
                .i_a(v), .ow_result(bf16_to_e5m2[k*8 +: 8]),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
            if (EN_INT8) begin : gen_q
                math_bf16_scale_to_int8 u_q (
                    .i_value(v), .i_scale(imm), .ow_int8(bf16_to_int8[k*8 +: 8]),
                    .ow_overflow(), .ow_underflow(), .ow_is_zero(), .ow_invalid());
            end else begin : gen_no_q
                assign bf16_to_int8[k*8 +: 8] = 8'h0;
            end
            if (EN_FP8) begin : gen_f8
                math_bf16_to_fp8_e4m3 u_f8 (
                    .i_a(v), .ow_result(bf16_to_fp8[k*8 +: 8]),
                    .ow_overflow(), .ow_underflow(), .ow_invalid());
            end else begin : gen_no_f8
                assign bf16_to_fp8[k*8 +: 8] = 8'h0;
            end
        end

        // ---- bf16 lanes: same-width and widening into bf16 ----------------
        for (genvar j = 0; j < N16; j++) begin : gen_w16
            logic [15:0] x;
            logic [7:0]  n;   // the 8-bit source lane a widening picks
            assign x = a_line[j*16 +: 16];
            assign n = a_line[(half*N16 + j)*8 +: 8];

            math_bf16_to_fp16 u_h (
                .i_a(x), .ow_result(bf16_to_fp16[j*16 +: 16]),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
            math_fp16_to_bf16 u_b (
                .i_a(x), .ow_result(fp16_to_bf16[j*16 +: 16]),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
            math_fp8_e5m2_to_bf16 u_e5 (
                .i_a(n), .ow_result(e5m2_to_bf16[j*16 +: 16]), .ow_invalid());
            if (EN_INT8) begin : gen_i
                math_int_to_bf16 #(.INT_WIDTH(8)) u_i (
                    .i_int(n), .ow_bf16(int8_to_bf16[j*16 +: 16]), .ow_is_zero());
            end else begin : gen_no_i
                assign int8_to_bf16[j*16 +: 16] = 16'h0;
            end
            if (EN_FP8) begin : gen_f8
                math_fp8_e4m3_to_bf16 u_f8 (
                    .i_a(n), .ow_result(fp8_to_bf16[j*16 +: 16]), .ow_invalid());
            end else begin : gen_no_f8
                assign fp8_to_bf16[j*16 +: 16] = 16'h0;
            end
            if (EN_FP32) begin : gen_f32
                math_fp32_to_bf16 u_f32 (
                    .i_a(pick32(a_line, b_line, j)), .ow_result(fp32_to_bf16[j*16 +: 16]),
                    .ow_overflow(), .ow_underflow(), .ow_invalid());
            end else begin : gen_no_f32
                assign fp32_to_bf16[j*16 +: 16] = 16'h0;
            end
        end

        // ---- fp32 lanes: widening into fp32, and fp32 -> fp8 --------------
        if (EN_FP32) begin : gen_fp32
            for (genvar j = 0; j < N32; j++) begin : gen_w32
                math_bf16_to_fp32 u_b (
                    .i_a(a_line[(half*N32 + j)*16 +: 16]),
                    .ow_result(bf16_to_fp32[j*32 +: 32]), .ow_invalid());
                if (EN_FP8) begin : gen_f8
                    math_fp8_e4m3_to_fp32 u_f8 (
                        .i_a(a_line[(quarter*N32 + j)*8 +: 8]),
                        .ow_result(fp8_to_fp32[j*32 +: 32]), .ow_invalid());
                end else begin : gen_no_f8
                    assign fp8_to_fp32[j*32 +: 32] = 32'h0;
                end
            end
            for (genvar k = 0; k < N8; k++) begin : gen_n8_32
                if (EN_FP8 && k < 2*N32) begin : gen_f8
                    math_fp32_to_fp8_e4m3 u_f8 (
                        .i_a(pick32(a_line, b_line, k)), .ow_result(fp32_to_fp8[k*8 +: 8]),
                        .ow_overflow(), .ow_underflow(), .ow_invalid());
                end else begin : gen_zero
                    assign fp32_to_fp8[k*8 +: 8] = 8'h0;
                end
            end
        end else begin : gen_no_fp32
            assign bf16_to_fp32 = '0;
            assign fp8_to_fp32  = '0;
            assign fp32_to_fp8  = '0;
        end
    endgenerate

    always_comb begin
        o_line = '0;
        if (opcode == OP_ALTFMT) begin
            case (dst)
                ALT_BF16_TO_FP16: o_line = bf16_to_fp16;
                ALT_FP16_TO_BF16: o_line = fp16_to_bf16;
                ALT_BF16_TO_E5M2: o_line = bf16_to_e5m2;
                default:          o_line = e5m2_to_bf16;
            endcase
        end else if (src == dst) begin
            o_line = a_line;
        end else begin
            case ({src, dst})
                {FMT_BF16, FMT_INT8}: o_line = bf16_to_int8;
                {FMT_BF16, FMT_FP32}: o_line = bf16_to_fp32;
                {FMT_BF16, FMT_FP8}:  o_line = bf16_to_fp8;
                {FMT_INT8, FMT_BF16}: o_line = int8_to_bf16;
                {FMT_FP32, FMT_BF16}: o_line = fp32_to_bf16;
                {FMT_FP32, FMT_FP8}:  o_line = fp32_to_fp8;
                {FMT_FP8,  FMT_BF16}: o_line = fp8_to_bf16;
                {FMT_FP8,  FMT_FP32}: o_line = fp8_to_fp32;
                default:              o_line = '0;
            endcase
        end
    end

endmodule : alu_infer_cvt
