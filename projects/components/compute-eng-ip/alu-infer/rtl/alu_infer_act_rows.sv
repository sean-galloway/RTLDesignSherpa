// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_act_rows
// Purpose: Library activation and scaling rows on operand A: leaky-relu,
//          gelu, sigmoid, silu, tanh (bf16, fp32, fp8) and reciprocal, exp2,
//          log2, log2-scale (bf16)
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - Each row is the rtl/math block's own approximation, inherited
//     unchanged (gelu/sigmoid/silu/tanh are coarse piecewise forms there);
//     the LUT row (alu_infer_pwl) is the accurate activation path.
//   - LEAKY_SHIFT sets alpha = 2^-LEAKY_SHIFT for every format.

`timescale 1ns / 1ps

module alu_infer_act_rows
    import alu_infer_pkg::*;
#(
    parameter int LINE_W      = 32,
    parameter int LEAKY_SHIFT = 4,
    parameter bit EN_FP32     = 1'b1,
    parameter bit EN_FP8      = 1'b1
) (
    input  logic [LINE_W-1:0] a_line,
    input  logic [4:0]        opcode,
    input  logic [1:0]        fmt,
    output logic [LINE_W-1:0] o_line
);

    localparam int N16 = LINE_W / 16;
    localparam int N32 = LINE_W / 32;
    localparam int N8  = LINE_W / 8;

    logic [LINE_W-1:0] bf16_line, fp32_line, fp8_line;

    // ---------------------------------------------------------------- bf16
    generate
        for (genvar i = 0; i < N16; i++) begin : gen_bf16
            logic [15:0] x, lk, ge, sg, si, th, rc, e2, l2, qs;
            assign x = a_line[i*16 +: 16];

            math_bf16_leaky_relu #(.ALPHA_SHIFT(LEAKY_SHIFT)) u_lk (.i_a(x), .ow_result(lk));
            math_bf16_gelu    u_ge (.i_a(x), .ow_result(ge));
            math_bf16_sigmoid u_sg (.i_a(x), .ow_result(sg));
            math_bf16_silu    u_si (.i_a(x), .ow_result(si));
            math_bf16_tanh    u_th (.i_a(x), .ow_result(th));
            math_bf16_reciprocal u_rc (
                .i_x(x), .ow_reciprocal(rc), .ow_div_by_zero(), .ow_is_zero(), .ow_invalid());
            math_bf16_exp2 u_e2 (
                .i_bf16(x), .ow_exp2(e2), .ow_is_zero(), .ow_is_inf(), .ow_is_nan());
            math_bf16_log2 u_l2 (
                .i_bf16(x), .ow_log2(l2), .ow_is_zero(), .ow_is_inf(), .ow_is_nan(), .ow_is_neg());
            math_bf16_log2_scale u_qs (
                .i_max_value(x), .ow_scale_exp(), .ow_quant_shift(), .ow_dequant_shift(),
                .ow_scale_bf16(qs), .ow_is_zero(), .ow_is_overflow());

            always_comb begin
                case (opcode)
                    OP_LEAKY:   bf16_line[i*16 +: 16] = lk;
                    OP_GELU:    bf16_line[i*16 +: 16] = ge;
                    OP_SIGMOID: bf16_line[i*16 +: 16] = sg;
                    OP_SILU:    bf16_line[i*16 +: 16] = si;
                    OP_TANH:    bf16_line[i*16 +: 16] = th;
                    OP_RECIP:   bf16_line[i*16 +: 16] = rc;
                    OP_EXP2:    bf16_line[i*16 +: 16] = e2;
                    OP_LOG2:    bf16_line[i*16 +: 16] = l2;
                    OP_QSCALE:  bf16_line[i*16 +: 16] = qs;
                    default:    bf16_line[i*16 +: 16] = 16'h0;
                endcase
            end
        end

        // ------------------------------------------------------------ fp32
        if (EN_FP32) begin : gen_fp32
            for (genvar i = 0; i < N32; i++) begin : gen_lane
                logic [31:0] x, lk, ge, sg, si, th;
                assign x = a_line[i*32 +: 32];

                math_fp32_leaky_relu #(.ALPHA_SHIFT(LEAKY_SHIFT)) u_lk (.i_a(x), .ow_result(lk));
                math_fp32_gelu    u_ge (.i_a(x), .ow_result(ge));
                math_fp32_sigmoid u_sg (.i_a(x), .ow_result(sg));
                math_fp32_silu    u_si (.i_a(x), .ow_result(si));
                math_fp32_tanh    u_th (.i_a(x), .ow_result(th));

                always_comb begin
                    case (opcode)
                        OP_LEAKY:   fp32_line[i*32 +: 32] = lk;
                        OP_GELU:    fp32_line[i*32 +: 32] = ge;
                        OP_SIGMOID: fp32_line[i*32 +: 32] = sg;
                        OP_SILU:    fp32_line[i*32 +: 32] = si;
                        OP_TANH:    fp32_line[i*32 +: 32] = th;
                        default:    fp32_line[i*32 +: 32] = 32'h0;
                    endcase
                end
            end
        end else begin : gen_no_fp32
            assign fp32_line = '0;
        end

        // ------------------------------------------------------------- fp8
        if (EN_FP8) begin : gen_fp8
            for (genvar i = 0; i < N8; i++) begin : gen_lane
                logic [7:0] x, lk, ge, sg, si, th;
                assign x = a_line[i*8 +: 8];

                math_fp8_e4m3_leaky_relu #(.ALPHA_SHIFT(LEAKY_SHIFT)) u_lk (.i_a(x), .ow_result(lk));
                math_fp8_e4m3_gelu    u_ge (.i_a(x), .ow_result(ge));
                math_fp8_e4m3_sigmoid u_sg (.i_a(x), .ow_result(sg));
                math_fp8_e4m3_silu    u_si (.i_a(x), .ow_result(si));
                math_fp8_e4m3_tanh    u_th (.i_a(x), .ow_result(th));

                always_comb begin
                    case (opcode)
                        OP_LEAKY:   fp8_line[i*8 +: 8] = lk;
                        OP_GELU:    fp8_line[i*8 +: 8] = ge;
                        OP_SIGMOID: fp8_line[i*8 +: 8] = sg;
                        OP_SILU:    fp8_line[i*8 +: 8] = si;
                        OP_TANH:    fp8_line[i*8 +: 8] = th;
                        default:    fp8_line[i*8 +: 8] = 8'h0;
                    endcase
                end
            end
        end else begin : gen_no_fp8
            assign fp8_line = '0;
        end
    endgenerate

    always_comb begin
        case (fmt)
            FMT_FP32: o_line = fp32_line;
            FMT_FP8:  o_line = fp8_line;
            default:  o_line = bf16_line;
        endcase
    end

endmodule : alu_infer_act_rows
