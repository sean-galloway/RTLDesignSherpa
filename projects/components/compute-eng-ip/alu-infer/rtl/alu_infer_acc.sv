// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_acc
// Purpose: The accumulator rows (MAC and REDUCE) for every element format:
//          a LINE_W/8-lane x 32-bit accumulator bank, an operand pipeline of
//          MAC_LATENCY stages, and a single-cycle accumulate stage
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-17
// Updated: 2026-10-20 -- REDUCE (sum/max, cross-lane fold), int8/fp32/fp8
//          accumulate, MAC_LATENCY operand pipeline, tag-carrying late write
//
// Notes:
//   - acc_ctrl: 2'b00 HOLD, 2'b01 ACCUMULATE, 2'b10 CLEAR, 2'b11 DRAIN.  HOLD
//     and DRAIN both present the bank without changing it.
//   - Every accumulator invocation (CLEAR/HOLD/DRAIN included) flows through
//     the same pipeline in issue order and reads the bank at the accumulate
//     stage, never at issue.  A dependent chain is therefore correct at any
//     MAC_LATENCY and sustains one step per clock: the loop is the one
//     accumulate stage, the operand stages sit ahead of it.
//   - The loop stays the fused math_bf16_fma (bf16, fp8) / fp32 FMA.  A split
//     exact-product + fp32-add loop is NOT bit-equivalent to the fused block
//     (product overflow against an infinite accumulator, subnormal
//     pass-through), so the operand stages are where depth goes.
//   - Formats: bf16 uses lanes 0..LINE_W/16-1, fp8 and int8 0..LINE_W/8-1,
//     fp32 0..LINE_W/32-1.  The bank is shared; CLEAR when changing format.
//   - REDUCE sum folds the A line into the bank (acc + a, one rounding via
//     fma(a, 1.0, acc)); REDUCE max keeps max(acc, a).  CLEAR loads the
//     operation's identity: +0 for MAC and sum, -inf (int8: ACC_INT_MIN) for
//     max.  sub_op[1] presents the cross-lane fold (lane 0 + 1 + ... in lane
//     order, or the max) broadcast to every lane; the bank is unchanged.
//   - int8 MAC/sum accumulate in int32 (wrapping); the presented lane is
//     sat8(round(acc / 2^imm[4:0])), the requantize shift.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_acc
    import alu_infer_pkg::*;
#(
    parameter int LINE_W      = 32,
    parameter int MAC_LATENCY = 0,
    parameter int TAG_W       = 8,
    parameter bit EN_INT8     = 1'b1,
    parameter bit EN_FP32     = 1'b1,
    parameter bit EN_FP8      = 1'b1
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic              acc_issue,
    input  logic [TAG_W-1:0]  issue_tag,
    input  logic [LINE_W-1:0] a_line,
    input  logic [LINE_W-1:0] b_line,
    input  logic [15:0]       imm,
    input  logic [8:0]        func_sel,
    input  logic [1:0]        acc_ctrl,

    output logic              o_valid,
    output logic [TAG_W-1:0]  o_tag,
    output logic [LINE_W-1:0] o_line
);

    localparam int NA  = LINE_W / 8;    // accumulator lanes
    localparam int N16 = LINE_W / 16;
    localparam int N32 = LINE_W / 32;
    localparam int PW  = TAG_W + 2*LINE_W + 16 + 9 + 2;

    // ------------------------------------------------------------------
    // Operand pipeline: the invocation, in order, MAC_LATENCY stages deep.
    // ------------------------------------------------------------------
    logic              s_valid;
    logic [TAG_W-1:0]  s_tag;
    logic [LINE_W-1:0] s_a, s_b;
    logic [15:0]       s_imm;
    logic [8:0]        s_fsel;
    logic [1:0]        s_ctrl;

    alu_infer_delay #(.W(PW), .DEPTH(MAC_LATENCY)) u_opnd (
        .clk     (clk),
        .aresetn (aresetn),
        .i_valid (acc_issue),
        .i_data  ({issue_tag, a_line, b_line, imm, func_sel, acc_ctrl}),
        .o_valid (s_valid),
        .o_data  ({s_tag, s_a, s_b, s_imm, s_fsel, s_ctrl})
    );

    logic [1:0] fmt;
    logic       is_reduce, red_max, fold;

    assign fmt       = s_fsel[8:7];
    assign is_reduce = (s_fsel[4:0] == OP_REDUCE);
    assign red_max   = is_reduce && s_fsel[5];
    assign fold      = is_reduce && s_fsel[6];

    // ------------------------------------------------------------------
    // Accumulate stage (the only loop: bank -> one fused op -> bank).
    // ------------------------------------------------------------------
    logic [31:0] acc_bank [NA];
    logic [31:0] next_acc [NA];
    logic [NA-1:0] lane_on;

    always_comb begin
        for (int i = 0; i < NA; i++) begin
            case (fmt)
                FMT_BF16: lane_on[i] = (i < N16);
                FMT_FP32: lane_on[i] = (i < N32);
                default:  lane_on[i] = 1'b1;
            endcase
        end
    end

    logic [31:0] clear_val;
    always_comb begin
        if (red_max) clear_val = (fmt == FMT_INT8) ? ACC_INT_MIN : FP32_NINF;
        else         clear_val = 32'h0;
    end

    generate
        for (genvar i = 0; i < NA; i++) begin : gen_lane
            // bf16-domain operands: bf16 lanes direct, fp8 lanes widened exactly.
            logic [15:0] x, y, x8, y8, x16, y16;
            logic [31:0] fma_r, max_r, upd;

            if (i < N16) begin : gen_b16
                assign x16 = s_a[i*16 +: 16];
                assign y16 = s_b[i*16 +: 16];
            end else begin : gen_no_b16
                assign x16 = 16'h0;
                assign y16 = 16'h0;
            end

            if (EN_FP8) begin : gen_f8
                math_fp8_e4m3_to_bf16 u_xa (.i_a(s_a[i*8 +: 8]), .ow_result(x8), .ow_invalid());
                math_fp8_e4m3_to_bf16 u_xb (.i_a(s_b[i*8 +: 8]), .ow_result(y8), .ow_invalid());
            end else begin : gen_no_f8
                assign x8 = 16'h0;
                assign y8 = 16'h0;
            end

            always_comb begin
                if (fmt == FMT_FP8) begin
                    x = x8;
                    y = y8;
                end else begin
                    x = x16;
                    y = y16;
                end
            end

            // MAC: acc + x*y; REDUCE sum: acc + x*1.0 (exact, one rounding).
            math_bf16_fma u_fma (
                .i_a        (x),
                .i_b        (is_reduce ? BF16_ONE : y),
                .i_c        (acc_bank[i]),
                .ow_result  (fma_r),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid ()
            );

            logic [31:0] max_in;
            logic [31:0] f32_r;

            // fp32 lanes: the IEEE fp32 FMA (fp32 x fp32 is not exact in fp32).
            if (EN_FP32 && i < N32) begin : gen_f32
                math_ieee754_2008_fp32_fma u_fma32 (
                    .i_a        (s_a[i*32 +: 32]),
                    .i_b        (is_reduce ? FP32_ONE : s_b[i*32 +: 32]),
                    .i_c        (acc_bank[i]),
                    .ow_result  (f32_r),
                    .ow_overflow(),
                    .ow_underflow(),
                    .ow_invalid ()
                );
                assign max_in = (fmt == FMT_FP32) ? s_a[i*32 +: 32] : {x, 16'h0};
            end else begin : gen_no_f32
                assign f32_r  = 32'h0;
                assign max_in = {x, 16'h0};
            end

            math_fp32_max u_max (.i_a(acc_bank[i]), .i_b(max_in), .ow_result(max_r));

            // int8 lanes: int32 accumulate.
            logic signed [31:0] acc_s, ia, ib, i_upd;
            assign acc_s = acc_bank[i];
            assign ia    = 32'(signed'(s_a[i*8 +: 8]));
            assign ib    = 32'(signed'(s_b[i*8 +: 8]));
            always_comb begin
                if (red_max)        i_upd = (ia > acc_s) ? ia : acc_s;
                else if (is_reduce) i_upd = acc_s + ia;
                else                i_upd = acc_s + ia * ib;
            end

            always_comb begin
                case (fmt)
                    FMT_INT8: upd = EN_INT8 ? i_upd : acc_bank[i];
                    FMT_FP32: upd = red_max ? max_r : f32_r;
                    default:  upd = red_max ? max_r : fma_r;
                endcase
            end

            always_comb begin
                next_acc[i] = acc_bank[i];
                if (s_valid && lane_on[i]) begin
                    case (s_ctrl)
                        ACC_CLEAR: next_acc[i] = clear_val;
                        ACC_ACCUM: next_acc[i] = upd;
                        default:   next_acc[i] = acc_bank[i];   // HOLD / DRAIN
                    endcase
                end
            end
        end
    endgenerate

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < NA; i++) acc_bank[i] <= '0;
        end else begin
            for (int i = 0; i < NA; i++) acc_bank[i] <= next_acc[i];
        end
    )

    // ------------------------------------------------------------------
    // Presentation: the post-update bank (or its cross-lane fold).
    // ------------------------------------------------------------------
    // Fold chains in lane order over the format's lanes; inactive lanes pass
    // the running value through, so no identity element enters the chain.
    // Each link is its own generate-block net (gen_fold[i-1] -> gen_fold[i]):
    // one array indexed along the chain reads as a false loop to Verilator.
    generate
        for (genvar i = 0; i < NA; i++) begin : gen_fold
            logic [31:0]        fsum, fmax;
            logic signed [31:0] isum, imax;

            if (i == 0) begin : gen_head
                assign fsum = next_acc[0];
                assign fmax = next_acc[0];
                assign isum = next_acc[0];
                assign imax = next_acc[0];
            end else begin : gen_link
                logic [31:0] add_r, max_r;
                logic signed [31:0] nx;

                math_ieee754_2008_fp32_adder u_add (
                    .i_clk       (clk),
                    .i_rst_n     (aresetn),
                    .i_a         (gen_fold[i-1].fsum),
                    .i_b         (next_acc[i]),
                    .i_valid     (1'b1),
                    .ow_result   (add_r),
                    .ow_overflow (),
                    .ow_underflow(),
                    .ow_invalid  (),
                    .ow_valid    ()
                );
                math_fp32_max u_max (.i_a(gen_fold[i-1].fmax), .i_b(next_acc[i]), .ow_result(max_r));

                assign nx   = next_acc[i];
                assign fsum = lane_on[i] ? add_r : gen_fold[i-1].fsum;
                assign fmax = lane_on[i] ? max_r : gen_fold[i-1].fmax;
                assign isum = gen_fold[i-1].isum + nx;
                assign imax = (nx > gen_fold[i-1].imax) ? nx : gen_fold[i-1].imax;
            end
        end
    endgenerate

    logic [31:0]        fold_fsum, fold_fmax;
    logic signed [31:0] fold_isum, fold_imax;
    assign fold_fsum = gen_fold[NA-1].fsum;
    assign fold_fmax = gen_fold[NA-1].fmax;
    assign fold_isum = gen_fold[NA-1].isum;
    assign fold_imax = gen_fold[NA-1].imax;

    logic [31:0] view [NA];
    always_comb begin
        for (int i = 0; i < NA; i++) begin
            if (!fold)                 view[i] = next_acc[i];
            else if (fmt == FMT_INT8)  view[i] = red_max ? fold_imax : fold_isum;
            else                       view[i] = red_max ? fold_fmax : fold_fsum;
        end
    end

    function automatic logic [7:0] requant(input logic signed [31:0] v, input logic [4:0] sh);
        logic signed [32:0] r;
        r = (sh == 5'd0) ? 33'(v) : ((33'(v) + (33'sd1 <<< (sh - 1))) >>> sh);
        if (r > 33'sd127)       return 8'h7F;
        else if (r < -33'sd128) return 8'h80;
        else                    return r[7:0];
    endfunction

    logic [LINE_W-1:0] bf16_view, fp8_view, fp32_view, int8_view;

    generate
        for (genvar i = 0; i < N16; i++) begin : gen_v16
            math_fp32_to_bf16 u_r (
                .i_a(view[i]), .ow_result(bf16_view[i*16 +: 16]),
                .ow_overflow(), .ow_underflow(), .ow_invalid());
        end
        for (genvar i = 0; i < NA; i++) begin : gen_v8
            if (EN_FP8) begin : gen_f8
                math_fp32_to_fp8_e4m3 u_r (
                    .i_a(view[i]), .ow_result(fp8_view[i*8 +: 8]),
                    .ow_overflow(), .ow_underflow(), .ow_invalid());
            end else begin : gen_no_f8
                assign fp8_view[i*8 +: 8] = 8'h0;
            end
            assign int8_view[i*8 +: 8] = requant(view[i], s_imm[4:0]);
        end
        for (genvar i = 0; i < N32; i++) begin : gen_v32
            assign fp32_view[i*32 +: 32] = view[i];
        end
    endgenerate

    always_comb begin
        case (fmt)
            FMT_INT8: o_line = int8_view;
            FMT_FP32: o_line = fp32_view;
            FMT_FP8:  o_line = fp8_view;
            default:  o_line = bf16_view;
        endcase
    end

    assign o_valid = s_valid;
    assign o_tag   = s_tag;

endmodule : alu_infer_acc
