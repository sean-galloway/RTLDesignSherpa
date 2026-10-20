// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_rows
// Purpose: The function table: decode, every row family, and the four
//          result ports (combinational, adder, multiplier, accumulator) that
//          carry each invocation's tag to the tag FIFO
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-17
// Updated: 2026-10-20 -- element formats (func_sel[8:7]), reduce, PWL LUT,
//          const, library activations, conversions; rows split per family;
//          one result port per latency class

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_rows
    import alu_infer_pkg::*;
#(
    parameter int LINE_W        = 32,
    parameter int ADDER_LATENCY = 3,
    parameter int MUL_LATENCY   = 0,
    parameter int MAC_LATENCY   = 0,
    parameter int TAG_W         = 8,
    parameter int LEAKY_SHIFT   = 4,
    parameter bit EN_INT8       = 1'b1,
    parameter bit EN_FP32       = 1'b1,
    parameter bit EN_FP8        = 1'b1,
    parameter bit EN_REDUCE     = 1'b1,
    parameter bit EN_PWL        = 1'b1,
    parameter bit EN_ACT        = 1'b1,
    parameter bit EN_CVT        = 1'b1
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic [LINE_W-1:0] op_line_a,
    input  logic [LINE_W-1:0] op_line_b,
    input  logic [15:0]       threshold_imm,
    input  logic [8:0]        func_sel,
    input  logic [1:0]        acc_ctrl,

    input  logic              issue,
    input  logic [TAG_W-1:0]  issue_tag,

    output logic              o_err,          // issue of an illegal func_sel

    output logic              port_valid [N_PORTS],
    output logic [TAG_W-1:0]  port_tag   [N_PORTS],
    output logic [LINE_W-1:0] port_data  [N_PORTS],
    output logic [LINE_W-1:0] port_flags [N_PORTS]
);

    logic [4:0] opcode;
    logic [1:0] sub_op;
    logic [1:0] fmt;

    assign opcode = func_sel[4:0];
    assign sub_op = func_sel[6:5];
    assign fmt    = func_sel[8:7];

    // ------------------------------------------------------------------
    // Decode
    // ------------------------------------------------------------------
    logic       legal;
    logic [1:0] port;

    alu_infer_decode #(
        .EN_INT8(EN_INT8), .EN_FP32(EN_FP32), .EN_FP8(EN_FP8),
        .EN_REDUCE(EN_REDUCE), .EN_PWL(EN_PWL), .EN_ACT(EN_ACT), .EN_CVT(EN_CVT)
    ) u_decode (
        .func_sel (func_sel),
        .o_legal  (legal),
        .o_port   (port)
    );

    assign o_err = issue && !legal;

    logic go_comb, go_add, go_mul, go_acc;
    assign go_comb = issue && (port == 2'(PORT_COMB));
    assign go_add  = issue && (port == 2'(PORT_ADD));
    assign go_mul  = issue && (port == 2'(PORT_MUL));
    assign go_acc  = issue && (port == 2'(PORT_ACC));

    // ------------------------------------------------------------------
    // Row families
    // ------------------------------------------------------------------
    logic [LINE_W-1:0] bf16_comb, bf16_flags, bf16_add, bf16_mul;
    logic [LINE_W-1:0] int8_comb, int8_flags;
    logic [LINE_W-1:0] fp32_comb, fp32_flags, fp32_add, fp32_mul;
    logic [LINE_W-1:0] fp8_comb,  fp8_flags;
    logic [LINE_W-1:0] act_line, pwl_line, cvt_line;
    logic [31:0]       lut_rdata;

    alu_infer_bf16_rows #(.LINE_W(LINE_W), .ADDER_LATENCY(ADDER_LATENCY)) u_bf16 (
        .clk       (clk),
        .aresetn   (aresetn),
        .a_line    (op_line_a),
        .b_line    (op_line_b),
        .imm       (threshold_imm),
        .opcode    (opcode),
        .sub_op    (sub_op),
        .add_issue (go_add && (fmt == FMT_BF16)),
        .o_comb    (bf16_comb),
        .o_flags   (bf16_flags),
        .o_add     (bf16_add),
        .o_mul     (bf16_mul)
    );

    generate
        if (EN_INT8) begin : gen_int8
            alu_infer_int8_rows #(.LINE_W(LINE_W)) u_int8 (
                .a_line (op_line_a), .b_line(op_line_b), .imm(threshold_imm),
                .opcode (opcode), .sub_op(sub_op),
                .o_comb (int8_comb), .o_flags(int8_flags));
        end else begin : gen_no_int8
            assign int8_comb  = '0;
            assign int8_flags = '0;
        end

        if (EN_FP32) begin : gen_fp32
            alu_infer_fp32_rows #(.LINE_W(LINE_W), .ADDER_LATENCY(ADDER_LATENCY)) u_fp32 (
                .clk       (clk),
                .aresetn   (aresetn),
                .a_line    (op_line_a),
                .b_line    (op_line_b),
                .imm       (threshold_imm),
                .opcode    (opcode),
                .sub_op    (sub_op),
                .add_issue (go_add && (fmt == FMT_FP32)),
                .o_comb    (fp32_comb),
                .o_flags   (fp32_flags),
                .o_add     (fp32_add),
                .o_mul     (fp32_mul));
        end else begin : gen_no_fp32
            assign fp32_comb  = '0;
            assign fp32_flags = '0;
            assign fp32_add   = '0;
            assign fp32_mul   = '0;
        end

        if (EN_FP8) begin : gen_fp8
            alu_infer_fp8_rows #(.LINE_W(LINE_W)) u_fp8 (
                .a_line (op_line_a), .b_line(op_line_b), .imm(threshold_imm),
                .opcode (opcode), .sub_op(sub_op),
                .o_comb (fp8_comb), .o_flags(fp8_flags));
        end else begin : gen_no_fp8
            assign fp8_comb  = '0;
            assign fp8_flags = '0;
        end

        if (EN_ACT) begin : gen_act
            alu_infer_act_rows #(
                .LINE_W(LINE_W), .LEAKY_SHIFT(LEAKY_SHIFT),
                .EN_FP32(EN_FP32), .EN_FP8(EN_FP8)
            ) u_act (
                .a_line (op_line_a), .opcode(opcode), .fmt(fmt), .o_line(act_line));
        end else begin : gen_no_act
            assign act_line = '0;
        end

        if (EN_PWL) begin : gen_pwl
            alu_infer_pwl #(.LINE_W(LINE_W)) u_pwl (
                .clk       (clk),
                .lut_we    (go_comb && legal && (opcode == OP_PWL_LUT) && !sub_op[0]),
                .lut_waddr (op_line_b[7:0]),
                .lut_wdata (op_line_a[31:0]),
                .lut_raddr (op_line_b[7:0]),
                .lut_rdata (lut_rdata),
                .a_line    (op_line_a),
                .o_line    (pwl_line));
        end else begin : gen_no_pwl
            assign pwl_line  = '0;
            assign lut_rdata = '0;
        end

        if (EN_CVT) begin : gen_cvt
            alu_infer_cvt #(
                .LINE_W(LINE_W), .EN_INT8(EN_INT8), .EN_FP32(EN_FP32), .EN_FP8(EN_FP8)
            ) u_cvt (
                .a_line (op_line_a), .b_line(op_line_b), .imm(threshold_imm),
                .opcode (opcode), .src(fmt), .dst(sub_op), .o_line(cvt_line));
        end else begin : gen_no_cvt
            assign cvt_line = '0;
        end
    endgenerate

    // ------------------------------------------------------------------
    // Port 0: combinational rows, written at the issue edge.
    // ------------------------------------------------------------------
    logic [LINE_W-1:0] comb_data, comb_flags;

    always_comb begin
        comb_data  = '0;
        comb_flags = '0;
        if (legal) begin
            case (opcode)
                OP_PWL:             comb_data = pwl_line;
                OP_PWL_LUT:         comb_data = sub_op[0] ? LINE_W'(lut_rdata) : '0;
                OP_LEAKY, OP_GELU, OP_SIGMOID, OP_SILU, OP_TANH,
                OP_RECIP, OP_EXP2, OP_LOG2, OP_QSCALE:
                                    comb_data = act_line;
                OP_CVT, OP_ALTFMT:  comb_data = cvt_line;
                default: begin
                    case (fmt)
                        FMT_INT8: begin comb_data = int8_comb; comb_flags = int8_flags; end
                        FMT_FP32: begin comb_data = fp32_comb; comb_flags = fp32_flags; end
                        FMT_FP8:  begin comb_data = fp8_comb;  comb_flags = fp8_flags;  end
                        default:  begin comb_data = bf16_comb; comb_flags = bf16_flags; end
                    endcase
                    if (opcode != OP_CMP) comb_flags = '0;
                end
            endcase
        end
    end

    assign port_valid[PORT_COMB] = go_comb;
    assign port_tag[PORT_COMB]   = issue_tag;
    assign port_data[PORT_COMB]  = comb_data;
    assign port_flags[PORT_COMB] = comb_flags;

    // ------------------------------------------------------------------
    // Port 1: adders (bf16 / fp32), ADDER_LATENCY after issue.  The library
    // adders carry the data; this line carries the tag and format alongside.
    // ------------------------------------------------------------------
    logic       add_v;
    logic [1:0] add_fmt;

    alu_infer_delay #(.W(TAG_W + 2), .DEPTH(ADDER_LATENCY)) u_add_tag (
        .clk     (clk),
        .aresetn (aresetn),
        .i_valid (go_add),
        .i_data  ({issue_tag, fmt}),
        .o_valid (add_v),
        .o_data  ({port_tag[PORT_ADD], add_fmt})
    );

    assign port_valid[PORT_ADD] = add_v;
    assign port_data[PORT_ADD]  = (add_fmt == FMT_FP32) ? fp32_add : bf16_add;
    assign port_flags[PORT_ADD] = '0;

    // ------------------------------------------------------------------
    // Port 2: multipliers (bf16 / fp32), MUL_LATENCY after issue.
    // ------------------------------------------------------------------
    alu_infer_delay #(.W(TAG_W + LINE_W), .DEPTH(MUL_LATENCY)) u_mul_pipe (
        .clk     (clk),
        .aresetn (aresetn),
        .i_valid (go_mul),
        .i_data  ({issue_tag, (fmt == FMT_FP32) ? fp32_mul : bf16_mul}),
        .o_valid (port_valid[PORT_MUL]),
        .o_data  ({port_tag[PORT_MUL], port_data[PORT_MUL]})
    );

    assign port_flags[PORT_MUL] = '0;

    // ------------------------------------------------------------------
    // Port 3: MAC / REDUCE, MAC_LATENCY after issue.
    // ------------------------------------------------------------------
    alu_infer_acc #(
        .LINE_W(LINE_W), .MAC_LATENCY(MAC_LATENCY), .TAG_W(TAG_W),
        .EN_INT8(EN_INT8), .EN_FP32(EN_FP32), .EN_FP8(EN_FP8)
    ) u_acc (
        .clk       (clk),
        .aresetn   (aresetn),
        .acc_issue (go_acc),
        .issue_tag (issue_tag),
        .a_line    (op_line_a),
        .b_line    (op_line_b),
        .imm       (threshold_imm),
        .func_sel  (func_sel),
        .acc_ctrl  (acc_ctrl),
        .o_valid   (port_valid[PORT_ACC]),
        .o_tag     (port_tag[PORT_ACC]),
        .o_line    (port_data[PORT_ACC])
    );

    assign port_flags[PORT_ACC] = '0;

endmodule : alu_infer_rows
