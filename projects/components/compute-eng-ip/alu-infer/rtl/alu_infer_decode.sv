// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_decode
// Purpose: func_sel legality check and result-port routing
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - An illegal invocation (unassigned opcode, a format the row does not
//     define, an unsupported conversion pair, or a feature built out by its
//     EN_* parameter) routes to the combinational port with a zero result:
//     it still retires its slot, and o_legal low raises err_opcode.

`timescale 1ns / 1ps

module alu_infer_decode
    import alu_infer_pkg::*;
#(
    parameter bit EN_INT8   = 1'b1,
    parameter bit EN_FP32   = 1'b1,
    parameter bit EN_FP8    = 1'b1,
    parameter bit EN_REDUCE = 1'b1,
    parameter bit EN_PWL    = 1'b1,
    parameter bit EN_ACT    = 1'b1,
    parameter bit EN_CVT    = 1'b1
) (
    input  logic [8:0] func_sel,
    output logic       o_legal,
    output logic [1:0] o_port
);

    logic [4:0] opcode;
    logic [1:0] sub_op;
    logic [1:0] fmt;

    assign opcode = func_sel[4:0];
    assign sub_op = func_sel[6:5];
    assign fmt    = func_sel[8:7];

    function automatic logic fmt_on(input logic [1:0] f);
        case (f)
            FMT_BF16: return 1'b1;
            FMT_INT8: return EN_INT8;
            FMT_FP32: return EN_FP32;
            default:  return EN_FP8;
        endcase
    endfunction

    // CVT pairs with a library converter (src = fmt, dst = sub_op).  The
    // same-format pair is a copy.  int8 <-> fp32/fp8 has no library block.
    function automatic logic cvt_pair_ok(input logic [1:0] src, input logic [1:0] dst);
        if (src == dst)                      return 1'b1;
        if (src == FMT_INT8 || dst == FMT_INT8)
            return (src == FMT_BF16) || (dst == FMT_BF16);
        return 1'b1;   // bf16 / fp32 / fp8 in any direction
    endfunction

    logic legal;
    logic [1:0] port;

    always_comb begin
        legal = 1'b0;
        port  = 2'(PORT_COMB);
        case (opcode)
            OP_COPY, OP_MINMAX, OP_CMP, OP_RELU, OP_CONST:
                legal = fmt_on(fmt);
            OP_ADD, OP_SUB: begin
                legal = fmt_on(fmt);
                port  = (fmt == FMT_BF16 || fmt == FMT_FP32) ? 2'(PORT_ADD) : 2'(PORT_COMB);
            end
            OP_MUL: begin
                legal = fmt_on(fmt);
                port  = (fmt == FMT_BF16 || fmt == FMT_FP32) ? 2'(PORT_MUL) : 2'(PORT_COMB);
            end
            OP_MAC: begin
                legal = fmt_on(fmt);
                port  = 2'(PORT_ACC);
            end
            OP_REDUCE: begin
                legal = EN_REDUCE && fmt_on(fmt);
                port  = 2'(PORT_ACC);
            end
            OP_PWL, OP_PWL_LUT:
                legal = EN_PWL && (fmt == FMT_BF16);
            OP_LEAKY, OP_GELU, OP_SIGMOID, OP_SILU, OP_TANH:
                legal = EN_ACT && fmt_on(fmt) && (fmt != FMT_INT8);
            OP_RECIP, OP_EXP2, OP_LOG2, OP_QSCALE:
                legal = EN_ACT && (fmt == FMT_BF16);
            OP_CVT:
                legal = EN_CVT && fmt_on(fmt) && fmt_on(sub_op) && cvt_pair_ok(fmt, sub_op);
            OP_ALTFMT:
                legal = EN_CVT && (fmt == FMT_BF16);
            default:
                legal = 1'b0;
        endcase
        if (!legal) port = 2'(PORT_COMB);
    end

    assign o_legal = legal;
    assign o_port  = port;

endmodule : alu_infer_decode
