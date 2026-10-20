// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_pkg
// Purpose: Opcode, element-format, accumulator-control and result-port
//          encodings shared by every alu_infer_* module
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-20

`timescale 1ns / 1ps

package alu_infer_pkg;

    // ------------------------------------------------------------------
    // func_sel = {fmt[8:7], sub_op[6:5], opcode[4:0]}
    // ------------------------------------------------------------------
    localparam logic [4:0] OP_COPY    = 5'd0;
    localparam logic [4:0] OP_ADD     = 5'd1;
    localparam logic [4:0] OP_SUB     = 5'd2;
    localparam logic [4:0] OP_MUL     = 5'd3;
    localparam logic [4:0] OP_MAC     = 5'd4;
    localparam logic [4:0] OP_MINMAX  = 5'd5;   // sub_op[0]: 0 min, 1 max
    localparam logic [4:0] OP_CMP     = 5'd6;   // sub_op[0]: 0 vs B, 1 vs imm
    localparam logic [4:0] OP_RELU    = 5'd7;
    localparam logic [4:0] OP_REDUCE  = 5'd8;   // sub_op[0]: 0 sum, 1 max; sub_op[1]: cross-lane fold
    localparam logic [4:0] OP_PWL     = 5'd9;   // LUT piecewise-linear activation
    localparam logic [4:0] OP_PWL_LUT = 5'd10;  // sub_op[0]: 0 write entry, 1 read entry
    localparam logic [4:0] OP_CONST   = 5'd11;  // broadcast threshold_imm
    localparam logic [4:0] OP_LEAKY   = 5'd12;
    localparam logic [4:0] OP_GELU    = 5'd13;
    localparam logic [4:0] OP_SIGMOID = 5'd14;
    localparam logic [4:0] OP_SILU    = 5'd15;
    localparam logic [4:0] OP_TANH    = 5'd16;
    localparam logic [4:0] OP_RECIP   = 5'd17;
    localparam logic [4:0] OP_EXP2    = 5'd18;
    localparam logic [4:0] OP_LOG2    = 5'd19;
    localparam logic [4:0] OP_QSCALE  = 5'd20;  // log2 quantization scale of a max value
    localparam logic [4:0] OP_CVT     = 5'd21;  // src format = fmt, dst format = sub_op
    localparam logic [4:0] OP_ALTFMT  = 5'd22;  // bf16 <-> fp16 / fp8-e5m2 conversions

    // Element formats (func_sel[8:7]); a 32-bit line holds 2, 4, 1, 4 lanes.
    localparam logic [1:0] FMT_BF16 = 2'd0;
    localparam logic [1:0] FMT_INT8 = 2'd1;
    localparam logic [1:0] FMT_FP32 = 2'd2;
    localparam logic [1:0] FMT_FP8  = 2'd3;   // e4m3

    // OP_ALTFMT sub-ops (bf16 source/destination only).
    localparam logic [1:0] ALT_BF16_TO_FP16 = 2'd0;
    localparam logic [1:0] ALT_FP16_TO_BF16 = 2'd1;
    localparam logic [1:0] ALT_BF16_TO_E5M2 = 2'd2;
    localparam logic [1:0] ALT_E5M2_TO_BF16 = 2'd3;

    // acc_ctrl (MAC and REDUCE invocations only).
    localparam logic [1:0] ACC_HOLD  = 2'b00;
    localparam logic [1:0] ACC_ACCUM = 2'b01;
    localparam logic [1:0] ACC_CLEAR = 2'b10;
    localparam logic [1:0] ACC_DRAIN = 2'b11;

    // Result ports into the tag FIFO: each carries its rows' natural latency.
    localparam int N_PORTS   = 4;
    localparam int PORT_COMB = 0;   // combinational rows, land at the issue edge
    localparam int PORT_ADD  = 1;   // bf16/fp32 adders, ADDER_LATENCY
    localparam int PORT_MUL  = 2;   // bf16/fp32 multipliers, MUL_LATENCY
    localparam int PORT_ACC  = 3;   // MAC/REDUCE accumulate stage, MAC_LATENCY

    localparam logic [15:0] BF16_ONE  = 16'h3F80;
    localparam logic [31:0] FP32_ONE  = 32'h3F80_0000;
    localparam logic [31:0] FP32_NINF = 32'hFF80_0000;
    localparam logic [31:0] ACC_INT_MIN = 32'h8000_0000;

endpackage : alu_infer_pkg
