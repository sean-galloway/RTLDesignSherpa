// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_top
// Purpose: Inference ALU block at the cell's issue seam (driven by the
//          tetrad's gatling core): bf16/int8/fp32/fp8 element formats
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: alu-infer
//
// Author: sean galloway
// Created: 2026-10-17
// Updated: 2026-10-19 -- tag-based alignment (owner ruling 2026-10-18): the
//          alignment-timer mailbox becomes a tag FIFO with an arrival join;
//          ROW_LATENCY is replaced by PIPE_DEPTH (in-flight bound) and
//          ADDER_LATENCY (the adder row's own pipe depth).
// Updated: 2026-10-20 -- the PRD function-set roadmap and growth rows:
//          element formats on func_sel[8:7], reduce, PWL LUT, const, library
//          activations and conversions; MUL_LATENCY / MAC_LATENCY; EN_*
//          build-out parameters; err_opcode status pulse.
//
// Parameters:
//   - LINE_W:        line width, a multiple of 32 (default 32)
//   - PIPE_DEPTH:    tag-FIFO entries = invocations in flight, [2,16]
//   - ADDER_LATENCY: bf16/fp32 adder row pipe stages, [0,4]
//   - MUL_LATENCY:   bf16/fp32 multiplier row output stages, [0,4]
//   - MAC_LATENCY:   operand stages ahead of the accumulate stage, [0,4]
//   - TAG_W:         alignment tag width (8, owner ruling)
//   - LEAKY_SHIFT:   leaky-relu alpha = 2^-LEAKY_SHIFT
//   - EN_INT8/EN_FP32/EN_FP8: build the element format; off = illegal
//   - EN_REDUCE/EN_PWL/EN_ACT/EN_CVT: build the row family; off = illegal
// Notes:
//   - opcode 6 (compare) returns result_line = 0; the mask is on result_flags,
//     one bit per lane, packed low.
//   - err_opcode pulses on the issue edge of an illegal func_sel.  It is a
//     status output for the cell's error IRQ, not seam flow control: the
//     invocation still retires its slot with a zero line.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_top
    import alu_infer_pkg::*;
#(
    parameter int LINE_W        = 32,
    parameter int N_LANES       = LINE_W / 16,
    parameter int ACC_W         = 32,
    parameter int PIPE_DEPTH    = 8,
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

    input  logic              valid,
    output logic              ready,

    output logic              result_valid,
    input  logic              result_ready,
    output logic [LINE_W-1:0] result_line,
    output logic [LINE_W-1:0] result_flags,

    output logic              err_opcode
);

    initial begin
        if (LINE_W < 32 || (LINE_W % 32) != 0) begin
            $error("alu_infer_top: LINE_W must be a positive multiple of 32, got %0d", LINE_W);
        end
        if (PIPE_DEPTH < 2 || PIPE_DEPTH > 16) begin
            $error("alu_infer_top: PIPE_DEPTH must be in [2,16], got %0d", PIPE_DEPTH);
        end
        if (ADDER_LATENCY < 0 || ADDER_LATENCY > 4) begin
            $error("alu_infer_top: ADDER_LATENCY must be in [0,4], got %0d", ADDER_LATENCY);
        end
        if (MUL_LATENCY < 0 || MUL_LATENCY > 4) begin
            $error("alu_infer_top: MUL_LATENCY must be in [0,4], got %0d", MUL_LATENCY);
        end
        if (MAC_LATENCY < 0 || MAC_LATENCY > 4) begin
            $error("alu_infer_top: MAC_LATENCY must be in [0,4], got %0d", MAC_LATENCY);
        end
    end

    logic              issue;
    logic [TAG_W-1:0]  issue_tag;
    logic              port_valid [N_PORTS];
    logic [TAG_W-1:0]  port_tag   [N_PORTS];
    logic [LINE_W-1:0] port_data  [N_PORTS];
    logic [LINE_W-1:0] port_flags [N_PORTS];

    // Issue event is captured by the tag FIFO; rows see the same signal.
    assign issue = valid && ready;

    alu_infer_pipe #(
        .LINE_W     (LINE_W),
        .PIPE_DEPTH (PIPE_DEPTH),
        .TAG_W      (TAG_W)
    ) u_pipe (
        .clk          (clk),
        .aresetn      (aresetn),
        .issue        (issue),
        .issue_tag    (issue_tag),
        .port_valid   (port_valid),
        .port_tag     (port_tag),
        .port_data    (port_data),
        .port_flags   (port_flags),
        .ready        (ready),
        .result_valid (result_valid),
        .result_ready (result_ready),
        .result_line  (result_line),
        .result_flags (result_flags)
    );

    alu_infer_rows #(
        .LINE_W        (LINE_W),
        .ADDER_LATENCY (ADDER_LATENCY),
        .MUL_LATENCY   (MUL_LATENCY),
        .MAC_LATENCY   (MAC_LATENCY),
        .TAG_W         (TAG_W),
        .LEAKY_SHIFT   (LEAKY_SHIFT),
        .EN_INT8       (EN_INT8),
        .EN_FP32       (EN_FP32),
        .EN_FP8        (EN_FP8),
        .EN_REDUCE     (EN_REDUCE),
        .EN_PWL        (EN_PWL),
        .EN_ACT        (EN_ACT),
        .EN_CVT        (EN_CVT)
    ) u_rows (
        .clk           (clk),
        .aresetn       (aresetn),
        .op_line_a     (op_line_a),
        .op_line_b     (op_line_b),
        .threshold_imm (threshold_imm),
        .func_sel      (func_sel),
        .acc_ctrl      (acc_ctrl),
        .issue         (issue),
        .issue_tag     (issue_tag),
        .o_err         (err_opcode),
        .port_valid    (port_valid),
        .port_tag      (port_tag),
        .port_data     (port_data),
        .port_flags    (port_flags)
    );

endmodule : alu_infer_top
