// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_top
// Purpose: BF16 inference ALU block at the cell execution-FSM seam
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-17
// Updated: 2026-10-19 -- tag-based alignment (owner ruling 2026-10-18): the
//          alignment-timer mailbox becomes a tag FIFO with an arrival join;
//          ROW_LATENCY is replaced by PIPE_DEPTH (in-flight bound) and
//          ADDER_LATENCY (the adder row's own pipe depth).
//
// NOTE: opcode 6 (compare) returns result_line = 32'h0 by v1 decision; the mask
//       is carried on result_flags[1:0] (one bit per lane, packed low).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_top #(
    parameter int LINE_W     = 32,
    parameter int N_LANES    = LINE_W / 16,
    parameter int ACC_W      = 32,
    parameter int PIPE_DEPTH = 8,
    parameter int ADDER_LATENCY = 3,
    parameter int TAG_W      = 8
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
    output logic [LINE_W-1:0] result_flags
);

    initial begin
        if (PIPE_DEPTH < 2 || PIPE_DEPTH > 16) begin
            $error("alu_infer_top: PIPE_DEPTH must be in [2,16], got %0d", PIPE_DEPTH);
        end
        if (ADDER_LATENCY < 0 || ADDER_LATENCY > 4) begin
            $error("alu_infer_top: ADDER_LATENCY must be in [0,4], got %0d", ADDER_LATENCY);
        end
    end

    logic              issue;
    logic              mac_issue;
    logic [TAG_W-1:0]  issue_tag;
    logic [LINE_W-1:0] row_write_data;
    logic [LINE_W-1:0] row_write_flags;
    logic              row_write_valid;
    logic [TAG_W-1:0]  row_write_tag;
    logic              late_write_valid;
    logic [TAG_W-1:0]  late_write_tag;
    logic [LINE_W-1:0] late_write_data;

    // Issue event is captured by the tag FIFO; rows see the same signal.
    assign issue = valid && ready;

    // The accumulator should only update during MAC invocations; acc_ctrl is
    // otherwise reserved and must not alter the accumulator state.
    assign mac_issue = issue && (func_sel[4:0] == 5'd4);

    alu_infer_pipe #(
        .LINE_W       (LINE_W),
        .PIPE_DEPTH   (PIPE_DEPTH),
        .TAG_W        (TAG_W)
    ) u_pipe (
        .clk              (clk),
        .aresetn          (aresetn),
        .issue            (issue),
        .issue_tag        (issue_tag),
        .row_write_valid  (row_write_valid),
        .row_write_tag    (row_write_tag),
        .row_write_data   (row_write_data),
        .row_write_flags  (row_write_flags),
        .late_write_valid (late_write_valid),
        .late_write_tag   (late_write_tag),
        .late_write_data  (late_write_data),
        .ready            (ready),
        .result_valid     (result_valid),
        .result_ready     (result_ready),
        .result_line      (result_line),
        .result_flags     (result_flags)
    );

    alu_infer_rows #(
        .LINE_W        (LINE_W),
        .N_LANES       (N_LANES),
        .ACC_W         (ACC_W),
        .ADDER_LATENCY (ADDER_LATENCY),
        .TAG_W         (TAG_W)
    ) u_rows (
        .clk              (clk),
        .aresetn          (aresetn),
        .op_line_a        (op_line_a),
        .op_line_b        (op_line_b),
        .threshold_imm    (threshold_imm),
        .func_sel         (func_sel),
        .acc_ctrl         (acc_ctrl),
        .issue            (issue),
        .mac_issue        (mac_issue),
        .issue_tag        (issue_tag),
        .row_write_valid  (row_write_valid),
        .row_write_tag    (row_write_tag),
        .row_write_data   (row_write_data),
        .row_write_flags  (row_write_flags),
        .late_write_valid (late_write_valid),
        .late_write_tag   (late_write_tag),
        .late_write_data  (late_write_data)
    );

endmodule : alu_infer_top
