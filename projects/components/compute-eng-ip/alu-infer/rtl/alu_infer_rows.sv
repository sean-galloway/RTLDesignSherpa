// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_rows
// Purpose: Seven row datapaths and func_sel decode for alu_infer_top
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_rows #(
    parameter int LINE_W     = 32,
    parameter int N_LANES    = LINE_W / 16,
    parameter int ACC_W      = 32,
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

    input  logic              issue,
    input  logic              mac_issue,
    input  logic [TAG_W-1:0]  issue_tag,

    output logic              row_write_valid,
    output logic [TAG_W-1:0]  row_write_tag,
    output logic [LINE_W-1:0] row_write_data,
    output logic [LINE_W-1:0] row_write_flags,

    // Late write path (pipelined adder result), carrying the invocation's
    // tag through the row's own pipeline so the pipe can join by tag.
    output logic              late_write_valid,
    output logic [TAG_W-1:0]  late_write_tag,
    output logic [LINE_W-1:0] late_write_data
);

    localparam logic [4:0] OPCODE_COPY  = 5'd0;
    localparam logic [4:0] OPCODE_ADD   = 5'd1;
    localparam logic [4:0] OPCODE_SUB   = 5'd2;
    localparam logic [4:0] OPCODE_MUL   = 5'd3;
    localparam logic [4:0] OPCODE_MAC   = 5'd4;
    localparam logic [4:0] OPCODE_MINMAX= 5'd5;
    localparam logic [4:0] OPCODE_CMP   = 5'd6;
    localparam logic [4:0] OPCODE_RELU  = 5'd7;

    localparam logic [1:0] ACC_CLEAR  = 2'b10;
    localparam logic [1:0] ACC_ACCUM  = 2'b01;

    initial begin
        if (ADDER_LATENCY < 0 || ADDER_LATENCY > 4) begin
            $error("alu_infer_rows: ADDER_LATENCY must be in [0,4], got %0d", ADDER_LATENCY);
        end
    end

    // Decode func_sel.
    logic [4:0] opcode;
    logic [1:0] sub_op;
    logic [1:0] reserved;

    assign opcode   = func_sel[4:0];
    assign sub_op   = func_sel[6:5];
    assign reserved = func_sel[8:7];

    // Lane decomposition: lane 0 = [15:0], lane 1 = [31:16].
    logic [15:0] a_lane [N_LANES];
    logic [15:0] b_lane [N_LANES];

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_lane_split
            assign a_lane[i] = op_line_a[i*16 +: 16];
            assign b_lane[i] = op_line_b[i*16 +: 16];
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Row results.
    // -------------------------------------------------------------------------
    logic [LINE_W-1:0] copy_result;
    logic [LINE_W-1:0] addsub_result;
    logic [LINE_W-1:0] mul_result;
    logic [LINE_W-1:0] mac_result;
    logic [LINE_W-1:0] minmax_result;
    logic [LINE_W-1:0] cmp_result;
    logic [LINE_W-1:0] cmp_flags;
    logic [LINE_W-1:0] relu_result;

    // Copy row: A passthrough.
    assign copy_result = op_line_a;

    // Adder row (sub uses sign-flipped B).
    logic [15:0] adder_result_lane [N_LANES];
    logic [15:0] adder_b_input [N_LANES];
    logic        adder_ow_valid [N_LANES];
    logic        is_addsub;

    assign is_addsub = (opcode == OPCODE_ADD) || (opcode == OPCODE_SUB);

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_adder_lane
            assign adder_b_input[i] = (opcode == OPCODE_SUB) ?
                (b_lane[i] ^ 16'h8000) : b_lane[i];

            math_bf16_adder #(
                .PIPE_STAGE_1(ADDER_LATENCY > 0 ? 1 : 0),
                .PIPE_STAGE_2(ADDER_LATENCY > 1 ? 1 : 0),
                .PIPE_STAGE_3(ADDER_LATENCY > 2 ? 1 : 0),
                .PIPE_STAGE_4(ADDER_LATENCY > 3 ? 1 : 0)
            ) u_adder (
                .i_clk      (clk),
                .i_rst_n    (aresetn),
                .i_a        (a_lane[i]),
                .i_b        (adder_b_input[i]),
                .i_valid    (issue && is_addsub),
                .ow_result  (adder_result_lane[i]),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid (),
                .ow_valid   (adder_ow_valid[i])
            );
        end
    endgenerate

    // Late-write path for the adder: carry the invocation's tag through the
    // row's pipeline so the result can join its tag group when it lands.
    logic              adder_write_valid;
    logic [TAG_W-1:0]  adder_write_tag;
    logic [LINE_W-1:0] adder_write_data;

    generate
        if (ADDER_LATENCY > 0) begin : gen_adder_shift
            logic [TAG_W-1:0] adder_tag_pipe [ADDER_LATENCY];
            logic             adder_valid_pipe [ADDER_LATENCY];

            `ALWAYS_FF_RST(clk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    for (int i = 0; i < ADDER_LATENCY; i++) begin
                        adder_tag_pipe[i]   <= '0;
                        adder_valid_pipe[i] <= 1'b0;
                    end
                end else begin
                    adder_tag_pipe[0]   <= issue_tag;
                    adder_valid_pipe[0] <= issue && is_addsub;
                    for (int i = 1; i < ADDER_LATENCY; i++) begin
                        adder_tag_pipe[i]   <= adder_tag_pipe[i-1];
                        adder_valid_pipe[i] <= adder_valid_pipe[i-1];
                    end
                end
            )

            assign adder_write_valid = adder_valid_pipe[ADDER_LATENCY-1] && adder_ow_valid[0];
            assign adder_write_tag   = adder_tag_pipe[ADDER_LATENCY-1];
        end else begin : gen_adder_no_shift
            assign adder_write_valid = issue && is_addsub && adder_ow_valid[0];
            assign adder_write_tag   = issue_tag;
        end
    endgenerate

    assign adder_write_data = {adder_result_lane[1], adder_result_lane[0]};
    assign addsub_result    = adder_write_data;

    // Multiplier row: one combinational multiplier per lane.
    logic [15:0] mul_result_lane [N_LANES];

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_mul_lane
            math_bf16_multiplier u_mul (
                .i_a        (a_lane[i]),
                .i_b        (b_lane[i]),
                .ow_result  (mul_result_lane[i]),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid ()
            );
        end
    endgenerate

    assign mul_result = {mul_result_lane[1], mul_result_lane[0]};

    // Min/max row: instantiate both and select by sub_op[0].
    logic [15:0] min_result_lane [N_LANES];
    logic [15:0] max_result_lane [N_LANES];

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_minmax_lane
            math_bf16_min u_min (
                .i_a       (a_lane[i]),
                .i_b       (b_lane[i]),
                .ow_result (min_result_lane[i])
            );
            math_bf16_max u_max (
                .i_a       (a_lane[i]),
                .i_b       (b_lane[i]),
                .ow_result (max_result_lane[i])
            );
        end
    endgenerate

    assign minmax_result = { (sub_op[0] ? max_result_lane[1] : min_result_lane[1]),
                             (sub_op[0] ? max_result_lane[0] : min_result_lane[0]) };

    // Compare row: per-lane A < B or A < threshold_imm, packed into flags.
    logic [N_LANES-1:0] cmp_lane_lt;

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_cmp_lane
            logic [15:0] cmp_b;
            logic        ow_lt;
            assign cmp_b = sub_op[0] ? threshold_imm : b_lane[i];

            math_bf16_comparator u_cmp (
                .i_a       (a_lane[i]),
                .i_b       (cmp_b),
                .ow_eq     (),
                .ow_lt     (ow_lt),
                .ow_gt     (),
                .ow_le     (),
                .ow_ge     (),
                .ow_ne     (),
                .ow_unord  ()
            );
            assign cmp_lane_lt[i] = ow_lt;
        end
    endgenerate

    assign cmp_result = '0;
    assign cmp_flags  = {{(LINE_W-N_LANES){1'b0}}, cmp_lane_lt};

    // ReLU row: per-lane on operand A.
    logic [15:0] relu_result_lane [N_LANES];

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_relu_lane
            math_bf16_relu u_relu (
                .i_a       (a_lane[i]),
                .ow_result (relu_result_lane[i])
            );
        end
    endgenerate

    assign relu_result = {relu_result_lane[1], relu_result_lane[0]};

    // MAC row: FP32 accumulator with BF16 read-back view.
    logic [LINE_W-1:0] acc_line;

    alu_infer_acc #(
        .LINE_W (LINE_W),
        .N_LANES(N_LANES),
        .ACC_W  (ACC_W)
    ) u_acc (
        .clk       (clk),
        .aresetn   (aresetn),
        .mac_issue (mac_issue),
        .acc_ctrl  (acc_ctrl),
        .a_line   (op_line_a),
        .b_line   (op_line_b),
        .acc_line (acc_line)
    );

    assign mac_result = acc_line;

    // -------------------------------------------------------------------------
    // Row select and issue-time write generation.
    // -------------------------------------------------------------------------
    logic [LINE_W-1:0] selected_result;
    logic [LINE_W-1:0] selected_flags;

    always_comb begin
        selected_result = copy_result;
        selected_flags  = '0;
        case (opcode)
            OPCODE_COPY:   selected_result = copy_result;
            OPCODE_ADD,
            OPCODE_SUB:    selected_result = addsub_result;
            OPCODE_MUL:    selected_result = mul_result;
            OPCODE_MAC:    selected_result = mac_result;
            OPCODE_MINMAX: selected_result = minmax_result;
            OPCODE_CMP:    begin selected_result = cmp_result; selected_flags = cmp_flags; end
            OPCODE_RELU:   selected_result = relu_result;
            default:       begin selected_result = '0; selected_flags = '0; end
        endcase
    end

    // Issue-time rows write at the issue edge.  The adder's late-write path
    // is a separate port pair; the pipe applies both in the same cycle.
    assign row_write_valid = issue && !is_addsub;
    assign row_write_tag   = issue_tag;
    assign row_write_data  = selected_result;
    assign row_write_flags = selected_flags;

    // Late write path: pipelined adder result, joined by tag.
    assign late_write_valid = adder_write_valid;
    assign late_write_tag   = adder_write_tag;
    assign late_write_data  = adder_write_data;

endmodule : alu_infer_rows
