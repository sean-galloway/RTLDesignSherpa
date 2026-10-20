// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_acc
// Purpose: Per-lane FP32 accumulator bank with BF16 read-back view for MAC row
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-17
//
// NOTE: acc_ctrl encoding is 2'b00 HOLD, 2'b01 ACCUMULATE, 2'b10 CLEAR, 2'b11 DRAIN.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_acc #(
    parameter int LINE_W = 32,
    parameter int N_LANES = LINE_W / 16,
    parameter int ACC_W = 32
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic              mac_issue,
    input  logic [1:0]        acc_ctrl,
    input  logic [LINE_W-1:0] a_line,
    input  logic [LINE_W-1:0] b_line,

    output logic [LINE_W-1:0] acc_line
);

    localparam int ACC_CLEAR  = 2'b10;
    localparam int ACC_ACCUM  = 2'b01;

    // Per-lane FP32 accumulator state.
    logic [ACC_W-1:0] acc_bank [N_LANES];
    logic [ACC_W-1:0] next_acc_bank [N_LANES];
    logic [ACC_W-1:0] fma_result [N_LANES];

    // Lane-decomposed inputs.
    logic [15:0] a_lane [N_LANES];
    logic [15:0] b_lane [N_LANES];

    generate
        for (genvar i = 0; i < N_LANES; i++) begin : gen_lanes
            assign a_lane[i] = a_line[i*16 +: 16];
            assign b_lane[i] = b_line[i*16 +: 16];

            math_bf16_fma u_fma (
                .i_a        (a_lane[i]),
                .i_b        (b_lane[i]),
                .i_c        (acc_bank[i]),
                .ow_result  (fma_result[i]),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid ()
            );

            // Present the post-update accumulator so the row can capture it at
            // the same issue edge that updates the bank.
            math_fp32_to_bf16 u_view (
                .i_a         (next_acc_bank[i]),
                .ow_result   (acc_line[i*16 +: 16]),
                .ow_overflow (),
                .ow_underflow(),
                .ow_invalid  ()
            );
        end
    endgenerate

    always_comb begin
        for (int i = 0; i < N_LANES; i++) begin
            next_acc_bank[i] = acc_bank[i];
            if (mac_issue) begin
                case (acc_ctrl)
                    ACC_CLEAR: next_acc_bank[i] = 32'h00000000;
                    ACC_ACCUM: next_acc_bank[i] = fma_result[i];
                    default:   next_acc_bank[i] = acc_bank[i]; // HOLD / DRAIN
                endcase
            end
        end
    end

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < N_LANES; i++) begin
                acc_bank[i] <= '0;
            end
        end else begin
            for (int i = 0; i < N_LANES; i++) begin
                acc_bank[i] <= next_acc_bank[i];
            end
        end
    )

endmodule : alu_infer_acc
