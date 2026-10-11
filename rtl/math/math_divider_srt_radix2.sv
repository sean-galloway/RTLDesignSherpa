// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_divider_srt_radix2
// Purpose: SRT radix-2 integer divider, exact selection, on-the-fly Q/QM
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_divider_srt_radix2 #(
    parameter int DATA_WIDTH = 32
) (
    input  logic                    i_clk,
    input  logic                    i_rst_n,
    input  logic                    i_valid,
    output logic                    ow_busy,
    output logic                    ow_done,
    output logic                    ow_dbz,
    input  logic [DATA_WIDTH-1:0]   i_dividend,
    input  logic [DATA_WIDTH-1:0]   i_divisor,
    output logic [DATA_WIDTH-1:0]   ow_quotient,
    output logic [DATA_WIDTH-1:0]   ow_remainder
);

    localparam int COUNT_W = (DATA_WIDTH <= 1) ? 1 : $clog2(DATA_WIDTH);
    localparam logic signed [DATA_WIDTH+1:0] C_ONE = {{(DATA_WIDTH+1){1'b0}}, 1'b1};

    localparam logic [1:0] S_IDLE = 2'd0,
                           S_RUN  = 2'd1,
                           S_DONE = 2'd2;

    logic [1:0] r_state;
    logic       r_busy;
    logic       r_done;
    logic       r_dbz;

    logic [DATA_WIDTH-1:0]        r_d;
    logic signed [DATA_WIDTH+2:0] r_R;
    logic signed [DATA_WIDTH+1:0] r_Q;
    logic signed [DATA_WIDTH+1:0] r_QM;
    logic [DATA_WIDTH-1:0]        r_x_shift;
    logic [COUNT_W-1:0]           r_count;

    logic signed [DATA_WIDTH+2:0] w_t;
    logic signed [DATA_WIDTH+2:0] w_t2;
    logic signed [DATA_WIDTH+2:0] w_d_pos;
    logic signed [DATA_WIDTH+2:0] w_d_neg;
    logic signed [1:0]            w_q;
    logic signed [DATA_WIDTH+1:0] w_Q_next;
    logic signed [DATA_WIDTH+1:0] w_QM_next;
    logic signed [DATA_WIDTH-1:0] w_rem_out;

    assign ow_busy     = r_busy;
    assign ow_done     = r_done;
    assign ow_dbz      = r_dbz;
    assign ow_quotient = (r_R < 0) ? r_QM[DATA_WIDTH-1:0] : r_Q[DATA_WIDTH-1:0];
    assign ow_remainder= w_rem_out;

    always_comb begin
        w_d_pos = signed'({{3{1'b0}}, r_d});
        w_rem_out = (r_R < 0) ? DATA_WIDTH'(r_R + signed'({1'b0, r_d}))
                              : r_R[DATA_WIDTH-1:0];
        w_d_neg = -w_d_pos;
        w_t     = (r_R <<< 1) + signed'({{DATA_WIDTH+2{1'b0}}, r_x_shift[DATA_WIDTH-1]});
        w_t2    = w_t <<< 1;

        if (w_t2 >= w_d_pos)      w_q = 2'sd1;
        else if (w_t2 <= w_d_neg) w_q = -2'sd1;
        else                      w_q = 2'sd0;

        case (w_q)
            2'sd1: begin
                w_Q_next  = (r_Q <<< 1) + C_ONE;
                w_QM_next = (r_Q <<< 1);
            end
            2'sd0: begin
                w_Q_next  = (r_Q <<< 1);
                w_QM_next = (r_QM <<< 1) + C_ONE;
            end
            default: begin
                w_Q_next  = (r_QM <<< 1) + C_ONE;
                w_QM_next = (r_QM <<< 1);
            end
        endcase
    end

    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state    <= S_IDLE;
            r_busy     <= 1'b0;
            r_done     <= 1'b0;
            r_dbz      <= 1'b0;
            r_d        <= {DATA_WIDTH{1'b0}};
            r_R        <= '0;
            r_Q        <= '0;
            r_QM       <= -1;
            r_x_shift  <= {DATA_WIDTH{1'b0}};
            r_count    <= {COUNT_W{1'b0}};
        end else begin
            r_done <= 1'b0;
            case (r_state)
                S_IDLE: begin
                    if (i_valid) begin
                        if (i_divisor == {DATA_WIDTH{1'b0}}) begin
                            r_dbz      <= 1'b1;
                            r_done     <= 1'b1;
                            r_busy     <= 1'b0;
                            r_Q        <= '0;
                            r_QM       <= -1;
                            r_R        <= '0;
                            r_state    <= S_DONE;
                        end else begin
                            r_dbz      <= 1'b0;
                            r_busy     <= 1'b1;
                            r_d        <= i_divisor;
                            r_R        <= '0;
                            r_Q        <= '0;
                            r_QM       <= -1;
                            r_x_shift  <= i_dividend;
                            r_count    <= COUNT_W'(DATA_WIDTH - 1);
                            r_state    <= S_RUN;
                        end
                    end
                end

                S_RUN: begin
                    r_R       <= w_t - (w_q * signed'({1'b0, r_d}));
                    r_Q       <= w_Q_next;
                    r_QM      <= w_QM_next;
                    r_x_shift <= {r_x_shift[DATA_WIDTH-2:0], 1'b0};
                    if (r_count == {COUNT_W{1'b0}}) begin
                        r_busy  <= 1'b0;
                        r_done  <= 1'b1;
                        r_state <= S_DONE;
                    end else begin
                        r_count <= r_count - 1'b1;
                    end
                end

                S_DONE: begin
                    r_state <= S_IDLE;
                end

                default: begin
                    r_state <= S_IDLE;
                end
            endcase
        end
    )

endmodule : math_divider_srt_radix2
