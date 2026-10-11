// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_divider_nonrestoring
// Purpose: Sequential non-restoring integer divider, sign-based digits {+1,-1},
//          one final correction cycle
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_divider_nonrestoring #(
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
                           S_CORR = 2'd2,
                           S_DONE = 2'd3;

    logic [1:0] r_state;
    logic       r_busy;
    logic       r_done;
    logic       r_dbz;

    logic [DATA_WIDTH-1:0]       r_divisor;
    logic signed [DATA_WIDTH+1:0] r_rem;
    logic signed [DATA_WIDTH+1:0] r_qacc;
    logic [DATA_WIDTH-1:0]        r_x_shift;
    logic [COUNT_W-1:0]           r_count;

    logic signed [DATA_WIDTH+1:0] w_t;
    logic signed [1:0]            w_q;
    logic signed [DATA_WIDTH+1:0] w_q_ext;

    assign ow_busy     = r_busy;
    assign ow_done     = r_done;
    assign ow_dbz      = r_dbz;
    assign ow_quotient = r_qacc[DATA_WIDTH-1:0];
    assign ow_remainder= r_rem[DATA_WIDTH-1:0];

    always_comb begin
        w_t     = (r_rem <<< 1) + signed'({{DATA_WIDTH+1{1'b0}}, r_x_shift[DATA_WIDTH-1]});
        w_q     = (w_t >= 0) ? 2'sd1 : -2'sd1;
        w_q_ext = signed'({{DATA_WIDTH{w_q[1]}}, w_q});
    end

    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state    <= S_IDLE;
            r_busy     <= 1'b0;
            r_done     <= 1'b0;
            r_dbz      <= 1'b0;
            r_divisor  <= {DATA_WIDTH{1'b0}};
            r_rem      <= '0;
            r_qacc     <= '0;
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
                            r_qacc     <= '0;
                            r_rem      <= '0;
                            r_state    <= S_DONE;
                        end else begin
                            r_dbz      <= 1'b0;
                            r_busy     <= 1'b1;
                            r_divisor  <= i_divisor;
                            r_rem      <= '0;
                            r_qacc     <= '0;
                            r_x_shift  <= i_dividend;
                            r_count    <= COUNT_W'(DATA_WIDTH - 1);
                            r_state    <= S_RUN;
                        end
                    end
                end

                S_RUN: begin
                    r_rem     <= w_t - (w_q * signed'({1'b0, r_divisor}));
                    r_qacc    <= (r_qacc <<< 1) + w_q_ext;
                    r_x_shift <= {r_x_shift[DATA_WIDTH-2:0], 1'b0};
                    if (r_count == {COUNT_W{1'b0}}) begin
                        r_state <= S_CORR;
                    end else begin
                        r_count <= r_count - 1'b1;
                    end
                end

                S_CORR: begin
                    if (r_rem < 0) begin
                        r_rem  <= r_rem + signed'({1'b0, r_divisor});
                        r_qacc <= r_qacc - C_ONE;
                    end
                    r_busy  <= 1'b0;
                    r_done  <= 1'b1;
                    r_state <= S_DONE;
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

endmodule : math_divider_nonrestoring
