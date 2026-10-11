// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_divider_restoring
// Purpose: Sequential restoring integer divider, 1 bit/cycle, DATA_WIDTH iterations
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_divider_restoring #(
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

    localparam logic [1:0] S_IDLE = 2'd0,
                           S_RUN  = 2'd1,
                           S_DONE = 2'd2;

    logic [1:0] r_state;
    logic       r_busy;
    logic       r_done;
    logic       r_dbz;

    logic [DATA_WIDTH-1:0] r_divisor;
    logic [DATA_WIDTH-1:0] r_rem;
    logic [DATA_WIDTH-1:0] r_quot;
    logic [DATA_WIDTH-1:0] r_x_shift;
    logic [COUNT_W-1:0]    r_count;

    logic [DATA_WIDTH:0]   w_t;
    logic                  w_q;
    logic [DATA_WIDTH-1:0] w_t_sub;
    logic [DATA_WIDTH-1:0] w_rem_next;

    assign ow_busy     = r_busy;
    assign ow_done     = r_done;
    assign ow_dbz      = r_dbz;
    assign ow_quotient = r_quot;
    assign ow_remainder= r_rem;

    always_comb begin
        w_t        = {r_rem, r_x_shift[DATA_WIDTH-1]};
        w_q        = (w_t >= {1'b0, r_divisor});
        w_t_sub    = DATA_WIDTH'(w_t - {1'b0, r_divisor});
        w_rem_next = w_q ? w_t_sub : w_t[DATA_WIDTH-1:0];
    end

    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state    <= S_IDLE;
            r_busy     <= 1'b0;
            r_done     <= 1'b0;
            r_dbz      <= 1'b0;
            r_divisor  <= {DATA_WIDTH{1'b0}};
            r_rem      <= {DATA_WIDTH{1'b0}};
            r_quot     <= {DATA_WIDTH{1'b0}};
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
                            r_quot     <= {DATA_WIDTH{1'b0}};
                            r_rem      <= {DATA_WIDTH{1'b0}};
                            r_state    <= S_DONE;
                        end else begin
                            r_dbz      <= 1'b0;
                            r_busy     <= 1'b1;
                            r_divisor  <= i_divisor;
                            r_rem      <= {DATA_WIDTH{1'b0}};
                            r_quot     <= {DATA_WIDTH{1'b0}};
                            r_x_shift  <= i_dividend;
                            r_count    <= COUNT_W'(DATA_WIDTH - 1);
                            r_state    <= S_RUN;
                        end
                    end
                end

                S_RUN: begin
                    r_rem     <= w_rem_next[DATA_WIDTH-1:0];
                    r_quot    <= {r_quot[DATA_WIDTH-2:0], w_q};
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

endmodule : math_divider_restoring
