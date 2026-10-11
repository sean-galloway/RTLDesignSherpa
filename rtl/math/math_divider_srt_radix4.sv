// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_divider_srt_radix4
// Purpose: Unnormalized shift-in radix-4 integer divider, digit set {-3..3}
//
// Architecture:
//   No divisor normalization / LZC / post-shift recovery.  n = ceil(W/2)
//   iterations consume the W dividend bits (plus one leading 0 for odd W).
//   Each step forms t = 4R + 2*b1 + b0.  Because the previous remainder is
//   kept bounded by |R| <= D/2, t/D lies in [-2, 2+3/D].  The digit q is the
//   nearest integer to t/D, selected by comparing 2t against the odd multiples
//   {-5D, -3D, -D, +D, +3D, +5D}.  Nearest-digit selection guarantees the new
//   remainder R = t - q*D satisfies |R| <= D/2, so the final R is already the
//   exact remainder after the last shift-in: no multiplier, no divider, no
//   while loops, only a single conditional add if R is negative.
//
//   D == 1 is special-cased: for D=1, t can reach 7 and t/D can exceed 3,
//   outside the digit set, so it returns (X,0) in one cycle.
//
//   The digit set {-3..3} is required for unnormalized radix-4: the maximum
//   |t/D| is 2 + 3/D, which is > 2.5 for every D >= 2, so the textbook
//   radix-4 set {-2..2} cannot cover the slop from shifting in two dividend
//   bits.  Radix-2 needs no normalization because its slop is only one bit,
//   keeping |t/D| < 1.5, well inside the {-1,0,+1} digit set.
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_divider_srt_radix4 #(
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

    localparam int N       = (DATA_WIDTH + 1) / 2;  // ceil(W/2)
    localparam bit EVEN_W  = (DATA_WIDTH % 2) == 0;
    localparam int COUNT_W = (N <= 1) ? 1 : $clog2(N);

    localparam logic [1:0] S_IDLE = 2'd0,
                           S_RUN  = 2'd1,
                           S_DONE = 2'd2;

    localparam logic signed [DATA_WIDTH+2:0] C_MINUS1 = -1;

    logic [1:0] r_state;
    logic       r_busy;
    logic       r_done;
    logic       r_dbz;

    logic [DATA_WIDTH-1:0]        r_divisor;
    logic signed [DATA_WIDTH+2:0] r_R;
    logic [DATA_WIDTH:0]          r_xreg;
    logic signed [DATA_WIDTH+2:0] r_Q;
    logic signed [DATA_WIDTH+2:0] r_QM;
    logic [COUNT_W-1:0]           r_count;

    logic [1:0]                   w_b;
    logic signed [DATA_WIDTH+2:0] w_t;
    logic signed [DATA_WIDTH+3:0] w_t2;
    logic signed [DATA_WIDTH+3:0] w_D;
    logic signed [DATA_WIDTH+3:0] w_3D;
    logic signed [DATA_WIDTH+3:0] w_5D;
    logic signed [2:0]            w_q;
    logic signed [DATA_WIDTH+2:0] w_qD;
    logic signed [DATA_WIDTH+2:0] w_D_r;
    logic signed [DATA_WIDTH+2:0] w_q_ext;
    logic signed [DATA_WIDTH+2:0] w_Q_next;
    logic signed [DATA_WIDTH+2:0] w_QM_next;
    logic signed [DATA_WIDTH-1:0] w_q_out;
    logic signed [DATA_WIDTH-1:0] w_r_out;

    assign ow_busy     = r_busy;
    assign ow_done     = r_done;
    assign ow_dbz      = r_dbz;
    assign ow_quotient = DATA_WIDTH'(w_q_out);
    assign ow_remainder= DATA_WIDTH'(w_r_out);

    always_comb begin
        // Two dividend bits shift in from the top of the combined register.
        w_b = r_xreg[DATA_WIDTH-:2];
        w_t = (r_R <<< 2) + signed'({{DATA_WIDTH+1{1'b0}}, w_b});

        // Exact nearest-digit selection via 2t vs odd multiples of D (W+4 signed).
        w_D  = signed'({{4{1'b0}}, r_divisor});
        w_3D = w_D + (w_D <<< 1);
        w_5D = w_D + (w_D <<< 2);
        w_t2 = {w_t, 1'b0};

        if      (w_t2 >=  w_5D) w_q = 3'sd3;
        else if (w_t2 >=  w_3D) w_q = 3'sd2;
        else if (w_t2 >=  w_D)  w_q = 3'sd1;
        else if (w_t2 >= -w_D)  w_q = 3'sd0;
        else if (w_t2 >= -w_3D) w_q = -3'sd1;
        else if (w_t2 >= -w_5D) w_q = -3'sd2;
        else                    w_q = -3'sd3;

        // R-update term q*D, W+3 signed.
        w_D_r = signed'({{3{1'b0}}, r_divisor});
        case (w_q)
            3'sd3:   w_qD =  w_D_r + (w_D_r <<< 1);
            3'sd2:   w_qD =  w_D_r <<< 1;
            3'sd1:   w_qD =  w_D_r;
            3'sd0:   w_qD = '0;
            -3'sd1:  w_qD = -w_D_r;
            -3'sd2:  w_qD = -(w_D_r <<< 1);
            default: w_qD = -(w_D_r + (w_D_r <<< 1));
        endcase

        // On-the-fly conversion, LSB-first.  The digit produced at
        // iteration k is injected at the BOTTOM of the combined register
        // (weight 4^(n-1-k)), so the first digit produced is the LEAST
        // significant pair of the quotient and Q must accumulate as
        //   Q <- 4*Q + q_k      (equivalently r_Q <<< 2, plus the sign-
        //   extended digit)
        // which holds for every digit in {-3..3}.  The canonical-minus-one
        // register follows exactly (Q - 1 only rewrites the low bits):
        //   QM <- 4*Q + q_k - 1 = Q_next - 1
        // Invariant QM == Q - 1 is maintained at every step.
        w_q_ext   = signed'({{(DATA_WIDTH){w_q[2]}}, w_q});
        w_Q_next  = (r_Q <<< 2) + w_q_ext;
        w_QM_next = w_Q_next + C_MINUS1;

        // Final remainder is already exact; one conditional add if negative.
        if (r_R < 0) begin
            w_q_out = DATA_WIDTH'(r_QM);
            w_r_out = DATA_WIDTH'(r_R + signed'({{2{1'b0}}, r_divisor}));
        end else begin
            w_q_out = DATA_WIDTH'(r_Q);
            w_r_out = DATA_WIDTH'(r_R);
        end
    end

    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state    <= S_IDLE;
            r_busy     <= 1'b0;
            r_done     <= 1'b0;
            r_dbz      <= 1'b0;
            r_divisor  <= {DATA_WIDTH{1'b0}};
            r_R        <= '0;
            r_xreg     <= {DATA_WIDTH+1{1'b0}};
            r_Q        <= '0;
            r_QM       <= -1;
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
                        end else if (i_divisor == {{(DATA_WIDTH-1){1'b0}}, 1'b1}) begin
                            // D == 1: result is (X, 0) in one cycle.
                            r_dbz      <= 1'b0;
                            r_done     <= 1'b1;
                            r_busy     <= 1'b0;
                            r_Q        <= signed'({{3{1'b0}}, i_dividend});
                            r_R        <= '0;
                            r_state    <= S_DONE;
                        end else begin
                            r_dbz      <= 1'b0;
                            r_busy     <= 1'b1;
                            r_divisor  <= i_divisor;
                            r_R        <= '0;
                            // Even W: trailing pad (top extraction starts at bit W-1);
                            // odd  W: leading pad (2N = W+1 bits are consumed).
                            r_xreg     <= EVEN_W ? {i_dividend, 1'b0} : {1'b0, i_dividend};
                            r_Q        <= '0;
                            r_QM       <= -1;
                            r_count    <= COUNT_W'(N - 1);
                            r_state    <= S_RUN;
                        end
                    end
                end

                S_RUN: begin
                    r_R    <= w_t - w_qD;
                    r_Q    <= w_Q_next;
                    r_QM   <= w_QM_next;
                    r_xreg <= {r_xreg[DATA_WIDTH-2:0], 2'b00};
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

endmodule : math_divider_srt_radix4
