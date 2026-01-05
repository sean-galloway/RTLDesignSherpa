// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_han_carlson_032
// Purpose: Han-Carlson 32-bit prefix adder for IEEE 754-2008 FP32
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/han_carlson_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_adder_han_carlson_032 #(parameter int  N = 32)(
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_cin,
    output logic [N-1:0] ow_sum,
    output logic         ow_cout
);

// Stage 0: Initial P and G computation
logic [N-1:0] w_p0, w_g0;

// P = A XOR B, G = A AND B
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_pg
        assign w_p0[i] = i_a[i] ^ i_b[i];
        assign w_g0[i] = i_a[i] & i_b[i];
    end
endgenerate

// Han-Carlson prefix tree
// Sparsity-2: compute even positions first, then fill odd positions

logic [N-1:0] w_p1, w_g1;
logic [N-1:0] w_p2, w_g2;
logic [N-1:0] w_p3, w_g3;
logic [N-1:0] w_p4, w_g4;
logic [N-1:0] w_p5, w_g5;
logic [N-1:0] w_p6, w_g6;

// Stage 1: Span-2 prefix (even positions combine with odd neighbor)
generate
    for (i = 0; i < N; i++) begin : gen_stage1
        if (i == 0) begin : gen_s1_bit0
            // Bit 0: incorporate carry-in (G[0:-1])
            assign w_g1[0] = w_g0[0] | (w_p0[0] & i_cin);
            assign w_p1[0] = w_p0[0];
        end else if (i % 2 == 0) begin : gen_s1_even
            // Even positions: G[i:i-1] = G[i] | P[i] & G[i-1]
            math_prefix_cell u_pf_s1 (
                .i_g_hi(w_g0[i]),   .i_p_hi(w_p0[i]),
                .i_g_lo(w_g0[i-1]), .i_p_lo(w_p0[i-1]),
                .ow_g(w_g1[i]),     .ow_p(w_p1[i])
            );
        end else begin : gen_s1_odd
            // Odd positions: pass through (will be filled in final stage)
            assign w_g1[i] = w_g0[i];
            assign w_p1[i] = w_p0[i];
        end
    end
endgenerate

// Stage 2: Kogge-Stone on even positions (span 4, step 2)
generate
    for (i = 0; i < N; i++) begin : gen_stage2
        if (i % 2 == 0 && i >= 2) begin : gen_s2_active
            math_prefix_cell u_pf_s2 (
                .i_g_hi(w_g1[i]),       .i_p_hi(w_p1[i]),
                .i_g_lo(w_g1[i-2]), .i_p_lo(w_p1[i-2]),
                .ow_g(w_g2[i]),           .ow_p(w_p2[i])
            );
        end else begin : gen_s2_pass
            assign w_g2[i] = w_g1[i];
            assign w_p2[i] = w_p1[i];
        end
    end
endgenerate

// Stage 3: Kogge-Stone on even positions (span 8, step 4)
generate
    for (i = 0; i < N; i++) begin : gen_stage3
        if (i % 2 == 0 && i >= 4) begin : gen_s3_active
            math_prefix_cell u_pf_s3 (
                .i_g_hi(w_g2[i]),       .i_p_hi(w_p2[i]),
                .i_g_lo(w_g2[i-4]), .i_p_lo(w_p2[i-4]),
                .ow_g(w_g3[i]),           .ow_p(w_p3[i])
            );
        end else begin : gen_s3_pass
            assign w_g3[i] = w_g2[i];
            assign w_p3[i] = w_p2[i];
        end
    end
endgenerate

// Stage 4: Kogge-Stone on even positions (span 16, step 8)
generate
    for (i = 0; i < N; i++) begin : gen_stage4
        if (i % 2 == 0 && i >= 8) begin : gen_s4_active
            math_prefix_cell u_pf_s4 (
                .i_g_hi(w_g3[i]),       .i_p_hi(w_p3[i]),
                .i_g_lo(w_g3[i-8]), .i_p_lo(w_p3[i-8]),
                .ow_g(w_g4[i]),           .ow_p(w_p4[i])
            );
        end else begin : gen_s4_pass
            assign w_g4[i] = w_g3[i];
            assign w_p4[i] = w_p3[i];
        end
    end
endgenerate

// Stage 5: Kogge-Stone on even positions (span 32, step 16)
generate
    for (i = 0; i < N; i++) begin : gen_stage5
        if (i % 2 == 0 && i >= 16) begin : gen_s5_active
            math_prefix_cell u_pf_s5 (
                .i_g_hi(w_g4[i]),       .i_p_hi(w_p4[i]),
                .i_g_lo(w_g4[i-16]), .i_p_lo(w_p4[i-16]),
                .ow_g(w_g5[i]),           .ow_p(w_p5[i])
            );
        end else begin : gen_s5_pass
            assign w_g5[i] = w_g4[i];
            assign w_p5[i] = w_p4[i];
        end
    end
endgenerate

// Stage 6: Fill odd positions (from even neighbors)
generate
    for (i = 0; i < N; i++) begin : gen_stage6
        if (i % 2 == 1) begin : gen_s6_odd
            // Odd positions: G[i:-1] = G[i] | P[i] & G[i-1:-1]
            math_prefix_cell_gray u_pf_s6 (
                .i_g_hi(w_g5[i]), .i_p_hi(w_p5[i]),
                .i_g_lo(w_g5[i-1]),
                .ow_g(w_g6[i])
            );
            assign w_p6[i] = w_p5[i];
        end else begin : gen_s6_even
            assign w_g6[i] = w_g5[i];
            assign w_p6[i] = w_p5[i];
        end
    end
endgenerate

// Final sum computation
generate
    for (i = 0; i < N; i++) begin : gen_sum
        if (i == 0) begin : gen_sum_bit0
            assign ow_sum[0] = w_p0[0] ^ i_cin;
        end else begin : gen_sum_other
            assign ow_sum[i] = w_p0[i] ^ w_g6[i-1];
        end
    end
endgenerate

// Carry out
assign ow_cout = w_g6[N-1];

endmodule
