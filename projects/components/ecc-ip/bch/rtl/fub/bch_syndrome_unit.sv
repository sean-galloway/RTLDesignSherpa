// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_syndrome_unit
// Purpose:
//   Computes the t odd syndromes S_1, S_3, ..., S_2t-1 of a received BCH
//   codeword as the bits arrive. The even syndromes are not computed; they
//   follow from the binary BCH evenness shortcut.
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/02_syndrome_unit.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_syndrome_unit
//==============================================================================
// Description:
//   t parallel GF(2^m) Horner accumulators, one per odd syndrome root. Each
//   lane uses the imported gf_syndrome_cell (which is itself one gf_mul_const
//   and a register). Bits are embedded as GF elements {0...0, bit} in the
//   low lane, so a beat of BITS_PER_BEAT bits feeds BITS_PER_BEAT symbols.
//
//   Completion: out_valid raises on the cycle the N_BITS-th bit is accepted.
//   out_no_error decodes the syndrome registers and is stable from that point
//   until the output handshake clears the pending flag.
//
//   Throughput: one received beat per cycle while the downstream solver keeps
//   up; a block costs ceil(N_BITS / BITS_PER_BEAT) cycles.
//
//   i_clear aborts the in-flight accumulation: the bit counter and any
//   pending out_valid drop, and the next accepted beat starts a fresh block.
//   The decoder core asserts it when a framing violation (a block longer
//   than N_BITS, issue #90) makes the accumulated state meaningless; without
//   it the unit would carry the garbage count into the next block.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM:     m, the field is GF(2^m). Default 6.
//   PRIM_POLY:     primitive polynomial with bit m set. Default 0x43.
//   T_BITS:        t, correctable bit errors. Default 1.
//   N_BITS:        n, received codeword length in bits. Default 63.
//   BITS_PER_BEAT: B, bits per valid/ready beat. Default 8.
//   FIRST_ROOT:    b, first consecutive root of g(x). Default 1.
//
//==============================================================================

module bch_syndrome_unit
    import bch_pkg::*;
    import gf_pkg::*;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int BITS_PER_BEAT = bch_pkg::BITS_PER_BEAT,
    parameter int FIRST_ROOT    = bch_pkg::FIRST_ROOT
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    input  logic                  in_valid,
    output logic                  in_ready,
    input  logic [BITS_PER_BEAT-1:0] in_data,
    input  logic [BITS_PER_BEAT-1:0] in_keep,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic                  in_last,
    /* verilator lint_on UNUSEDSIGNAL */
    input  logic                  i_clear,

    output logic                  out_valid,
    input  logic                  out_ready,
    output logic [T_BITS*FIELD_DIM-1:0] out_syndromes,
    output logic                  out_no_error
);

    localparam int M  = FIELD_DIM;
    localparam int T  = T_BITS;
    localparam int N  = N_BITS;
    localparam int B  = BITS_PER_BEAT;
    localparam int CW = $clog2(B + 1);
    localparam int CNT_W = $clog2(N + B + 1);

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_syndrome_unit: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_syndrome_unit: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T < 1 || 2 * T > (1 << M) - 2)
            $error("bch_syndrome_unit: T_BITS %0d out of range for GF(2^%0d)", T, M);
        if (N < 2 * T + 1 || N > (1 << M) - 1)
            $error("bch_syndrome_unit: N_BITS %0d out of range for GF(2^%0d)", N, M);
        if (B < 1 || B > N)
            $error("bch_syndrome_unit: BITS_PER_BEAT %0d out of range 1..N (%0d)", B, N);
    end

    // -------------------------------------------------------------------------
    // Beat conversion and control
    // -------------------------------------------------------------------------
    logic [CW-1:0]    w_in_count;
    logic [B*M-1:0]   w_sym_data;
    logic             w_in_fire;
    logic [CNT_W-1:0] r_bit_count;
    logic             r_out_valid;

    assign w_in_count = CW'(bch_keep_count(64'(in_keep), B));
    assign w_in_fire  = in_valid && in_ready && (w_in_count != '0);

    // Embed each input bit as the GF element 0 or 1 in its lane
    always_comb begin
        for (int u = 0; u < B; u++) begin
            for (int k = 0; k < M; k++) begin
                if (k == 0)
                    w_sym_data[u * M + k] = in_data[u];
                else
                    w_sym_data[u * M + k] = 1'b0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Syndrome cells (one per odd root)
    // -------------------------------------------------------------------------
    for (genvar j = 0; j < T; j++) begin : g_lane
        gf_syndrome_cell #(
            .SYMBOL_WIDTH    (M),
            .PRIM_POLY       (PRIM_POLY),
            .ROOT_EXP        (bch_syndrome_root_exp(j, FIRST_ROOT)),
            .SYMBOLS_PER_BEAT(B)
        ) u_cell (
            .aclk   (aclk),
            .aresetn(aresetn),
            .i_step (w_in_fire),
            .i_first(r_bit_count == '0),
            .i_data (w_sym_data),
            .i_count(w_in_count),
            .ow_synd(out_syndromes[j * M +: M]),
            .ow_next()
        );
    end

    // -------------------------------------------------------------------------
    // Completion and no-error qualifiers
    // -------------------------------------------------------------------------
    wire w_last_bit      = (r_bit_count + CNT_W'(w_in_count) == CNT_W'(N));
    wire w_syndrome_done = w_last_bit && in_valid && in_ready;

    // Hold input while the previous block's syndromes are still pending.
    assign in_ready = (!r_out_valid || out_ready);

    assign out_no_error = (out_syndromes == '0);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_bit_count <= '0;
            r_out_valid <= 1'b0;
        end else begin
            if (i_clear) begin
                // framing abort (issue #90): the accumulated count and any
                // pending result are meaningless; start the next block clean
                r_bit_count <= '0;
                r_out_valid <= 1'b0;
            end else begin
                if (w_syndrome_done) begin
                    r_bit_count <= '0;
                    r_out_valid <= 1'b1;
                end else if (w_in_fire) begin
                    r_bit_count <= r_bit_count + CNT_W'(w_in_count);
                end
                if (r_out_valid && out_ready) begin
                    r_out_valid <= 1'b0;
                end
            end
        end
    )

    assign out_valid = r_out_valid;

endmodule : bch_syndrome_unit
