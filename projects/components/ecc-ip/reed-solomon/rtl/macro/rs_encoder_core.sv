// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_encoder_core
// Purpose:
//   Systematic Reed-Solomon encoder core: k data symbols in, n = k + 2t coded
//   symbols out, valid/ready at both ends, block boundary on `last`.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/reed_solomon_has/reed_solomon_has_index.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: rs_encoder_core
//==============================================================================
// Description:
//   HAS chapter 4.1, table 4.2. Two phases per block:
//
//   DATA:  each accepted input symbol steps the LFSR and passes straight to the
//          output (systematic code) with last = 0. `in_last` marks the k-th
//          symbol; the count is checked against k and a mismatch pulses
//          frame_err, but the block is still encoded as given.
//   DRAIN: in_ready is held low while the 2t parity symbols shift out of the
//          LFSR; the final one carries out_last = 1. The LFSR is all-zero
//          again when the drain ends, so the next block needs no clear.
//
//   A skid buffer on the output decouples the consumer's ready from the LFSR
//   step, so the encoder takes one symbol per cycle when the consumer keeps
//   up, and the 2t-cycle parity gap is the only stall it introduces (HAS 3.2).
//
//   SYMBOLS_PER_BEAT = S (DATA_WIDTH / SYMBOL_WIDTH) symbols travel per beat,
//   symbol 0 in the low lanes. in_keep says how many are present and must be
//   low-aligned and contiguous; only a block's last beat may be partial. The
//   LFSR advances by the beat's symbol count in one cycle. Data beats pass
//   through with their keep; parity follows in ceil(2t/S) beats, the final one
//   partial when S does not divide 2t. So a block's output may hold a partial
//   beat at the end of the data and another at the end of the parity; a
//   consumer that needs contiguous packing puts a beat packer at the outlet
//   (the adapters' job, HAS 4.2 / 4.3). The parity gap is ceil(2t/S) cycles.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t; 2t parity symbols per block. Default 8.
//   N_SYMBOLS:    n, codeword length; below 2^m - 1 is a shortened code.
//                 Default 2^m - 1. K_SYMBOLS = N_SYMBOLS - 2*T_SYMBOLS.
//   FIRST_ROOT:   b, first root of g(x). Default 0.
//   DATA_WIDTH:   beat width, a multiple of SYMBOL_WIDTH. Default = SYMBOL_WIDTH.
//   SKID_DEPTH:   output skid depth, 2..8. Default 2.
//
//==============================================================================

module rs_encoder_core
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int N_SYMBOLS    = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT   = 0,
    parameter int DATA_WIDTH   = SYMBOL_WIDTH,
    parameter int SKID_DEPTH   = 2,
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // data symbols in
    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic [SYMBOLS_PER_BEAT-1:0] in_keep,   // low-aligned; partial only on a block's last beat
    input  logic                        in_last,

    // coded symbols out
    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,
    output logic                        out_last,

    // one-cycle pulse: a block ended with other than k data symbols
    output logic                        frame_err
);

    localparam int M     = SYMBOL_WIDTH;
    localparam int T2    = 2 * T_SYMBOLS;
    localparam int N     = N_SYMBOLS;
    localparam int K     = K_SYMBOLS;
    localparam int S     = SYMBOLS_PER_BEAT;
    localparam int CW    = $clog2(S + 1);          // symbols in a beat, 0 .. S
    localparam int CNT_W = $clog2(N + S + 1);       // symbols accepted in the block
    localparam int PB    = (T2 + S - 1) / S;        // parity beats
    localparam int PREM  = T2 - (PB - 1) * S;       // symbols in the last parity beat
    localparam int DRN_W = $clog2(PB + 1);
    localparam int SK_W  = 1 + S + S * M;           // {last, keep, data}

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (DATA_WIDTH % M != 0)
            $error("rs_encoder_core: DATA_WIDTH %0d is not a multiple of SYMBOL_WIDTH %0d",
                   DATA_WIDTH, M);
        if (S < 1)
            $error("rs_encoder_core: SYMBOLS_PER_BEAT must be >= 1 (got %0d)", S);
        if (N > (1 << M) - 1)
            $error("rs_encoder_core: N_SYMBOLS %0d exceeds 2^%0d - 1", N, M);
        if (K < 1)
            $error("rs_encoder_core: K = N - 2t = %0d; N_SYMBOLS must exceed 2*T_SYMBOLS", K);
        if (SKID_DEPTH < 2 || SKID_DEPTH > 8)
            $error("rs_encoder_core: SKID_DEPTH must be 2..8 (got %0d)", SKID_DEPTH);
    end

    // -------------------------------------------------------------------------
    // Control state
    // -------------------------------------------------------------------------
    logic             r_drain;        // 0: DATA phase, 1: parity DRAIN
    logic [CNT_W-1:0] r_count;        // data symbols accepted in this block
    logic [DRN_W-1:0] r_drain_left;   // parity beats still to emit

    logic             w_skid_wr_valid;
    logic             w_skid_wr_ready;
    logic [SK_W-1:0]  w_skid_wr_data;
    logic [SK_W-1:0]  w_skid_rd_data;

    logic             w_in_fire;
    logic             w_drain_fire;
    logic [CW-1:0]    w_in_count;
    logic [S*M-1:0]   w_parity;
    logic [S-1:0]     w_par_keep;
    logic [S*M-1:0]   w_par_data;
    logic [CNT_W-1:0] w_count_next;

    assign in_ready     = !r_drain && w_skid_wr_ready;
    assign w_in_fire    = in_valid && in_ready;
    assign w_drain_fire = r_drain && w_skid_wr_ready;
    assign w_in_count   = CW'(gf_keep_count(64'(in_keep), S));
    assign w_count_next = r_count + CNT_W'(w_in_count);

    // -------------------------------------------------------------------------
    // LFSR
    // -------------------------------------------------------------------------
    gf_lfsr_encoder #(
        .SYMBOL_WIDTH    (M),
        .PRIM_POLY       (PRIM_POLY),
        .T_SYMBOLS       (T_SYMBOLS),
        .FIRST_ROOT      (FIRST_ROOT),
        .SYMBOLS_PER_BEAT(S)
    ) u_lfsr (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_step   (w_in_fire),
        .i_data   (in_data),
        .i_count  (w_in_count),
        .i_shift  (w_drain_fire),
        .ow_parity(w_parity)
    );

    // -------------------------------------------------------------------------
    // Output select: data beats pass through, then parity with last on the
    // final beat (partial when S does not divide 2t)
    // -------------------------------------------------------------------------
    always_comb begin
        for (int u = 0; u < S; u++) begin
            w_par_keep[u]       = (r_drain_left != DRN_W'(1)) || (u < PREM);
            w_par_data[u*M +: M] = w_par_keep[u] ? w_parity[u*M +: M] : '0;
        end
        if (r_drain) begin
            w_skid_wr_valid = 1'b1;
            w_skid_wr_data  = {(r_drain_left == DRN_W'(1)), w_par_keep, w_par_data};
        end else begin
            w_skid_wr_valid = in_valid;
            w_skid_wr_data  = {1'b0, in_keep, in_data};
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_drain      <= 1'b0;
            r_count      <= '0;
            r_drain_left <= '0;
            frame_err    <= 1'b0;
        end else begin
            frame_err <= 1'b0;
            if (w_in_fire) begin
                if (in_last) begin
                    r_drain      <= 1'b1;
                    r_drain_left <= DRN_W'(PB);
                    r_count      <= '0;
                    frame_err    <= (w_count_next != CNT_W'(K));
                end else if (r_count < CNT_W'(N)) begin
                    // a non-final beat must be full; a short one is a framing
                    // error the count check will report at the block's end
                    r_count <= w_count_next;
                end
            end else if (w_drain_fire) begin
                r_drain_left <= r_drain_left - DRN_W'(1);
                if (r_drain_left == DRN_W'(1)) r_drain <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Output skid buffer
    // -------------------------------------------------------------------------
    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_skid_buffer #(
        .DATA_WIDTH(SK_W),
        .DEPTH     (SKID_DEPTH)
    ) u_out_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_skid_wr_valid),
        .wr_ready   (w_skid_wr_ready),
        .wr_data    (w_skid_wr_data),
        .count      (),
        .rd_valid   (out_valid),
        .rd_ready   (out_ready),
        .rd_count   (),
        .rd_data    (w_skid_rd_data)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    assign {out_last, out_keep, out_data} = w_skid_rd_data;

endmodule : rs_encoder_core
