// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_decoder_core
// Purpose:
//   Reed-Solomon decoder core: n received symbols in, k corrected data
//   symbols out with a per-block verdict on the last one, valid/ready at
//   both ends, block boundary on `last`.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/reed_solomon_has/reed_solomon_has_index.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: rs_decoder_core
//==============================================================================
// Description:
//   HAS chapter 4.1, table 4.3. Three stages joined by descriptor buffers, so
//   a block is received while the previous one is solved and the one before
//   that is corrected:
//
//   A  receive   every accepted symbol goes into the block FIFO and through
//                the syndrome unit. On the block's last symbol a descriptor
//                {length, frame_err, all_zero, syndromes} is pushed to B. A
//                block that reaches the FIFO's depth without a last is ended
//                there with frame_err, so a runaway stream cannot deadlock the
//                core; it resynchronises on the next in_last.
//   B  solve     a clean or mis-framed block bypasses the solver; otherwise
//                the riBM solver runs 2t cycles and {Lambda, Omega, degree}
//                join the descriptor on the way to C.
//   C  correct   loads Chien and Forney, then walks the block's beats one per
//                cycle reading the FIFO (C1: Chien lanes, Forney values, hit
//                count) into a pipeline register; from that register (C2) every
//                corrected symbol, data and parity, is fed to a second syndrome
//                unit and the data beats are pushed to the output FIFO. The
//                register exists because Chien registers -> lane sums -> gf_inv
//                -> gf_mul -> re-check chain -> status was 24 logic levels on
//                the Nexys A7 harness.
//   C3 verdict   one more cycle, so the status write reads the re-check's
//                REGISTERED all-zero output rather than its combinational
//                next-value. That ends the S-fold Horner chain at the syndrome
//                cells' own flops instead of carrying it into the verdict and
//                the status FIFO: 16 levels, and the last thing holding this
//                design off 100 MHz on an Artix-7 -1. Costs one cycle per
//                block. On the last beat the verdict is final:
//                  uncorrectable = deg > t | deg == 0 | roots != deg
//                                | zero derivative at a root
//                                | re-computed syndromes not all zero
//                and is pushed to the status FIFO.
//   out          the output FIFO holds {received symbol, correction, hit} for
//                every data position and releases a block only once its
//                verdict exists; the correction is applied on the way out and
//                only when the block is not uncorrectable, so an uncorrectable
//                block leaves exactly as it arrived. The status ports are
//                valid throughout the block and out_last marks its k-th
//                symbol. Parity positions are walked but never emitted.
//
//   The re-check is what makes "never silently pass a failed block" true: a
//   block with more than t errors can yield a locator of degree d <= t with
//   exactly d roots whose "correction" is not a codeword; the degree and
//   root-count checks pass it, the re-computed syndromes do not
//   (dv/tbclasses/rs_model.py, RS(15,11), three errors).
//
//   A mis-framed block (length != n, or a partial beat before the last) is
//   passed through uncorrected with frame_err: its first length - 2t symbols
//   are emitted as data (all of them when length <= 2t).
//
//   SYMBOLS_PER_BEAT = S symbols travel per beat, symbol 0 in the low lanes,
//   in_keep low-aligned and partial only on a block's last beat. Every stage
//   works a beat per cycle: the syndrome cells take S Horner steps, the Chien
//   and Forney cells evaluate S positions (S inverses), the re-check takes S
//   steps, and the output FIFO holds beats. The output beat holding the last
//   data position also holds the first parity positions; its keep marks the
//   data lanes only, so the emitted block is k symbols in ceil(k/S) beats with
//   a partial final beat when S does not divide k.
//
//   KES_ALGO picks the solver; nothing else changes except the Forney block's
//   evaluator-form constant, which follows it.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH, PRIM_POLY, T_SYMBOLS, N_SYMBOLS, FIRST_ROOT, DATA_WIDTH,
//   SKID_DEPTH: as rs_encoder_core.
//   BLOCK_FIFO_DEPTH: symbols the block FIFO holds; power of two, default the
//                first power of two at or above n + 2t + 8 (HAS 5.2).
//
//==============================================================================

module rs_decoder_core
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int PRIM_POLY        = 'h11D,
    parameter int T_SYMBOLS        = 8,
    parameter int N_SYMBOLS        = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT       = 0,
    parameter int DATA_WIDTH       = SYMBOL_WIDTH,
    parameter int SKID_DEPTH       = 2,
    // beats the block FIFO holds: a block plus the next one's arrival during the
    // solve, rounded up to a power of two (HAS 5.2)
    parameter int BLOCK_FIFO_DEPTH = 1 << $clog2((N_SYMBOLS + 2 * T_SYMBOLS) / (DATA_WIDTH / SYMBOL_WIDTH) + 8),
    parameter string KES_ALGO      = "RIBM",   // "RIBM" or "EUCLID" (PRD D11)
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH,
    parameter int STATUS_CNT_WIDTH = $clog2(T_SYMBOLS + 1)
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // received symbols in
    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic [SYMBOLS_PER_BEAT-1:0] in_keep,   // low-aligned; partial only on a block's last beat
    input  logic                        in_last,

    // corrected data symbols out
    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,
    output logic                        out_last,

    // block verdict, valid with out_last
    output logic                        out_status_ok,
    output logic [STATUS_CNT_WIDTH-1:0] out_status_corrected,
    output logic                        out_status_uncorrectable,
    output logic                        out_status_frame_err
);

    localparam int M     = SYMBOL_WIDTH;
    localparam int T     = T_SYMBOLS;
    localparam int T2    = 2 * T;
    localparam int N     = N_SYMBOLS;
    localparam int S     = SYMBOLS_PER_BEAT;
    localparam int CW    = $clog2(S + 1);            // symbols in a beat, 0 .. S
    localparam int BFD   = BLOCK_FIFO_DEPTH;          // beats
    localparam int CNT_W = $clog2(BFD * S + 1);       // symbols in a block
    localparam int BCW   = $clog2(BFD + 1);           // beats in a block
    localparam int DEG_W = $clog2(T2 + 1);
    localparam int SC_W  = STATUS_CNT_WIDTH;
    localparam int KB    = (K_SYMBOLS + S - 1) / S;   // data beats per block
    localparam int OFD   = 1 << $clog2(2 * KB + 8);   // output FIFO depth, beats

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (DATA_WIDTH % M != 0)
            $error("rs_decoder_core: DATA_WIDTH %0d is not a multiple of SYMBOL_WIDTH %0d",
                   DATA_WIDTH, M);
        if (S < 1)
            $error("rs_decoder_core: SYMBOLS_PER_BEAT must be >= 1 (got %0d)", S);
        if (N > (1 << M) - 1)
            $error("rs_decoder_core: N_SYMBOLS %0d exceeds 2^%0d - 1", N, M);
        if (K_SYMBOLS < 1)
            $error("rs_decoder_core: K = N - 2t = %0d; N_SYMBOLS must exceed 2*T_SYMBOLS", K_SYMBOLS);
        if (BFD * S < N + 1 || (BFD & (BFD - 1)) != 0)
            $error("rs_decoder_core: BLOCK_FIFO_DEPTH %0d beats must be a power of two holding more than N symbols", BFD);
        if (SKID_DEPTH < 2 || SKID_DEPTH > 8)
            $error("rs_decoder_core: SKID_DEPTH must be 2..8 (got %0d)", SKID_DEPTH);
        if (KES_ALGO != "RIBM" && KES_ALGO != "EUCLID")
            $error("rs_decoder_core: KES_ALGO must be \"RIBM\" or \"EUCLID\" (got %s)", KES_ALGO);
    end

    // =========================================================================
    // Stage A: receive
    // =========================================================================
    logic             w_in_fire;
    logic             w_blk_wr_ready;
    logic             r_first;             // next accepted beat starts a block
    logic [CNT_W-1:0] r_rx_count;          // symbols accepted so far in this block
    logic [BCW-1:0]   r_rx_beats;          // beats accepted so far in this block
    logic             r_rx_partial;        // a non-final beat was partial
    logic             w_force_end;         // the FIFO would overflow: end the block here
    logic             w_block_end;
    logic [CW-1:0]    w_in_count;
    logic [CNT_W-1:0] w_len;
    logic             w_frame_err;

    logic [T2*M-1:0]  w_synd;
    logic [T2*M-1:0]  w_synd_next;
    logic             w_all_zero_next;

    // A -> B descriptor: {len, frame_err, all_zero, synd}
    localparam int DAB_W = CNT_W + 2 + T2 * M;
    logic             w_dab_wr_valid, w_dab_wr_ready, w_dab_rd_valid, w_dab_rd_ready;
    logic [DAB_W-1:0] w_dab_wr_data, w_dab_rd_data;

    assign w_in_count  = CW'(gf_keep_count(64'(in_keep), S));
    assign w_force_end = (r_rx_beats == BCW'(BFD - 1));
    assign w_block_end = in_last || w_force_end;
    assign w_len       = r_rx_count + CNT_W'(w_in_count);
    assign w_frame_err = (w_len != CNT_W'(N)) || r_rx_partial || w_force_end;
    assign in_ready    = w_blk_wr_ready && w_dab_wr_ready;
    assign w_in_fire   = in_valid && in_ready;

    /* verilator lint_off PINCONNECTEMPTY */
    syndrome_unit #(
        .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T), .FIRST_ROOT(FIRST_ROOT),
        .SYMBOLS_PER_BEAT(S)
    ) u_synd (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_step          (w_in_fire),
        .i_first         (r_first),
        .i_data          (in_data),
        .i_count         (w_in_count),
        .ow_synd         (w_synd),
        .ow_all_zero     (),
        .ow_synd_next    (w_synd_next),
        .ow_all_zero_next(w_all_zero_next)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    assign w_dab_wr_valid = w_in_fire && w_block_end;
    assign w_dab_wr_data  = {w_len, w_frame_err, w_all_zero_next, w_synd_next};

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_first      <= 1'b1;
            r_rx_count   <= '0;
            r_rx_beats   <= '0;
            r_rx_partial <= 1'b0;
        end else if (w_in_fire) begin
            r_first      <= w_block_end;
            r_rx_count   <= w_block_end ? '0 : w_len;
            r_rx_beats   <= w_block_end ? '0 : r_rx_beats + BCW'(1);
            r_rx_partial <= w_block_end ? 1'b0 : (r_rx_partial || (w_in_count != CW'(S)));
        end
    )

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_skid_buffer #(.DATA_WIDTH(DAB_W), .DEPTH(2)) u_desc_ab (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_dab_wr_valid), .wr_ready(w_dab_wr_ready), .wr_data(w_dab_wr_data),
        .count(), .rd_valid(w_dab_rd_valid), .rd_ready(w_dab_rd_ready), .rd_count(),
        .rd_data(w_dab_rd_data));
    /* verilator lint_on PINCONNECTEMPTY */

    // -------------------------------------------------------------------------
    // Block FIFO: every received beat {keep, data}, read back by stage C
    // -------------------------------------------------------------------------
    localparam int BF_W = S + S * M;
    logic            w_blk_rd_valid, w_blk_rd_ready;
    logic [BF_W-1:0] w_blk_rd_data;
    logic [S-1:0]    w_blk_rd_keep;
    logic [S*M-1:0]  w_blk_rd_sym;

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_fifo_sync #(.DATA_WIDTH(BF_W), .DEPTH(BFD), .REGISTERED(0)) u_blk_fifo (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_in_fire), .wr_ready(w_blk_wr_ready), .wr_data({in_keep, in_data}),
        .rd_ready(w_blk_rd_ready), .count(), .rd_valid(w_blk_rd_valid), .rd_data(w_blk_rd_data));
    /* verilator lint_on PINCONNECTEMPTY */

    assign {w_blk_rd_keep, w_blk_rd_sym} = w_blk_rd_data;

    // =========================================================================
    // Stage B: solve
    // =========================================================================
    logic [CNT_W-1:0] w_b_len;
    logic             w_b_frame_err, w_b_all_zero;
    logic [T2*M-1:0]  w_b_synd;
    assign {w_b_len, w_b_frame_err, w_b_all_zero, w_b_synd} = w_dab_rd_data;

    logic                 w_kes_start, w_kes_busy, w_kes_done, w_kes_deg_err;
    logic [(T2+1)*M-1:0]  w_kes_lambda;
    logic [T*M-1:0]       w_kes_omega;
    logic [DEG_W-1:0]     w_kes_deg;

    localparam bit KES_EUCLID = (KES_ALGO == "EUCLID");

    if (KES_EUCLID) begin : g_kes_euclid
        key_equation_solver_euclid #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T)) u_kes (
            .aclk(aclk), .aresetn(aresetn),
            .i_start(w_kes_start), .i_synd(w_b_synd),
            .o_busy(w_kes_busy), .o_done(w_kes_done),
            .o_lambda(w_kes_lambda), .o_omega(w_kes_omega), .o_deg(w_kes_deg), .o_deg_err(w_kes_deg_err));
    end else begin : g_kes_ribm
        key_equation_solver_ribm #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T)) u_kes (
            .aclk(aclk), .aresetn(aresetn),
            .i_start(w_kes_start), .i_synd(w_b_synd),
            .o_busy(w_kes_busy), .o_done(w_kes_done),
            .o_lambda(w_kes_lambda), .o_omega(w_kes_omega), .o_deg(w_kes_deg), .o_deg_err(w_kes_deg_err));
    end

    // B -> C descriptor: {len, frame_err, all_zero, correct, bad, deg, lambda[0..t], omega}
    localparam int DBC_W = CNT_W + 4 + DEG_W + (T + 1) * M + T * M;
    logic             w_dbc_wr_valid, w_dbc_wr_ready, w_dbc_rd_valid, w_dbc_rd_ready;
    logic [DBC_W-1:0] w_dbc_wr_data, w_dbc_rd_data;

    typedef enum logic [1:0] {B_IDLE, B_SOLVE, B_PUSH} b_state_t;
    b_state_t         r_b_state;
    logic [CNT_W-1:0] r_b_len;
    logic             w_b_bypass;
    logic             w_b_bad;             // solver says more than t errors, or nothing located

    assign w_b_bypass  = w_b_all_zero || w_b_frame_err;
    assign w_b_bad     = w_kes_deg_err || (w_kes_deg == '0);
    assign w_kes_start = (r_b_state == B_IDLE) && w_dab_rd_valid && !w_b_bypass;
    assign w_dab_rd_ready = (r_b_state == B_IDLE) && (w_b_bypass ? w_dbc_wr_ready : 1'b1);

    always_comb begin
        if (r_b_state == B_PUSH) begin
            w_dbc_wr_valid = 1'b1;
            w_dbc_wr_data  = {r_b_len, 1'b0, 1'b0, 1'b1, w_b_bad, w_kes_deg,
                              w_kes_lambda[(T+1)*M-1:0], w_kes_omega};
        end else begin
            w_dbc_wr_valid = (r_b_state == B_IDLE) && w_dab_rd_valid && w_b_bypass;
            w_dbc_wr_data  = {w_b_len, w_b_frame_err, w_b_all_zero, 1'b0, 1'b0, DEG_W'(0),
                              {((T + 1) * M){1'b0}}, {(T * M){1'b0}}};
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_state <= B_IDLE;
            r_b_len   <= '0;
        end else begin
            case (r_b_state)
                B_IDLE: if (w_kes_start) begin
                    r_b_state <= B_SOLVE;
                    r_b_len   <= w_b_len;
                end
                B_SOLVE: if (w_kes_done) r_b_state <= B_PUSH;
                B_PUSH:  if (w_dbc_wr_ready) r_b_state <= B_IDLE;
                default: r_b_state <= B_IDLE;
            endcase
        end
    )

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_skid_buffer #(.DATA_WIDTH(DBC_W), .DEPTH(2)) u_desc_bc (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_dbc_wr_valid), .wr_ready(w_dbc_wr_ready), .wr_data(w_dbc_wr_data),
        .count(), .rd_valid(w_dbc_rd_valid), .rd_ready(w_dbc_rd_ready), .rd_count(),
        .rd_data(w_dbc_rd_data));
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Stage C: correct and drain, a beat per cycle
    // =========================================================================
    logic [CNT_W-1:0]    w_c_len;
    logic                w_c_frame_err, w_c_all_zero, w_c_correct, w_c_bad;
    logic [DEG_W-1:0]    w_c_deg;
    logic [(T+1)*M-1:0]  w_c_lambda;
    logic [T*M-1:0]      w_c_omega;
    assign {w_c_len, w_c_frame_err, w_c_all_zero, w_c_correct, w_c_bad, w_c_deg, w_c_lambda, w_c_omega}
        = w_dbc_rd_data;

    typedef enum logic [1:0] {C_IDLE, C_WALK} c_state_t;
    c_state_t         r_c_state;
    logic [CNT_W-1:0] r_c_len;             // symbols in the block
    logic [CNT_W-1:0] r_c_pos;             // first position of the beat being processed
    logic [CNT_W-1:0] r_c_data_len;        // positions emitted as data
    logic             r_c_frame_err, r_c_all_zero, r_c_correct, r_c_bad;
    logic [DEG_W-1:0] r_c_deg;
    logic [SC_W:0]    r_c_roots;           // one wider than the count: saturates
    logic             r_c_den_zero;

    logic             w_c_load;            // pop a descriptor and load the search
    logic             w_c_step;            // C1: walk one beat this cycle
    logic             w_c_last_beat;
    logic [CW-1:0]    w_c_count;           // symbols in this beat (from its keep)
    logic [S-1:0]     w_c_valid;           // lane holds a symbol of the block
    logic [S-1:0]     w_c_is_data;         // lane is a data position
    logic             w_c_any_data;
    logic             w_c_last_data_beat;
    logic [S-1:0]     w_chien_root;
    logic [S*M-1:0]   w_chien_odd;
    logic [S*M-1:0]   w_forney_val;
    logic [S-1:0]     w_forney_den_zero;
    logic [S-1:0]     w_c_hit;             // a correction is applied in this lane
    logic [CW-1:0]    w_c_hits;            // corrections in this beat
    logic             w_c_den_zero_hit;
    logic             w_rechk_zero;   // registered: valid the cycle after the last beat

    // output FIFO: {last_data_beat, keep_data[S], hit[S], correction[S*M], received[S*M]}
    localparam int OF_W = 1 + S + S + 2 * S * M;
    logic            w_of_wr_valid, w_of_wr_ready, w_of_rd_valid, w_of_rd_ready;
    logic [OF_W-1:0] w_of_wr_data, w_of_rd_data;
    // status FIFO: {frame_err, uncorrectable, ok, corrected}
    localparam int ST_W = 3 + SC_W;
    logic            w_st_wr_valid, w_st_wr_ready, w_st_rd_valid, w_st_rd_ready;
    logic [ST_W-1:0] w_st_wr_data, w_st_rd_data;

    logic          w_uncorrectable_final;
    logic [SC_W:0] w_roots_final;

    // C3: the verdict stage. One entry, loaded the cycle after a block's last
    // beat leaves C2, so it can read u_rechk's registered all-zero output.
    logic            r_st_v;
    logic [ST_W-1:0] r_st_data;
    logic            r_c2_last_fired;

    // C2: the walked beat, registered, from which the re-check, the output
    // FIFO write and the verdict are driven
    logic           r_c2_v, r_c2_any_data, r_c2_last_data, r_c2_last_beat, r_c2_first;
    logic [CW-1:0]  r_c2_count;
    logic [S-1:0]   r_c2_is_data, r_c2_hit;
    logic [S*M-1:0] r_c2_corr, r_c2_rx, w_c2_sym;
    logic           w_c2_can_go, w_c2_fire;

    chien_search #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
                   .SYMBOLS_PER_BEAT(S)) u_chien (
        .aclk(aclk), .aresetn(aresetn),
        .i_load(w_c_load), .i_lambda(w_c_lambda), .i_step(w_c_step),
        .o_root(w_chien_root), .o_odd_sum(w_chien_odd));

    forney_evaluator #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T), .N_SYMBOLS(N),
                       .FIRST_ROOT(FIRST_ROOT), .OMEGA_HIGH_HALF(!KES_EUCLID),
                       .SYMBOLS_PER_BEAT(S)) u_forney (
        .aclk(aclk), .aresetn(aresetn),
        .i_load(w_c_load), .i_omega(w_c_omega), .i_step(w_c_step),
        .i_odd_sum(w_chien_odd), .o_err_val(w_forney_val), .o_den_zero(w_forney_den_zero));

    // a new block is loaded only once the previous one's last beat has left C2
    // AND its verdict has been written, because both read this block's
    // descriptor flags and its root count
    assign w_c_load       = (r_c_state == C_IDLE) && w_dbc_rd_valid && !r_c2_v
                            && !r_c2_last_fired && !r_st_v;
    assign w_dbc_rd_ready = w_c_load;
    assign w_c_count      = CW'(gf_keep_count(64'(w_blk_rd_keep), S));
    assign w_c_last_beat  = (r_c_pos + CNT_W'(w_c_count) >= r_c_len);

    always_comb begin
        w_c_any_data       = 1'b0;
        w_c_last_data_beat = 1'b0;
        w_c_hits           = '0;
        w_c_den_zero_hit   = 1'b0;
        for (int u = 0; u < S; u++) begin
            w_c_valid[u]   = (CW'(u) < w_c_count);
            w_c_is_data[u] = w_c_valid[u] && (r_c_pos + CNT_W'(u) < r_c_data_len);
            w_c_hit[u]     = r_c_correct && w_c_valid[u] && w_chien_root[u];
            if (w_c_is_data[u]) w_c_any_data = 1'b1;
            if (w_c_is_data[u] && (r_c_pos + CNT_W'(u) == r_c_data_len - CNT_W'(1)))
                w_c_last_data_beat = 1'b1;
            if (w_c_hit[u]) begin
                w_c_hits = w_c_hits + CW'(1);
                if (w_forney_den_zero[u]) w_c_den_zero_hit = 1'b1;
            end
        end
    end

    // C1 walks a beat when it is in the FIFO and C2 is free or moving on; C2
    // moves when the output FIFO can take a data beat and, on the last beat,
    // the status FIFO can take the verdict
    assign w_c2_can_go = (!r_c2_any_data || w_of_wr_ready)
                      && (!r_c2_last_beat || !r_st_v || w_st_wr_ready);
    assign w_c2_fire   = r_c2_v && w_c2_can_go;
    assign w_c_step    = (r_c_state == C_WALK) && w_blk_rd_valid && (!r_c2_v || w_c2_fire);
    assign w_blk_rd_ready = w_c_step;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c2_v <= 1'b0; r_c2_any_data <= 1'b0; r_c2_last_data <= 1'b0; r_c2_last_beat <= 1'b0;
            r_c2_first <= 1'b0; r_c2_count <= '0; r_c2_is_data <= '0; r_c2_hit <= '0;
            r_c2_corr <= '0; r_c2_rx <= '0;
        end else if (w_c_step) begin
            r_c2_v         <= 1'b1;
            r_c2_any_data  <= w_c_any_data;
            r_c2_last_data <= w_c_last_data_beat;
            r_c2_last_beat <= w_c_last_beat;
            r_c2_first     <= (r_c_pos == '0);
            r_c2_count     <= w_c_count;
            r_c2_is_data   <= w_c_is_data;
            r_c2_hit       <= w_c_hit;
            r_c2_corr      <= w_forney_val;
            r_c2_rx        <= w_blk_rd_sym;
        end else if (w_c2_fire) begin
            r_c2_v <= 1'b0;
        end
    )

    always_comb begin
        for (int u = 0; u < S; u++)
            w_c2_sym[u*M +: M] = r_c2_rx[u*M +: M] ^ (r_c2_hit[u] ? r_c2_corr[u*M +: M] : '0);
    end

    // re-check: syndromes of the corrected stream, data and parity alike
    /* verilator lint_off PINCONNECTEMPTY */
    syndrome_unit #(
        .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T), .FIRST_ROOT(FIRST_ROOT),
        .SYMBOLS_PER_BEAT(S)
    ) u_rechk (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_step          (w_c2_fire),
        .i_first         (r_c2_first),
        .i_data          (w_c2_sym),
        .i_count         (r_c2_count),
        .ow_synd         (),
        .ow_all_zero     (w_rechk_zero),
        .ow_synd_next    (),
        .ow_all_zero_next()
    );
    /* verilator lint_on PINCONNECTEMPTY */

    // saturating root count: the field is one bit wider than the status count
    always_comb begin
        w_roots_final = r_c_roots + (SC_W + 1)'(w_c_hits);
        if (w_roots_final < r_c_roots) w_roots_final = '1;
    end

    // C1 folded every beat's hits into r_c_roots and r_c_den_zero, and
    // w_rechk_zero is the re-check's registered verdict on the whole block, so
    // one cycle after the last beat this is a short expression off flops.
    assign w_uncorrectable_final =
        r_c_correct && (r_c_bad
                        || (r_c_roots != (SC_W + 1)'(r_c_deg))
                        || r_c_den_zero
                        || !w_rechk_zero);

    assign w_of_wr_valid = w_c2_fire && r_c2_any_data;
    assign w_of_wr_data  = {r_c2_last_data, r_c2_is_data, r_c2_hit, r_c2_corr, r_c2_rx};

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c2_last_fired <= 1'b0;
            r_st_v          <= 1'b0;
            r_st_data       <= '0;
        end else begin
            r_c2_last_fired <= w_c2_fire && r_c2_last_beat;
            if (r_c2_last_fired) begin
                r_st_v    <= 1'b1;
                r_st_data <= {r_c_frame_err,
                              w_uncorrectable_final,
                              r_c_all_zero && !r_c_frame_err,
                              (r_c_correct && !w_uncorrectable_final) ? r_c_roots[SC_W-1:0] : SC_W'(0)};
            end else if (w_st_wr_ready) begin
                r_st_v <= 1'b0;
            end
        end
    )

    assign w_st_wr_valid = r_st_v;
    assign w_st_wr_data  = r_st_data;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c_state     <= C_IDLE;
            r_c_len       <= '0;
            r_c_pos       <= '0;
            r_c_data_len  <= '0;
            r_c_frame_err <= 1'b0;
            r_c_all_zero  <= 1'b0;
            r_c_correct   <= 1'b0;
            r_c_bad       <= 1'b0;
            r_c_deg       <= '0;
            r_c_roots     <= '0;
            r_c_den_zero  <= 1'b0;
        end else begin
            case (r_c_state)
                C_IDLE: if (w_c_load) begin
                    r_c_state     <= C_WALK;
                    r_c_len       <= w_c_len;
                    r_c_pos       <= '0;
                    r_c_data_len  <= (w_c_len > CNT_W'(T2)) ? w_c_len - CNT_W'(T2) : w_c_len;
                    r_c_frame_err <= w_c_frame_err;
                    r_c_all_zero  <= w_c_all_zero;
                    r_c_correct   <= w_c_correct;
                    r_c_bad       <= w_c_bad;
                    r_c_deg       <= w_c_deg;
                    r_c_roots     <= '0;
                    r_c_den_zero  <= 1'b0;
                end
                C_WALK: if (w_c_step) begin
                    r_c_pos      <= r_c_pos + CNT_W'(w_c_count);
                    r_c_roots    <= w_roots_final;
                    r_c_den_zero <= r_c_den_zero || w_c_den_zero_hit;
                    if (w_c_last_beat) r_c_state <= C_IDLE;
                end
                default: r_c_state <= C_IDLE;
            endcase
        end
    )

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_fifo_sync #(.DATA_WIDTH(OF_W), .DEPTH(OFD), .REGISTERED(0)) u_out_fifo (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_of_wr_valid), .wr_ready(w_of_wr_ready), .wr_data(w_of_wr_data),
        .rd_ready(w_of_rd_ready), .count(), .rd_valid(w_of_rd_valid), .rd_data(w_of_rd_data));

    gaxi_skid_buffer #(.DATA_WIDTH(ST_W), .DEPTH(2)) u_status (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_st_wr_valid), .wr_ready(w_st_wr_ready), .wr_data(w_st_wr_data),
        .count(), .rd_valid(w_st_rd_valid), .rd_ready(w_st_rd_ready), .rd_count(),
        .rd_data(w_st_rd_data));
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // Output: a block is released once its verdict exists; corrections are
    // applied here, and only when the block is not uncorrectable
    // =========================================================================
    logic           w_out_fire;
    logic           w_o_last;
    logic [S-1:0]   w_o_keep, w_o_hit;
    logic [S*M-1:0] w_o_corr, w_o_rx;

    assign {w_o_last, w_o_keep, w_o_hit, w_o_corr, w_o_rx} = w_of_rd_data;
    assign {out_status_frame_err, out_status_uncorrectable, out_status_ok, out_status_corrected}
        = w_st_rd_data;

    always_comb begin
        for (int u = 0; u < S; u++)
            out_data[u*M +: M] = w_o_keep[u]
                ? (w_o_rx[u*M +: M] ^ ((w_o_hit[u] && !out_status_uncorrectable) ? w_o_corr[u*M +: M] : '0))
                : '0;
    end
    assign out_last      = w_o_last;
    assign out_keep      = w_o_keep;
    assign out_valid     = w_of_rd_valid && w_st_rd_valid;
    assign w_out_fire    = out_valid && out_ready;
    assign w_of_rd_ready = w_out_fire;
    assign w_st_rd_ready = w_out_fire && out_last;

    // Unused here: the stage-A syndrome register (its _next form is consumed),
    // the solver's busy flag, and Lambda_{t+1..2t} (folded into o_deg_err).
    logic unused_a;
    assign unused_a = ^w_synd ^ w_kes_busy ^ (^w_kes_lambda[(T2+1)*M-1:(T+1)*M]);

endmodule : rs_decoder_core
