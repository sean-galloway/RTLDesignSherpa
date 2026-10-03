// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_erasure_unit
// Purpose:
//   The erasure half of the decoder (ERASURE_SUPPORT = 1): records the
//   flagged positions as the block arrives, turns the syndromes into the
//   window the key-equation solver consumes, and builds the combined
//   locator and evaluator the Chien/Forney walk consumes.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-10-02

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: rs_erasure_unit
//==============================================================================
// Description:
//   dv/tbclasses/rs_model.py is the bit-exact reference (its decode() erasure
//   path, validated against reedsolo on every profile). The unit is two
//   halves joined by a packed bus that rides the decoder core's A -> B
//   descriptor:
//
//   A  record   lane u of a beat is erasure-flagged when i_rx_erasure[u] is
//               set for a valid symbol at position j; its location
//               X_j = alpha^(n-1-j) comes from a running power register
//               (loaded alpha^(n-1) on the block's first beat, multiplied by
//               alpha^(-count) per beat) times the per-lane constant
//               alpha^(-u). Flagged X values are written into a 2t+1-entry
//               file in arrival order -- the rank of each flagged lane
//               within its beat selects the entry -- and the erasure count f
//               accumulates per block, saturating at 2t+1 with f_over: more
//               than 2t erasures is uncorrectable by inspection.
//   B  solve    TRANS replays the file one entry per cycle, combining both
//               the Gamma register (r_gam[i] ^= X_p * r_gam[i-1], so Gamma(x)
//               = prod(1 + X_p x), roots at X_p^-1, Chien's convention) and
//               the syndrome register (r_gs[j] ^= X_p * r_gs[j-1], leaving
//               Gamma*S mod x^2t). The solver input is then a window of the
//               result: riBM takes T = GS >> f (the low f cells are the
//               evaluator tail; feeding them to a forward-iterating BM is the
//               unsound step the model caught), Euclid takes the zeroed-low
//               window x^f * T, sound there because it consumes the
//               polynomial whole. When the high cells are all zero the
//               erasures alone explain the syndromes: o_t_zero skips the
//               solver (Euclid would not terminate on all-zero Q) with
//               Lambda_e = 1, and the registers already hold the answers.
//               COMB then Horners over Lambda_e's coefficients:
//               Lambda_c = Gamma * Lambda_e and Omega_c = Lambda_e * GS mod
//               x^2t (== Gamma*Lambda_e*S mod x^2t, the combined textbook
//               evaluator, so the walk's Forney exponent is 1 - b).
//
//   o_deg_c is the combined degree deg_e + f, clamped at 2t+1 (a block whose
//   solver overflowed is bad anyway); a clean solve always lands <= 2t.
//
//   Latency: TRANS is f cycles (skipped when f = 0 beyond the load cycle)
//   and COMB is deg_e + 1 <= t + 1 cycles, both single gf_mul deep -- the
//   receive-side work per beat is one constant multiply per lane plus the
//   rank muxes.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH, PRIM_POLY, T_SYMBOLS, N_SYMBOLS, SYMBOLS_PER_BEAT: as
//                rs_decoder_core.
//   KES_ALGO:      "RIBM" or "EUCLID"; selects the solver-input window.
//
//==============================================================================

module rs_erasure_unit
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int N_SYMBOLS    = (1 << SYMBOL_WIDTH) - 1,
    parameter int SYMBOLS_PER_BEAT = 1,
    parameter string KES_ALGO  = "RIBM",
    // packed A -> B record width: {f_over, f, xfile[0..2t]}
    parameter int AB_W = 1 + $clog2(2 * T_SYMBOLS + 1) + (2 * T_SYMBOLS + 1) * SYMBOL_WIDTH
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    // ---- A: receive side -------------------------------------------------
    input  logic                          i_rx_fire,      // a beat is accepted
    input  logic                          i_rx_first,     // it starts a new block
    input  logic [$clog2(SYMBOLS_PER_BEAT+1)-1:0] i_rx_count,  // valid symbols in it
    input  logic [SYMBOLS_PER_BEAT-1:0]   i_rx_erasure,   // per-lane erasure flags

    // packed A -> B record: {f_over, f, xfile[0..2t]}; rides the descriptor
    output logic [AB_W-1:0]               o_ab,
    input  logic [AB_W-1:0]               i_ab,

    // ---- B: solve side ---------------------------------------------------
    input  logic [2*T_SYMBOLS*SYMBOL_WIDTH-1:0] i_synd,   // syndromes from the descriptor
    input  logic                          i_trans_start,  // load and run the transform
    output logic                          o_trans_done,
    input  logic                          i_comb_start,   // combine over Lambda_e
    output logic                          o_comb_done,
    input  logic [(2*T_SYMBOLS+1)*SYMBOL_WIDTH-1:0] i_lambda_e,
    input  logic [$clog2(2*T_SYMBOLS+1)-1:0] i_deg_e,

    output logic [2*T_SYMBOLS*SYMBOL_WIDTH-1:0] o_kes_synd,   // solver input window
    output logic [$clog2(2*T_SYMBOLS+1)-1:0]    o_f,
    output logic                          o_f_over,
    output logic                          o_t_zero,       // erasures alone explain the syndromes
    output logic [(2*T_SYMBOLS+1)*SYMBOL_WIDTH-1:0] o_lambda_c,
    output logic [2*T_SYMBOLS*SYMBOL_WIDTH-1:0]   o_omega_c,
    output logic [$clog2(2*T_SYMBOLS+1):0]        o_deg_c
);

    localparam int M     = SYMBOL_WIDTH;
    localparam int T     = T_SYMBOLS;
    localparam int T2    = 2 * T;
    localparam int N     = N_SYMBOLS;
    localparam int S     = SYMBOLS_PER_BEAT;
    localparam int CW    = $clog2(S + 1);
    localparam int DEG_W = $clog2(T2 + 1);
    localparam int EW    = DEG_W + CW + 1;   // wide enough that f + rank never wraps

    initial begin : param_check
        if (T < 1 || T2 > (1 << M) - 2)
            $error("rs_erasure_unit: T_SYMBOLS %0d out of range for GF(2^%0d)", T, M);
        if (N > (1 << M) - 1)
            $error("rs_erasure_unit: N_SYMBOLS %0d exceeds 2^%0d - 1", N, M);
        if (KES_ALGO != "RIBM" && KES_ALGO != "EUCLID")
            $error("rs_erasure_unit: KES_ALGO must be \"RIBM\" or \"EUCLID\" (got %s)", KES_ALGO);
    end

    // =========================================================================
    // A: record the flagged locations
    // =========================================================================
    logic [M-1:0] r_xpow;              // alpha^(n-1-pos) at the current beat
    logic [M-1:0] r_xfile [T2+1];      // X of each flagged symbol, in order
    logic [DEG_W-1:0] r_f;             // erasures this block, saturating at 2t+1
    logic             r_over;          // f would exceed 2t

    /* verilator lint_off UNUSEDSIGNAL */   // gf_wide_t whose low M bits are the value
    gf_wide_t w_nm1;
    /* verilator lint_on UNUSEDSIGNAL */
    assign w_nm1 = gf_alpha_pow(N - 1, M, PRIM_POLY);

    logic [M-1:0]     w_xbase;
    logic [M-1:0]     w_x_lane [S];
    logic [S-1:0]     w_m;             // flagged valid lanes of this beat
    logic [CW-1:0]    w_rank [S];      // flags before this lane in the beat
    logic [CW:0]      w_pop;           // flagged lanes in the beat
    logic [DEG_W-1:0] w_f_base;
    logic [EW-1:0]    w_f_next;        // wide: the narrow sum can wrap at small t

    assign w_xbase  = i_rx_first ? w_nm1[M-1:0] : r_xpow;
    assign w_f_base = i_rx_first ? '0 : r_f;

    for (genvar u = 0; u < S; u++) begin : g_lane
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(-u, M, PRIM_POLY)))
        ) u_lane (.i_a(w_xbase), .ow_p(w_x_lane[u]));

        assign w_m[u] = i_rx_erasure[u] && (CW'(u) < i_rx_count) && i_rx_fire;
        always_comb begin
            w_rank[u] = '0;
            for (int v = 0; v < u; v++) w_rank[u] = w_rank[u] + CW'(w_m[v]);
        end
    end

    always_comb begin
        w_pop = '0;
        for (int u = 0; u < S; u++) w_pop = w_pop + (CW + 1)'(w_m[u]);
    end
    assign w_f_next = EW'(w_f_base) + EW'(w_pop);

    // advance: times alpha^(-count), one constant multiply per possible count
    logic [M-1:0] w_adv [S+1];
    for (genvar c = 0; c <= S; c++) begin : g_adv
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(-c, M, PRIM_POLY)))
        ) u_adv (.i_a(w_xbase), .ow_p(w_adv[c]));
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_xpow <= '0;
            for (int e = 0; e <= T2; e++) r_xfile[e] <= '0;
            r_f    <= '0;
            r_over <= 1'b0;
        end else if (i_rx_fire) begin
            r_xpow <= w_adv[i_rx_count];
            for (int e = 0; e <= T2; e++)
                for (int u = 0; u < S; u++)
                    if (w_m[u] && (EW'(e) == EW'(w_f_base) + EW'(w_rank[u])))
                        r_xfile[e] <= w_x_lane[u];
            r_f    <= (w_f_next > EW'(T2 + 1)) ? DEG_W'(T2 + 1) : w_f_next[DEG_W-1:0];
            r_over <= (i_rx_first ? 1'b0 : r_over) || (w_f_next > EW'(T2));
        end
    )

    // pack: {over, f, xfile[2t] ... xfile[0]} with entry 0 in the low bits.
    // The core's descriptor pack samples o_ab on the block-end EDGE, before
    // that edge's own flags have landed in the registers -- the same reason
    // the syndrome path ships w_synd_next. o_ab is therefore the NEXT-value
    // record: this beat's flagged lanes merged over the register file. When
    // no beat is firing w_m is all zero and this reduces to the registers.
    logic [(T2+1)*M-1:0] w_xfile_packed;
    logic [(T2+1)*M-1:0] w_xfile_next;
    logic [DEG_W-1:0]    w_f_sat;
    logic                w_over_next;
    for (genvar e = 0; e <= T2; e++) begin : g_pack
        assign w_xfile_packed[e*M +: M] = r_xfile[e];
    end
    always_comb begin
        w_xfile_next = w_xfile_packed;
        for (int e = 0; e <= T2; e++)
            for (int u = 0; u < S; u++)
                if (w_m[u] && (EW'(e) == EW'(w_f_base) + EW'(w_rank[u])))
                    w_xfile_next[e*M +: M] = w_x_lane[u];
    end
    assign w_f_sat     = (w_f_next > EW'(T2 + 1)) ? DEG_W'(T2 + 1) : w_f_next[DEG_W-1:0];
    assign w_over_next = (i_rx_first ? 1'b0 : r_over) || (w_f_next > EW'(T2));
    assign o_ab = {w_over_next, w_f_sat, w_xfile_next};

    // =========================================================================
    // B: transform, solve window, combine
    // =========================================================================
    logic                  w_f_over;
    logic [DEG_W-1:0]      w_f;
    logic [M-1:0]          w_xfile [T2+1];
    assign {w_f_over, w_f} = i_ab[AB_W-1 -: 1 + DEG_W];
    for (genvar e = 0; e <= T2; e++) begin : g_unpack
        assign w_xfile[e] = i_ab[e*M +: M];
    end

    // The core pops the descriptor on the SAME edge i_trans_start fires
    // (every other field it needs is consumed that cycle or sampled into
    // its own registers), so i_ab is not guaranteed to hold through TRANS:
    // the record is latched here at the start edge and everything after it
    // reads the latch. o_f_over stays combinational -- the core uses it
    // only in BE_IDLE, while the descriptor is still at the read port.
    logic [DEG_W-1:0]      r_fb;
    logic [M-1:0]          r_xfile_b [T2+1];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_fb <= '0;
            for (int e = 0; e <= T2; e++) r_xfile_b[e] <= '0;
        end else if (i_trans_start) begin
            r_fb <= w_f;
            for (int e = 0; e <= T2; e++) r_xfile_b[e] <= w_xfile[e];
        end
    )

    logic [M-1:0] r_gam [T2+1];        // Gamma(x), combined per TRANS cycle
    logic [M-1:0] r_gs  [T2];          // Gamma*S mod x^2t after TRANS
    logic [DEG_W-1:0] r_tc;            // TRANS cycle index
    logic             r_tr_run;
    logic             r_t_zero;

    logic [M-1:0]     w_x;
    logic [M-1:0]     w_gs_nxt [T2];   // this cycle's combine result
    logic             w_t_nonzero;     // any high (x^f * T) cell nonzero, post-combine

    assign w_x = r_xfile_b[r_tc];

    for (genvar j = 0; j < T2; j++) begin : g_gs
        if (j == 0) begin : g_j0
            assign w_gs_nxt[j] = r_gs[j];
        end else begin : g_jn
            logic [M-1:0] w_p;
            gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_gs (
                .i_a(w_x), .i_b(r_gs[j-1]), .ow_p(w_p));
            assign w_gs_nxt[j] = r_gs[j] ^ w_p;
        end
    end

    always_comb begin
        w_t_nonzero = 1'b0;
        for (int j = 0; j < T2; j++)
            if ((DEG_W'(j) >= r_fb) && (w_gs_nxt[j] != '0)) w_t_nonzero = 1'b1;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i <= T2; i++) r_gam[i] <= '0;
            for (int j = 0; j < T2; j++)  r_gs[j]  <= '0;
            r_tc         <= '0;
            r_tr_run     <= 1'b0;
            r_t_zero     <= 1'b0;
            o_trans_done <= 1'b0;
        end else begin
            o_trans_done <= 1'b0;
            if (i_trans_start) begin
                for (int j = 0; j < T2; j++)
                    r_gs[j] <= i_synd[j*M +: M];
                r_gam[0] <= M'(1);
                for (int i = 1; i <= T2; i++) r_gam[i] <= '0;
                r_tc         <= '0;
                r_tr_run     <= (w_f != '0);
                r_t_zero     <= 1'b0;
                o_trans_done <= (w_f == '0);
            end else if (r_tr_run) begin
                for (int j = 0; j < T2; j++) r_gs[j] <= w_gs_nxt[j];
                for (int i = 1; i <= T2; i++) begin
                    logic [M-1:0] p;
                    p = M'(gf_mul_fn(gf_wide_t'(w_x), gf_wide_t'(r_gam[i-1]), M, PRIM_POLY));
                    r_gam[i] <= r_gam[i] ^ p;
                end
                if (r_tc == r_fb - DEG_W'(1)) begin
                    r_tr_run     <= 1'b0;
                    o_trans_done <= 1'b1;
                    r_t_zero     <= !w_t_nonzero;
                end
                r_tc <= r_tc + DEG_W'(1);
            end
        end
    )

    // -------------------------------------------------------------------------
    // The solver input window: riBM takes T = GS >> f zero-padded, Euclid the
    // zeroed-low window x^f * T. f = 0 makes both the identity.
    // -------------------------------------------------------------------------
    if (KES_ALGO == "EUCLID") begin : g_window_euclid
        for (genvar i = 0; i < T2; i++) begin : g_w
            assign o_kes_synd[i*M +: M] = (DEG_W'(i) >= r_fb) ? r_gs[i] : '0;
        end
    end else begin : g_window_ribm
        // T = GS >> f as a crossbar: cell i takes r_gs[j] when j == i + f,
        // zero when i + f leaves the register (no out-of-bounds read)
        for (genvar i = 0; i < T2; i++) begin : g_w
            always_comb begin
                o_kes_synd[i*M +: M] = '0;
                for (int j = 0; j < T2; j++)
                    if (EW'(j) == EW'(i) + EW'(r_fb)) o_kes_synd[i*M +: M] = r_gs[j];
            end
        end
    end

    // -------------------------------------------------------------------------
    // COMB: Horner over Lambda_e's coefficients, high to low:
    //   acc_lam = x*acc_lam + Lambda_e[i]*Gamma   ->  Lambda_c = Gamma*Lambda_e
    //   acc_om  = x*acc_om  + Lambda_e[i]*GS      ->  Omega_c (mod x^2t by the drop)
    // -------------------------------------------------------------------------
    logic [M-1:0] r_acc_lam [T2+1];
    logic [M-1:0] r_acc_om  [T2];
    logic [DEG_W-1:0] r_ci;
    logic             r_cb_run;

    logic [M-1:0] w_lc;

    assign w_lc = i_lambda_e[r_ci*M +: M];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i <= T2; i++) r_acc_lam[i] <= '0;
            for (int j = 0; j < T2; j++)  r_acc_om[j]  <= '0;
            r_ci        <= '0;
            r_cb_run    <= 1'b0;
            o_comb_done <= 1'b0;
        end else begin
            o_comb_done <= 1'b0;
            if (i_comb_start) begin
                for (int i = 0; i <= T2; i++) r_acc_lam[i] <= '0;
                for (int j = 0; j < T2; j++)  r_acc_om[j]  <= '0;
                r_ci     <= i_deg_e;
                r_cb_run <= 1'b1;
            end else if (r_cb_run) begin
                for (int i = 0; i <= T2; i++) begin
                    logic [M-1:0] p;
                    p = M'(gf_mul_fn(gf_wide_t'(w_lc), gf_wide_t'(r_gam[i]), M, PRIM_POLY));
                    r_acc_lam[i] <= ((i > 0) ? r_acc_lam[i-1] : '0) ^ p;
                end
                for (int j = 0; j < T2; j++) begin
                    logic [M-1:0] p;
                    p = M'(gf_mul_fn(gf_wide_t'(w_lc), gf_wide_t'(r_gs[j]), M, PRIM_POLY));
                    r_acc_om[j] <= ((j > 0) ? r_acc_om[j-1] : '0) ^ p;
                end
                if (r_ci == '0) begin
                    r_cb_run    <= 1'b0;
                    o_comb_done <= 1'b1;
                end
                r_ci <= r_ci - DEG_W'(1);
            end
        end
    )

    // -------------------------------------------------------------------------
    // Outputs. On t_zero the solver never ran: Lambda_e = 1 makes Lambda_c =
    // Gamma and Omega_c = GS, both already in the registers.
    // -------------------------------------------------------------------------
    logic [DEG_W:0] w_deg_sum;

    assign w_deg_sum = {1'b0, i_deg_e} + {1'b0, r_fb};
    assign o_deg_c   = r_t_zero ? {1'b0, r_fb}
                                : ((w_deg_sum > (DEG_W + 1)'(T2 + 1)) ? (DEG_W + 1)'(T2 + 1) : w_deg_sum);
    assign o_f       = r_fb;
    assign o_f_over  = w_f_over;   // combinational: the core reads it only pre-pop (BE_IDLE)
    assign o_t_zero  = r_t_zero;

    for (genvar i = 0; i <= T2; i++) begin : g_ol
        assign o_lambda_c[i*M +: M] = r_t_zero ? r_gam[i] : r_acc_lam[i];
    end
    for (genvar j = 0; j < T2; j++) begin : g_oo
        assign o_omega_c[j*M +: M] = r_t_zero ? r_gs[j] : r_acc_om[j];
    end

endmodule : rs_erasure_unit
