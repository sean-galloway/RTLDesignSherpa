// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Package: bch_pkg
// Purpose:
//   Elaboration-time constants and helper functions for the binary BCH codec.
//   Every GF(2^m) arithmetic operation is delegated to gf_pkg; this package
//   holds only BCH-specific construction (generator polynomial, syndrome roots,
//   beat counts) computed at elaboration from FIELD_DIM/PRIM_POLY/T_BITS/
//   FIRST_ROOT so no polynomial coefficient is ever typed in.
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/01_encoder.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps

package bch_pkg;

    import gf_pkg::*;

    // -------------------------------------------------------------------------
    // Elaboration defaults
    // -------------------------------------------------------------------------
    // CCSDS TC (63,56) modified BCH is the reference profile: m = 6, the field
    // polynomial is x^6 + x + 1 (0x43), t = 1, n = 63. FIRST_ROOT defaults to
    // 1 (narrow-sense); CCSDS overrides it to 0 to include the (x+1) factor.
    parameter int FIELD_DIM     = 6;
    parameter int PRIM_POLY     = 'h43;
    parameter int T_BITS        = 1;
    parameter int N_BITS        = 63;
    parameter int BITS_PER_BEAT = 8;
    parameter int FIRST_ROOT    = 1;

    // Largest generator degree this package can represent.  GF_MAX_M * 512 is
    // generous for every realistic profile (m=13,t=8 gives deg 104) while
    // keeping the fixed-width return vectors manageable for elaboration.
    localparam int BCH_MAX_DEG = GF_MAX_M * 512;

    // -------------------------------------------------------------------------
    // Field size
    // -------------------------------------------------------------------------
    function automatic int bch_order(input int m);
        return (1 << m) - 1;
    endfunction

    // -------------------------------------------------------------------------
    // Generator polynomial degree.
    // g(x) is the lcm over GF(2) of the minimal polynomials of alpha^b ..
    // alpha^(b+2t-1). The degree is the number of distinct conjugates in that
    // consecutive root range; each cyclotomic coset modulo 2^m - 1 contributes
    // its size once.
    // -------------------------------------------------------------------------
    function automatic int bch_degree_g(input int m, input int prim, input int t, input int b);
        int n_full;
        int visited [(1 << GF_MAX_M)];
        int deg;
        int e, cur;
        n_full = bch_order(m);
        deg    = 0;
        for (int i = 0; i < n_full; i++) visited[i] = 0;
        for (int i = 0; i < 2 * t; i++) begin
            e   = ((b + i) % n_full + n_full) % n_full;
            cur = e;
            while (visited[cur] == 0) begin
                visited[cur] = 1;
                deg++;
                cur = (cur * 2) % n_full;
            end
        end
        return deg;
    endfunction

    // -------------------------------------------------------------------------
    // Generator polynomial coefficients as a vector of GF_MAX_M-bit lanes.
    // Coefficient j lives at bits [j*GF_MAX_M +: GF_MAX_M]; only the low M bits
    // are meaningful. The leading coefficient g_DEG = 1 is implicit.
    // Built by multiplying (x + alpha^exp) over every distinct conjugate exp in
    // the consecutive root range. Coefficients are GF(2) values packaged in
    // GF_MAX_M-bit lanes so they can feed gf_mul_const taps directly. The
    // vector is padded to BCH_MAX_DEG lanes so the return width is a compile-
    // time constant independent of the arguments.
    // -------------------------------------------------------------------------
    function automatic logic [BCH_MAX_DEG * GF_MAX_M - 1:0]
        bch_gen_poly_packed(input int m, input int prim, input int t, input int b);

        int       n_full;
        int       cur_deg;
        int       visited [(1 << GF_MAX_M)];
        gf_wide_t root;
        gf_wide_t poly [BCH_MAX_DEG + 1];
        gf_wide_t new_poly [BCH_MAX_DEG + 1];
        logic [BCH_MAX_DEG * GF_MAX_M - 1:0] r;

        n_full  = bch_order(m);
        cur_deg = 0;
        for (int j = 0; j <= BCH_MAX_DEG; j++) poly[j] = '0;
        poly[0] = gf_mask(m) & gf_wide_t'(1);
        for (int i = 0; i < n_full; i++) visited[i] = 0;

        for (int i = 0; i < 2 * t; i++) begin
            int e;
            e = ((b + i) % n_full + n_full) % n_full;
            if (visited[e] == 0) begin
                int cur;
                cur = e;
                // One (x + alpha^cur) factor per CONJUGATE, not per coset: the
                // minimal polynomial of alpha^e is the product over its whole
                // cyclotomic coset. The first cut multiplied once per coset and
                // produced a degree-2 stand-in for the CCSDS degree-7 g(x)
                // (bch_gen_poly_bits(6,0x43,1,0) returned 0x6, not 0xc5); the
                // syndrome lanes never noticed because they use only root
                // exponents, and the encoder test that caught it could not run
                // until the sim-build lint failure above it was fixed.
                //
                // Every loop here is bounded by cur_deg, never BCH_MAX_DEG:
                // the padding lanes are zero by construction and iterating
                // them once per factor is what OOM-killed Verilator (signal 9)
                // on the full-coset build at m = 13.
                while (visited[cur] == 0) begin
                    visited[cur] = 1;
                    root = gf_alpha_pow(cur, m, prim);
                    for (int j = 0; j <= cur_deg + 1; j++) new_poly[j] = '0;
                    for (int j = cur_deg + 1; j >= 0; j--) begin
                        gf_wide_t old_c;
                        gf_wide_t tap;
                        old_c = (j <= cur_deg) ? (poly[j] & gf_mask(m)) : '0;
                        tap   = gf_mul_fn(root, old_c, m, prim) & gf_mask(m);
                        if (j > 0) begin
                            gf_wide_t shift_c;
                            shift_c = poly[j - 1] & gf_mask(m);
                            new_poly[j] = shift_c ^ tap;
                        end else begin
                            new_poly[0] = tap;
                        end
                    end
                    for (int j = 0; j <= cur_deg + 1; j++) poly[j] = new_poly[j];
                    cur_deg = cur_deg + 1;
                    cur = (cur * 2) % n_full;
                end
            end
        end

        for (int j = 0; j < BCH_MAX_DEG; j++) begin
            r[j * GF_MAX_M +: GF_MAX_M] = poly[j] & gf_mask(m);
        end
        return r;
    endfunction

    // -------------------------------------------------------------------------
    // Generator polynomial coefficients as a packed bit vector (one bit per
    // coefficient). Only the low DEG bits are meaningful; the rest are zero.
    // -------------------------------------------------------------------------
    function automatic logic [BCH_MAX_DEG - 1:0]
        bch_gen_poly_bits(input int m, input int prim, input int t, input int b);

        logic [BCH_MAX_DEG * GF_MAX_M - 1:0] packed_g;
        logic [BCH_MAX_DEG - 1:0] bits;
        packed_g = bch_gen_poly_packed(m, prim, t, b);
        for (int j = 0; j < BCH_MAX_DEG; j++) begin
            bits[j] = packed_g[j * GF_MAX_M];
        end
        return bits;
    endfunction

    // -------------------------------------------------------------------------
    // Syndrome root exponents. For a code whose generator has consecutive roots
    // alpha^b .. alpha^(b+2t-1), the independent (odd) syndromes are those at
    // the odd exponents inside that range.
    // -------------------------------------------------------------------------
    function automatic int bch_syndrome_root_exp(input int j, input int b);
        int first_odd;
        first_odd = b + ((b + 1) % 2);
        return first_odd + 2 * j;
    endfunction

    // -------------------------------------------------------------------------
    // Beat-count helpers
    // -------------------------------------------------------------------------
    function automatic int bch_beats(input int bits, input int bpb);
        return (bits + bpb - 1) / bpb;
    endfunction

    function automatic int bch_keep_count(input logic [63:0] keep, input int s);
        return gf_keep_count(keep, s);
    endfunction

endpackage : bch_pkg
