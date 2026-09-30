// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Package: gf_pkg
// Purpose:
//   Elaboration-time arithmetic over GF(2^m) for the Reed-Solomon codec. Every
//   function here is a constant function: it takes the field (m and the
//   primitive polynomial) as arguments, so one package serves every profile and
//   the modules that use it fold the results into constants and XOR networks.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

package gf_pkg;

    // Widest symbol any function here handles. Modules mask to their own m.
    localparam int GF_MAX_M = 16;
    typedef logic [GF_MAX_M-1:0] gf_wide_t;

    // Field constants ---------------------------------------------------------

    // 2^m - 1: the number of nonzero elements, and the order of alpha.
    function automatic int gf_order(input int m);
        return (1 << m) - 1;
    endfunction

    // A mask with the low m bits set.
    function automatic gf_wide_t gf_mask(input int m);
        return gf_wide_t'((1 << m) - 1);
    endfunction

    // Multiply by x (alpha) with reduction: shift left, fold the overflow bit
    // back with the primitive polynomial. prim has bit m set and bits below it
    // describing the rest of the polynomial (0x11D = x^8+x^4+x^3+x^2+1).
    function automatic gf_wide_t gf_mul_x(input gf_wide_t a, input int m, input int prim);
        logic [31:0] s;
        s = {16'b0, a} << 1;
        if (a[m-1]) s = s ^ unsigned'(prim);
        return s[GF_MAX_M-1:0] & gf_mask(m);
    endfunction

    // Arithmetic -----------------------------------------------------------------

    // Shift-and-add product a * b in GF(2^m).
    function automatic gf_wide_t gf_mul_fn(input gf_wide_t a, input gf_wide_t b,
                                            input int m, input int prim);
        gf_wide_t p;
        gf_wide_t aa;
        p  = '0;
        aa = a & gf_mask(m);
        for (int i = 0; i < m; i++) begin
            if (b[i]) p = p ^ aa;
            aa = gf_mul_x(aa, m, prim);
        end
        return p;
    endfunction

    // alpha^k for any integer k, negative included (reduced modulo 2^m - 1;
    // SystemVerilog's % keeps the sign of k, so the result is re-wrapped).
    function automatic gf_wide_t gf_alpha_pow(input int k, input int m, input int prim);
        gf_wide_t r;
        int       e;
        r = gf_wide_t'(1);
        e = ((k % gf_order(m)) + gf_order(m)) % gf_order(m);
        for (int i = 0; i < e; i++) r = gf_mul_x(r, m, prim);
        return r;
    endfunction

    // a^e by square-and-multiply.
    function automatic gf_wide_t gf_pow_fn(input gf_wide_t a, input int e,
                                            input int m, input int prim);
        gf_wide_t r;
        gf_wide_t base;
        int       ee;
        r    = gf_wide_t'(1);
        base = a & gf_mask(m);
        ee   = e;
        while (ee > 0) begin
            if (ee % 2 == 1) r = gf_mul_fn(r, base, m, prim);
            base = gf_mul_fn(base, base, m, prim);
            ee   = ee / 2;
        end
        return r;
    endfunction

    // Multiplicative inverse: a^(2^m - 2). Returns 0 for a = 0 by convention.
    function automatic gf_wide_t gf_inv_fn(input gf_wide_t a, input int m, input int prim);
        if ((a & gf_mask(m)) == '0) return '0;
        return gf_pow_fn(a, gf_order(m) - 1, m, prim);
    endfunction

    // Discrete log base alpha: the k with alpha^k = a, for a != 0. Returns 0
    // for a = 0 (callers gate on zero separately).
    function automatic int gf_log_fn(input gf_wide_t a, input int m, input int prim);
        gf_wide_t r;
        r = gf_wide_t'(1);
        for (int k = 0; k < gf_order(m); k++) begin
            if (r == (a & gf_mask(m))) return k;
            r = gf_mul_x(r, m, prim);
        end
        return 0;
    endfunction

    // Sanity ------------------------------------------------------------------------

    // True when prim is a degree-m polynomial with a nonzero constant term and
    // alpha = x generates every nonzero element (alpha^k != 1 for 0 < k < 2^m-1).
    function automatic bit gf_is_primitive(input int m, input int prim);
        gf_wide_t r;
        if (m < 2 || m > GF_MAX_M) return 1'b0;
        if (((prim >> m) != 1) || (prim % 2 == 0)) return 1'b0;
        r = gf_wide_t'(1);
        for (int k = 1; k < gf_order(m); k++) begin
            r = gf_mul_x(r, m, prim);
            if (r == gf_wide_t'(1)) return 1'b0;
        end
        return 1'b1;
    endfunction

endpackage : gf_pkg
