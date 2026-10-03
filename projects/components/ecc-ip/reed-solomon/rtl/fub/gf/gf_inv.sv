// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gf_inv
// Purpose:
//   Multiplicative inverse in GF(2^m) by table lookup. Combinational, no clock.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

//==============================================================================
// Module: gf_inv
//==============================================================================
// Description:
//   inv(a) = alpha^(-log a) = antilog[(2^m - 1 - log a) mod (2^m - 1)]. Both
//   tables are built at elaboration by gf_pkg and packed into localparam
//   vectors, so the module is two ROMs and a subtract: at m = 8 that is two
//   256-entry tables that infer to LUTs; by m = 10 they are BRAM candidates
//   and above INV_MAX_M the table form is refused (Itoh-Tsujii is the
//   alternative at those widths).
//
//   Zero has no inverse. The output is 0 and ow_zero is raised so the caller
//   (Forney, which divides by the locator derivative) can flag the block.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m, the field is GF(2^m). Range 2..INV_MAX_M (12). Default 8.
//   PRIM_POLY:    primitive polynomial with bit m set. Default 0x11D.
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   i_a:     operand
//   ow_inv:  1 / a, or 0 when a = 0
//   ow_zero: a was 0
//
//==============================================================================

module gf_inv
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D
) (
    input  logic [SYMBOL_WIDTH-1:0] i_a,
    output logic [SYMBOL_WIDTH-1:0] ow_inv,
    output logic                    ow_zero
);

    localparam int M         = SYMBOL_WIDTH;
    localparam int INV_MAX_M = 12;
    localparam int N         = (1 << M) - 1;   // order of alpha

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 2 || M > INV_MAX_M)
            $error("gf_inv: SYMBOL_WIDTH must be 2..%0d for the table form (got %0d)",
                   INV_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("gf_inv: PRIM_POLY 0x%0h is not a primitive polynomial of degree %0d",
                   PRIM_POLY, M);
    end

    // -------------------------------------------------------------------------
    // Tables. LOG has 2^M entries (index a, entry log a; entry 0 unused).
    // ANTILOG has N entries (index k, entry alpha^k).
    // -------------------------------------------------------------------------
    localparam int LOG_W = (1 << M) * M;
    localparam int ALOG_W = N * M;

    // Every entry is assigned by the loop, so neither table needs a zero fill
    // (a fill of 2^M x M bits trips Verilator's replication limit at M >= 10).
    function automatic logic [ALOG_W-1:0] build_antilog();
        logic [ALOG_W-1:0] r;
        gf_wide_t          e;
        e = gf_wide_t'(1);
        for (int k = 0; k < N; k++) begin
            r[k*M +: M] = e[M-1:0];
            e = gf_mul_x(e, M, PRIM_POLY);
        end
        return r;
    endfunction

    function automatic logic [LOG_W-1:0] build_log();
        logic [LOG_W-1:0] r;
        gf_wide_t         e;
        r[0 +: M] = '0;   // log 0 is undefined; entry 0 is never used
        e = gf_wide_t'(1);
        for (int k = 0; k < N; k++) begin
            r[e[M-1:0]*M +: M] = M'(k);
            e = gf_mul_x(e, M, PRIM_POLY);
        end
        return r;
    endfunction

    localparam logic [ALOG_W-1:0] ANTILOG = build_antilog();
    localparam logic [LOG_W-1:0]  LOG     = build_log();

    // -------------------------------------------------------------------------
    // Lookup: neg_log = N - log a, wrapped to 0 when log a = 0 (a = 1)
    // -------------------------------------------------------------------------
    logic [M-1:0] w_log;
    logic [M-1:0] w_neg_log;

    always_comb begin
        w_log     = LOG[i_a*M +: M];
        w_neg_log = (w_log == '0) ? '0 : M'(N) - w_log;
        ow_zero   = (i_a == '0);
        ow_inv    = ow_zero ? '0 : ANTILOG[w_neg_log*M +: M];
    end

endmodule : gf_inv
