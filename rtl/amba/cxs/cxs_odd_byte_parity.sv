// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_odd_byte_parity
// Purpose: CXSCHECKTYPE = Odd_Byte_Parity for one signal (IHI 0079D 3.2):
//          generate the check vector, and compare a received one
//
// Documentation: docs/markdown/rtl-amba/cxs/README.md
// Subsystem: amba
//
// Check bit [n] covers data[8n+7:8n]; when WIDTH is not a whole number of
// bytes the top check bit covers the short remainder (CXSCNTL of 27 bits:
// CXSCNTLCHK[3] covers CXSCNTL[26:24]). ODD parity: a check bit plus the
// bits it covers always hold an odd number of ones, so a one-bit signal's
// check is its inversion. Every piece is one rtl/common dataint_parity
// (CHUNKS=1, parity_type=0 = odd), the same primitive the AXIS5 endpoints use.
//
// Parameters:
//   - WIDTH: width of the protected signal, >= 1
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

module cxs_odd_byte_parity #(
    parameter int WIDTH = 8,
    parameter int CHKW  = (WIDTH + 7) / 8
) (
    input  logic [WIDTH-1:0] data,
    input  logic [CHKW-1:0]  chk_in,    // received check vector (tie '0 to only generate)
    output logic [CHKW-1:0]  chk_out,   // correct odd-parity check vector for data
    output logic             chk_err    // chk_in disagrees with data (caller qualifies it)
);

    logic [CHKW-1:0] w_err;

    for (genvar g = 0; g < CHKW; g++) begin : g_piece
        localparam int LO      = 8 * g;
        localparam int PIECE_W = (WIDTH - LO < 8) ? (WIDTH - LO) : 8;
        dataint_parity #(.CHUNKS(1), .WIDTH(PIECE_W)) u_par (
            .data_in     (data[LO +: PIECE_W]),
            .parity_in   (chk_in[g]),
            .parity_type (1'b0),
            .parity      (chk_out[g]),
            .parity_err  (w_err[g])
        );
    end

    assign chk_err = |w_err;

endmodule : cxs_odd_byte_parity
