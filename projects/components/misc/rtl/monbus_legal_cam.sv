// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_legal_cam
// Purpose: Legal-set match CAM for the profile-mode packet tally. A CSR-loaded
//          set of legal message identities (agent/protocol/type/event keys) is
//          matched against an incoming key; a hit returns the entry's DENSE
//          index (used directly as the tally bin), a miss is reported so the
//          caller can route it to a single UNEXPECTED bin.
//
// Documentation: vault/handbook/fpga/Genesys2/stream-mon/monitor-board-coverage.md
// Subsystem: amba
//
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_legal_cam #(
    parameter int N_ENTRIES = 64,          // legal-set capacity (dense bins 0..N-1)
    parameter int KEY_WIDTH = 32,          // message-identity key width
    // Derived
    parameter int IDX_WIDTH = (N_ENTRIES > 1) ? $clog2(N_ENTRIES) : 1
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Load / clear (one entry per load_we pulse; load_clear invalidates all).
    input  logic                    load_clear,
    input  logic                    load_we,
    input  logic [IDX_WIDTH-1:0]    load_addr,
    input  logic                    load_valid,   // entry valid bit
    input  logic [KEY_WIDTH-1:0]    load_key,

    // Combinational lookup.
    input  logic [KEY_WIDTH-1:0]    lookup_key,
    output logic                    lookup_hit,
    output logic [IDX_WIDTH-1:0]    lookup_idx    // valid only when lookup_hit
);

    // Valid is a packed vector so reset is a single-shot assign (no
    // BLKLOOPINIT). Keys are gated by valid, so they need no reset.
    logic [N_ENTRIES-1:0]  r_valid;
    logic [KEY_WIDTH-1:0]  r_key [N_ENTRIES];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid <= '0;
        end else if (load_clear) begin
            r_valid <= '0;
        end else if (load_we) begin
            r_valid[load_addr] <= load_valid;
            r_key  [load_addr] <= load_key;
        end
    )

    // Parallel exact-match against the loaded legal set.
    logic [N_ENTRIES-1:0] w_match;
    always_comb begin
        for (int i = 0; i < N_ENTRIES; i++)
            w_match[i] = r_valid[i] && (r_key[i] == lookup_key);
    end

    // Priority-encode to a dense index. The host loads unique tuples so at most
    // one entry matches; the low index wins if a duplicate is ever loaded.
    always_comb begin
        lookup_hit = 1'b0;
        lookup_idx = '0;
        for (int i = N_ENTRIES-1; i >= 0; i--)
            if (w_match[i]) begin
                lookup_hit = 1'b1;
                lookup_idx = IDX_WIDTH'(i);
            end
    end

endmodule : monbus_legal_cam
