//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: arbiter_round_robin_simple
        // Purpose: Arbiter Round Robin Simple module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        // Generic rotating-priority arbiter with masking/rotation (no if/case ladders in priority path)
        // - Parameterizable number of agents N (N >= 1)
        // - Remembers last granted index in a flop (r_last_grant)
        // - Uses rotation and lowest-set-bit isolate: x & (~x + 1)
        // - Prefixes: w_* = wires, r_* = flops
        
        `include "reset_defs.svh"
        module arbiter_round_robin_simple #(
            parameter int unsigned N = 4,
            parameter int unsigned W = $clog2(N)
        ) (
 060363     input  logic          clk,
%000007     input  logic          rst_n,         // active-low reset
 001040     input  logic [N-1:0]  request,       // request bits [N-1:0]
 010014     output logic          grant_valid,   // any grant
 000428     output logic [N-1:0]  grant,         // one-hot grant
 002524     output logic [W-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
        );
            // ------------------------------
            // State: last granted index
            // ------------------------------
 001868     logic [W-1:0] r_last_grant;
        
            // ------------------------------
            // Combinational priority logic
            // ------------------------------
 002524     logic [W-1:0] w_grant_id;
 001722     logic [N-1:0] w_rot_req;
 000078     logic [N-1:0] w_rot_sel;
 000428     logic [N-1:0] w_nxt_grant;
 010014     logic         w_grant_valid;
        
            // Shift amount = last_grant + 1 (mod N), renamed per your request.
 001450     logic [W-1:0] w_shift_amount;       // 0..N-1
            assign w_shift_amount = (r_last_grant == (W)'(N-1)) ? '0 : (r_last_grant + 1);
        
            // Rotate-left request by w_shift_amount, with a guard for 0 to avoid shifting by N
 180928     always_comb begin
 026852         if (w_shift_amount == '0) begin
 026852             w_rot_req = request;
 154076         end else begin
 154076             w_rot_req = (request << w_shift_amount) | (request >> ((W)'(N) - w_shift_amount));
                end
                // Isolate lowest set bit (one-hot). Works for zero too (yields zero).
 180928         w_rot_sel = w_rot_req & ((~w_rot_req) + {{(N-1){1'b0}}, 1'b1});
        
                // Rotate-right by the same amount to restore original bit positions
 026852         if (w_shift_amount == '0) begin
 026852             w_nxt_grant = w_rot_sel;
 154076         end else begin
 154076             w_nxt_grant = (w_rot_sel >> w_shift_amount) | (w_rot_sel << ((W)'(N) - w_shift_amount));
                end
            end
        
            assign grant = w_nxt_grant;
            assign w_grant_valid = |w_nxt_grant;
            assign grant_valid = w_grant_valid;
        
            // One-hot to index encoder (compact & synth-friendly)
 079488     always_comb begin
 079488         w_grant_id = r_last_grant; // don't-care if no grant; default to last
 079488         for (int i = 0; i < N; i++) begin
 054777             if (w_nxt_grant[i]) w_grant_id = i[W-1:0];
                end
            end
            assign grant_id = w_grant_id;
        
            // ------------------------------
            // State update
            // ------------------------------
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_last_grant <= (W)'(N-1); // first pass starts at agent 0
                end else if (w_grant_valid) begin
                    r_last_grant <= w_grant_id;
                end
 000084     )
        
        
        endmodule : arbiter_round_robin_simple
        
