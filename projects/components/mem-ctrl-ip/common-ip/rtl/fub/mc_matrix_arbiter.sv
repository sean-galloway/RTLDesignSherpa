// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_matrix_arbiter
// Purpose: N-requester matrix (pairwise-state) arbiter for the aged
//          scheduler core (MC-003 2026-10-18, owner architecture).  Each
//          requester pair carries one state bit r_mat[i][j]: 1 = i outranks
//          j.  Grant for i = req_i AND, over every other requesting j, the
//          state says i outranks j.  The pairwise state keeps a total order,
//          so exactly one requester grants whenever any request; the winner
//          updates itself to lowest priority, giving round-robin fairness
//          over the requesting set.
//          Timing: the grant is a per-row AND over pre-masked request terms
//          -- the aged core masks requests down to the age-minimum, timer-
//          ready set before the matrix, so in steady state only one or two
//          terms are live and the grant collapses to a couple of gate
//          levels.  No priority-encoder ripple, no shared carry chain.
//
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_matrix_arbiter
#(
    parameter int N = 16
)(
    input  logic         aclk,
    input  logic         aresetn,

    input  logic [N-1:0] req_i,
    output logic [N-1:0] gnt_o,
    // Advance the pairwise state for the granted requester (assert on the
    // cycle the grant is consumed -- the pick registers at this edge).
    input  logic         upd_i
);

    logic r_mat [N][N];

    logic w_outranks_all;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_outranks_all = 1'b1;
            for (int j = 0; j < N; j++) begin
                if ((i != j) && req_i[j] && !r_mat[i][j]) begin
                    w_outranks_all = 1'b0;
                end
            end
            gnt_o[i] = req_i[i] && w_outranks_all;
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // Initial total order: lower index outranks higher (deterministic
            // cold start; fairness emerges from the update rule).
            for (int i = 0; i < N; i++) begin
                for (int j = 0; j < N; j++) begin
                    r_mat[i][j] <= (i < j);
                end
            end
        end else if (upd_i) begin
            for (int i = 0; i < N; i++) begin
                for (int j = 0; j < N; j++) begin
                    if (i == j) begin
                        r_mat[i][j] <= r_mat[i][j];
                    end else if (gnt_o[i]) begin
                        r_mat[i][j] <= 1'b0;   // winner loses to everyone
                    end else if (gnt_o[j]) begin
                        r_mat[i][j] <= 1'b1;   // everyone beats the winner
                    end
                end
            end
        end
    )

endmodule : mc_matrix_arbiter
