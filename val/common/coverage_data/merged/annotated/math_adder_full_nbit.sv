//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_adder_full_nbit
        // Purpose: Math Adder Full Nbit module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        module math_adder_full_nbit #(
            parameter int N = 4
        ) (
%000001     input  logic [N-1:0] i_a,
 000031     input  logic [N-1:0] i_b,
 000511     input  logic         i_c,      // Initial carry-in
 000033     output logic [N-1:0] ow_sum,
 000031     output logic         ow_carry  // Final carry-out
        );
        
 000031     logic [N:0] w_c;  // array for internal carries
        
            assign w_c[0] = i_c;  // Initialize the first carry input
        
            genvar i;
            generate
                for (i = 0; i < N; i++) begin : gen_full_adders
                    math_adder_full fa (
                        .i_a(i_a[i]),
                        .i_b(i_b[i]),
                        .i_c(w_c[i]),
                        .ow_sum(ow_sum[i]),
                        .ow_carry(w_c[i+1])
                    );
                end
            endgenerate
        
            assign ow_carry = w_c[N];  // output the final carry
        
        endmodule : math_adder_full_nbit
        
