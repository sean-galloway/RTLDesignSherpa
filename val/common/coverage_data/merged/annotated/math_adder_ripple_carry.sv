//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_adder_ripple_carry
        // Purpose: Math Adder Ripple Carry module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        
        module math_adder_ripple_carry #(
            parameter int N = 4
        ) (
%000001     input  logic [N-1:0] i_a,
 000031     i_b,
 000511     input  logic         i_c,
 000033     output logic [N-1:0] ow_sum,
 000031     output logic         ow_carry  // A single bit indicating final carry out
        );
        
 000031     logic [N-1:0] w_c;  // Intermediate carries for each bit
        
            math_adder_full fa0 (
                .i_a(i_a[0]),
                .i_b(i_b[0]),
                .i_c(i_c),
                .ow_sum(ow_sum[0]),
                .ow_carry(w_c[0])
            );
        
            genvar i;
            generate
                for (i = 1; i < N; i++) begin : gen_full_adders
                    math_adder_full fa (
                        .i_a(i_a[i]),
                        .i_b(i_b[i]),
                        .i_c(w_c[i-1]),
                        .ow_sum(ow_sum[i]),
                        .ow_carry(w_c[i])
                    );
                end
            endgenerate
        
            // Assign the final carry out
            assign ow_carry = w_c[N-1];
        
        endmodule : math_adder_ripple_carry
        
