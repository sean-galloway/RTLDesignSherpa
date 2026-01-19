//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_adder_full
        // Purpose: Math Adder Full module
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        // Simple Full Adder implemented
        module math_adder_full #(parameter int N=1) (
%000002     input  logic i_a,
%000002     input  logic i_b,
%000002     input  logic i_c,
 000010     output logic ow_sum,
%000000     output logic ow_carry
        );
        
            assign ow_sum   = i_a ^ i_b ^ i_c;  // XOR gate for sum output
            assign ow_carry = (i_a & i_b) | (i_c & (i_a ^ i_b));  // OR gate for carry output
        
        endmodule : math_adder_full
        
