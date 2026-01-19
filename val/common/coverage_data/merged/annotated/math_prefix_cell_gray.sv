//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_prefix_cell
        // Purpose: Prefix Cell for the Han-Carlson structure
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        module math_prefix_cell_gray (
%000000     input  logic i_g_hi, i_p_hi,
%000000     input  logic i_g_lo,           // No P needed from lower position
%000000     output logic ow_g              // Only G output (this IS the carry)
        );
            assign ow_g = i_g_hi | (i_p_hi & i_g_lo);
        
        endmodule : math_prefix_cell_gray
        
