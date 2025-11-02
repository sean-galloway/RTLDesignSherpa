// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: find_last_set
// Purpose: //   Finds the position (index) of the most significant '1' bit in the input
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: find_last_set
//==============================================================================
// Description:
//   Finds the position (index) of the most significant '1' bit in the input
//   vector. Scans from MSB (bit WIDTH-1) to LSB, returning the index of the
//   first set bit encountered. Returns 0 if no bits are set. Commonly used in
//   count leading zeros (CLZ) and normalization operations.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Input vector width in bits
//     Type: int
//     Range: 2 to 256
//     Default: 32
//     Constraints: Determines output index width ($clog2(WIDTH))
//
//   Derived Parameters (localparam - computed automatically):
//     N: Output index width ($clog2(WIDTH))
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Combinational logic (no clock/reset required)
//   - Returns index 0 if input is all zeros (no bit set)
//   - For count leading zeros: CLZ = WIDTH - 1 - index
//   - Priority: Higher bit indices have higher priority
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - find_first_set.sv - Finds LSB set bit (trailing one)
//   - leading_one_trailing_one.sv - Combined leading/trailing detection
//   - count_leading_zeros.sv - Dedicated CLZ implementation
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_find_last_set.py
//   Run: pytest val/common/test_find_last_set.py -v
//
//==============================================================================
module find_last_set #(
    parameter int WIDTH = 32,
    parameter string INSTANCE_NAME = "FLS"
) (
    input  logic [WIDTH-1:0] data,
    output logic [$clog2(WIDTH)-1:0] index  // Changed to match arbiter's N
);
    localparam int N = $clog2(WIDTH);  // Changed to match arbiter's definition
    logic w_found;

    always_comb begin
        index = {N{1'b0}}; // Default value if no bit is set
        w_found = 1'b0;

        for (int i = WIDTH - 1; i >= 0; i--) begin
            if (data[i] && !w_found) begin
                index = i[N-1:0]; // Ensure correct bit width
                w_found = 1'b1;
            end
        end
    end
endmodule : find_last_set
