// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: leading_one_trailing_one
// Purpose: //   Combined leading and trailing '1' bit position detector. Finds both the
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: leading_one_trailing_one
//==============================================================================
// Description:
//   Combined leading and trailing '1' bit position detector. Finds both the
//   most significant (leading) and least significant (trailing) '1' bits in
//   the input vector, providing both index values and one-hot vectors. Also
//   detects all-zeros and all-ones conditions. Used in Gray code conversion
//   and Johnson counter decoding.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Input vector width in bits
//     Type: int
//     Range: 2 to 256
//     Default: 8
//     Constraints: Determines output index width ($clog2(WIDTH))
//
//   Derived Parameters (localparam - computed automatically):
//     N: Output index width ($clog2(WIDTH))
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Combinational logic (no clock/reset required)
//   - leadingone: Index of MSB set bit (0 if all zeros)
//   - trailingone: Index of LSB set bit (0 if all zeros)
//   - leadingone_vector: One-hot vector with MSB set bit marked
//   - trailingone_vector: One-hot vector with LSB set bit marked
//   - all_zeroes: Asserted when input = 0
//   - all_ones: Asserted when input = all 1s
//   - valid: Asserted when at least one bit is set
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - find_first_set.sv - Used internally for trailing one detection
//   - find_last_set.sv - Used internally for leading one detection
//   - grayj2bin.sv - Primary user of this module
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_leading_one_trailing_one.py
//   Run: pytest val/common/test_leading_one_trailing_one.py -v
//
//==============================================================================
module leading_one_trailing_one #(
    parameter int WIDTH = 8,
    parameter string INSTANCE_NAME = ""
) (
    input  logic [WIDTH-1:0]     data,
    output logic [$clog2(WIDTH)-1:0] leadingone,       // Changed to match arbiter's N
    output logic [WIDTH-1:0]     leadingone_vector,
    output logic [$clog2(WIDTH)-1:0] trailingone,      // Changed to match arbiter's N
    output logic [WIDTH-1:0]     trailingone_vector,
    output logic                 all_zeroes,
    output logic                 all_ones,
    output logic                 valid
);
    localparam int N = $clog2(WIDTH);  // Changed to match arbiter's definition

    find_last_set #(
        .WIDTH         (WIDTH),
        .INSTANCE_NAME (INSTANCE_NAME)
    ) u_find_last_set(
        .data          (data),
        .index         (leadingone)
    );

    find_first_set #(
        .WIDTH         (WIDTH),
        .INSTANCE_NAME (INSTANCE_NAME)
    ) u_find_first_set(
        .data          (data),
        .index         (trailingone)
    );

    always_comb begin
        leadingone_vector = '0;
        trailingone_vector = '0;

        // Only set vector bits if there is valid data
        if (|data) begin
            if (int'(leadingone) < WIDTH) begin
                leadingone_vector[leadingone] = 1'b1;
            end

            if (int'(trailingone) < WIDTH) begin
                trailingone_vector[trailingone] = 1'b1;
            end
        end
    end

    assign all_ones = &data;
    assign all_zeroes = ~(|data);
    assign valid = |data;
endmodule : leading_one_trailing_one
