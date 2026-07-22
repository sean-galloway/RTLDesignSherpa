// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: count_trailing_zeros
// Purpose: Counts consecutive zero bits from the LSB up to the first set bit
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: count_trailing_zeros
//
// Counts the number of consecutive zero bits starting at bit 0 and scanning
// upward, stopping at the first set bit.
//
//   data = 32'h0000_0001 -> ctz =  0   (bit 0 is set)
//   data = 32'h8000_0000 -> ctz = 31   (31 zeros below the MSB)
//   data = 32'h0000_0000 -> ctz = WIDTH
//
// For the count from the MSB downward, use count_leading_zeros.
//
// Parameters:
//   - WIDTH: input width in bits. Result is $clog2(WIDTH)+1 bits so that the
//            all-zeros case (ctz == WIDTH) is representable.
//==============================================================================
module count_trailing_zeros #(
    parameter int WIDTH = 32
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] ctz
);

    function automatic [$clog2(WIDTH):0] ctz_func;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            ctz_func = 0;
            found = 1'b0;
            // Scan from the LSB upward.
            for (int i = 0; i < WIDTH; i++) begin
                if (!input_data[i] && !found) begin
                    ctz_func += 1;
                end else begin
                    found = 1'b1;
                end
            end
        end
    endfunction

    always_comb begin
        ctz = ctz_func(data);
    end

endmodule : count_trailing_zeros
