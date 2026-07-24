// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: count_leading_zeros
// Purpose: Counts consecutive zero bits from the MSB down to the first set bit
//
// Documentation: docs/markdown/RTLCommon/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: count_leading_zeros
//
// Counts the number of consecutive zero bits starting at the MSB and scanning
// downward, stopping at the first set bit.
//
//   data = 32'h8000_0000 -> clz =  0   (MSB is set)
//   data = 32'h0000_0001 -> clz = 31   (31 zeros above the LSB)
//   data = 32'h0000_0000 -> clz = WIDTH
//
// For the count from the LSB upward, use count_trailing_zeros.
//
// HISTORY: earlier revisions of this module scanned from bit 0 upward, which is
// count_trailing_zeros, not count_leading_zeros. Callers compensated by feeding
// it a bit-reversed input. Both the module and its callers have been corrected;
// do not reintroduce a reversal at the call site.
//
// Parameters:
//   - WIDTH: input width in bits. Result is $clog2(WIDTH)+1 bits so that the
//            all-zeros case (clz == WIDTH) is representable.
//==============================================================================
module count_leading_zeros #(
    parameter int WIDTH = 32
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] clz
);

    function automatic [$clog2(WIDTH):0] clz_func;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            clz_func = 0;
            found = 1'b0;
            // Scan from the MSB downward.
            for (int i = WIDTH - 1; i >= 0; i--) begin
                if (!input_data[i] && !found) begin
                    clz_func += 1;
                end else begin
                    found = 1'b1;
                end
            end
        end
    endfunction

    always_comb begin
        clz = clz_func(data);
    end

endmodule : count_leading_zeros
