// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for count_trailing_zeros (yosys-compatible)
//
// Counterpart to formal/common/count_leading_zeros/. These properties describe a
// scan from the LSB upward: the bit AT ctz is set, and everything BELOW it is zero.

module formal_count_trailing_zeros #(
    parameter int WIDTH = 8,
    parameter int N = $clog2(WIDTH) + 1
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] data;

    logic [N-1:0] ctz;

    count_trailing_zeros #(.WIDTH(WIDTH)) dut (
        .data(data),
        .ctz (ctz)
    );

    // CTZ is in valid range [0, WIDTH]
    always @(posedge clk)
assert (ctz <= WIDTH);

    // All zeros -> CTZ == WIDTH
    always @(posedge clk)
        if (data == '0)
assert (ctz == N'(WIDTH));

    // Conversely, CTZ == WIDTH only for all zeros
    always @(posedge clk)
        if (ctz == N'(WIDTH))
assert (data == '0);

    // For nonzero data the bit at ctz is the first set bit from the bottom
    always @(posedge clk)
        if (data != '0)
assert (data[ctz]);

    // Everything below that bit must be zero
    always @(posedge clk)
        if (data != '0 && ctz > 0)
assert ((data & ((WIDTH'(1) << ctz) - 1)) == '0);

    // LSB set -> CTZ is 0
    always @(posedge clk)
        if (data[0])
assert (ctz == '0);

    // Only the MSB set -> CTZ is WIDTH-1
    always @(posedge clk)
        if (data == (WIDTH'(1) << (WIDTH - 1)))
assert (ctz == N'(WIDTH - 1));

    // Cover: CTZ == 0 (LSB set)
    always @(posedge clk)
cover (ctz == '0 && data != '0);

    // Cover: CTZ == WIDTH (all zeros)
    always @(posedge clk)
cover (ctz == N'(WIDTH));

    // Cover: CTZ == WIDTH/2
    always @(posedge clk)
cover (ctz == N'(WIDTH / 2));

    // Cover: various CTZ values
    always @(posedge clk) begin
cover (ctz == N'(1));
cover (ctz == N'(WIDTH - 1));
    end

endmodule
