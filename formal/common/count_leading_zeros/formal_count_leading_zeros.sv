// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for count_leading_zeros (yosys-compatible)
//
// NOTE: an earlier version of this wrapper asserted TRAILING-zero properties
// (data[clz] set, all bits BELOW clz zero) because the module under test scanned
// from bit 0 upward. Both have been corrected. The properties below describe a
// true CLZ: scan from the MSB down. For the trailing-zero counterpart see
// formal/common/count_trailing_zeros/.

module formal_count_leading_zeros #(
    parameter int WIDTH = 8,
    parameter int N = $clog2(WIDTH) + 1
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] data;

    logic [N-1:0] clz;

    count_leading_zeros #(.WIDTH(WIDTH)) dut (
        .data(data),
        .clz (clz)
    );

    // Index of the first set bit counted from the MSB. Only meaningful when
    // data != 0, which every property using it is guarded on.
    logic [N-1:0] w_first_set_idx;
    assign w_first_set_idx = N'(WIDTH - 1) - clz;

    // Number of leading bit positions that must be zero.
    logic [N-1:0] w_shift;
    assign w_shift = N'(WIDTH) - clz;

    // CLZ is in valid range [0, WIDTH]
    always @(posedge clk)
assert (clz <= WIDTH);

    // All zeros -> CLZ == WIDTH
    always @(posedge clk)
        if (data == '0)
assert (clz == N'(WIDTH));

    // Conversely, CLZ == WIDTH only for all zeros
    always @(posedge clk)
        if (clz == N'(WIDTH))
assert (data == '0);

    // For nonzero data the bit at (WIDTH-1-clz) is the first set bit from the top
    always @(posedge clk)
        if (data != '0)
assert (data[w_first_set_idx]);

    // Everything above that bit must be zero
    always @(posedge clk)
        if (data != '0 && clz > 0)
assert ((data >> w_shift) == '0);

    // MSB set -> CLZ is 0
    always @(posedge clk)
        if (data[WIDTH-1])
assert (clz == '0);

    // Only the LSB set -> CLZ is WIDTH-1
    always @(posedge clk)
        if (data == WIDTH'(1))
assert (clz == N'(WIDTH - 1));

    // Cover: CLZ == 0 (MSB set)
    always @(posedge clk)
cover (clz == '0 && data != '0);

    // Cover: CLZ == WIDTH (all zeros)
    always @(posedge clk)
cover (clz == N'(WIDTH));

    // Cover: CLZ == WIDTH/2
    always @(posedge clk)
cover (clz == N'(WIDTH / 2));

    // Cover: various CLZ values
    always @(posedge clk) begin
cover (clz == N'(1));
cover (clz == N'(WIDTH - 1));
    end

endmodule
