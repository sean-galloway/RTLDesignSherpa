// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for count_leading_zeros (yosys-compatible)

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

    // CLZ is in valid range [0, WIDTH]
    always @(posedge clk)
assert (clz <= WIDTH);

    // When data is all zeros, CLZ equals WIDTH
    always @(posedge clk)
        if (data == '0)
assert (clz == N'(WIDTH));

    // When data is nonzero, the first set bit from bit[0] is at position clz
    // The CLZ module scans from bit[0] upward, counting zeros until first 1
    // So data[clz] should be 1 (the first set bit found)
    always @(posedge clk)
        if (data != '0)
assert (data[clz]);

    // All bits below the first set bit must be zero
    always @(posedge clk)
        if (data != '0 && clz > 0)
assert ((data & ((WIDTH'(1) << clz) - 1)) == '0);

    // When MSB (bit[0]) is set, CLZ is 0
    always @(posedge clk)
        if (data[0])
assert (clz == '0);

    // Cover: CLZ == 0 (bit[0] set)
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
