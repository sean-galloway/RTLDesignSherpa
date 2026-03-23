// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for find_last_set (yosys-compatible)

module formal_find_last_set #(
    parameter int WIDTH = 8,
    parameter int N = $clog2(WIDTH)
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] data;

    logic [N-1:0] index;

    find_last_set #(.WIDTH(WIDTH)) dut (
        .data (data),
        .index(index)
    );

    // When any bit is set, the indexed bit must be 1
    always @(posedge clk)
        if (|data)
assert (data[index]);

    // When any bit is set, all bits above index must be 0
    // Mask: bits [WIDTH-1 : index+1] must all be zero
    always @(posedge clk)
        if (|data && index < WIDTH - 1)
assert ((data >> (index + 1)) == '0);

    // When no bits are set, index is zero
    always @(posedge clk)
        if (data == '0)
assert (index == '0);

    // Output is in valid range
    always @(posedge clk)
        if (|data)
assert (index < WIDTH);

    // When exactly one bit is set, index matches that bit position
    always @(posedge clk)
        if ($onehot(data))
assert (data == (WIDTH'(1) << index));

    // Cover: index at each position
    generate
        genvar i;
        for (i = 0; i < WIDTH; i++) begin : gen_cover
            always @(posedge clk)
cover (|data && index == N'(i));
        end
    endgenerate

    // Cover: all zeros
    always @(posedge clk)
cover (data == '0);

endmodule
