// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for encoder_priority_enable (yosys-compatible)

module formal_encoder_priority_enable #(
    parameter int WIDTH = 8,
    parameter int N = $clog2(WIDTH)
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] priority_in;
    (* anyconst *) logic             enable;

    logic [N-1:0] encode;

    encoder_priority_enable #(.WIDTH(WIDTH)) dut (
        .priority_in(priority_in),
        .enable     (enable),
        .encode     (encode)
    );

    // When disabled, output is zero
    always @(posedge clk)
        if (!enable)
assert (encode == '0);

    // When enabled with no bits set, output is zero
    always @(posedge clk)
        if (enable && priority_in == '0)
assert (encode == '0);

    // When enabled with input, the indicated bit is set in priority_in
    always @(posedge clk)
        if (enable && |priority_in)
assert (priority_in[encode]);

    // When enabled, encode points to the highest set bit (no higher bit is set)
    always @(posedge clk)
        if (enable && |priority_in && encode < WIDTH - 1)
assert ((priority_in >> (encode + 1)) == '0);

    // Output is in valid range
    always @(posedge clk)
        if (enable && |priority_in)
assert (encode < WIDTH);

    // Cover: various input patterns
    always @(posedge clk) begin
cover (enable && $onehot(priority_in));
cover (enable && $countones(priority_in) > 1);
cover (enable && &priority_in);
cover (!enable && |priority_in);
cover (enable && priority_in[0]);
cover (enable && priority_in[WIDTH-1] && !priority_in[0]);
    end

endmodule
