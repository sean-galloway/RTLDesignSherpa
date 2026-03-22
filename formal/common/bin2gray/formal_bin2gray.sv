// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for bin2gray (yosys-compatible)
// Proves Gray code conversion correctness: formula, single-bit change, MSB preserved.

module formal_bin2gray #(
    parameter int WIDTH = 4
) (
    input  logic clk
);

    // =========================================================================
    // Free inputs -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] binary;
    logic [WIDTH-1:0] gray;

    // Instantiate DUT
    bin2gray #(.WIDTH(WIDTH)) dut (
        .binary (binary),
        .gray   (gray)
    );

    // =========================================================================
    // Helper: Gray code for an arbitrary value (used for single-bit check)
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] probe_bin;
    logic [WIDTH-1:0] probe_gray;
    logic [WIDTH-1:0] probe_next_gray;

    bin2gray #(.WIDTH(WIDTH)) u_probe (
        .binary (probe_bin),
        .gray   (probe_gray)
    );

    bin2gray #(.WIDTH(WIDTH)) u_probe_next (
        .binary (WIDTH'(probe_bin + 1)),
        .gray   (probe_next_gray)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Gray code formula: gray == binary ^ (binary >> 1)
    always @(posedge clk) begin
        ap_formula: assert (gray == (binary ^ (binary >> 1)));
    end

    // MSB preserved: gray[WIDTH-1] == binary[WIDTH-1]
    always @(posedge clk) begin
        ap_msb_preserved: assert (gray[WIDTH-1] == binary[WIDTH-1]);
    end

    // Zero maps to zero: binary == 0 implies gray == 0
    always @(posedge clk) begin
        if (binary == '0)
            ap_zero_maps_zero: assert (gray == '0);
    end

    // Single-bit change: consecutive binary values produce Gray codes
    // differing in exactly 1 bit. Uses anyconst probe to check universally.
    always @(posedge clk) begin
        ap_single_bit_change: assert ($countones(probe_gray ^ probe_next_gray) == 1);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover zero input
    always @(posedge clk) begin
        cp_zero: cover (binary == '0);
    end

    // Cover max input
    always @(posedge clk) begin
        cp_max: cover (binary == {WIDTH{1'b1}});
    end

    // Cover midpoint
    always @(posedge clk) begin
        cp_mid: cover (binary == {1'b1, {(WIDTH-1){1'b0}}});
    end

    // Cover alternating bits
    always @(posedge clk) begin
        cp_alt: cover (binary == {WIDTH/2{2'b10}});
    end

    // Cover MSB transition in Gray output
    always @(posedge clk) begin
        cp_gray_msb_set: cover (gray[WIDTH-1] == 1'b1);
    end

endmodule
