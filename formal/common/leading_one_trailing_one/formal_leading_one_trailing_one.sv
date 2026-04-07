// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for leading_one_trailing_one (yosys-compatible)

module formal_leading_one_trailing_one #(
    parameter int WIDTH = 8,
    parameter int N = $clog2(WIDTH)
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] data;

    logic [N-1:0]     leadingone;
    logic [WIDTH-1:0] leadingone_vector;
    logic [N-1:0]     trailingone;
    logic [WIDTH-1:0] trailingone_vector;
    logic             all_zeroes;
    logic             all_ones;
    logic             valid;

    leading_one_trailing_one #(.WIDTH(WIDTH)) dut (
        .data              (data),
        .leadingone        (leadingone),
        .leadingone_vector (leadingone_vector),
        .trailingone       (trailingone),
        .trailingone_vector(trailingone_vector),
        .all_zeroes        (all_zeroes),
        .all_ones          (all_ones),
        .valid             (valid)
    );

    // =========================================================================
    // Safety properties: leadingone (MSB set bit index)
    // =========================================================================

    // When data is nonzero, leadingone index points to a set bit
    always @(posedge clk)
        if (|data)
            ap_leading_bit_set: assert (data[leadingone]);

    // No higher bit is set above the leadingone index
    always @(posedge clk)
        if (|data)
            ap_leading_is_highest: assert ((data >> (leadingone + 1)) == '0);

    // =========================================================================
    // Safety properties: trailingone (LSB set bit index)
    // =========================================================================

    // When data is nonzero, trailingone index points to a set bit
    always @(posedge clk)
        if (|data)
            ap_trailing_bit_set: assert (data[trailingone]);

    // No lower bit is set below the trailingone index
    always @(posedge clk)
        if (|data)
            ap_trailing_is_lowest: assert ((data & ((WIDTH'(1) << trailingone) - 1)) == '0);

    // =========================================================================
    // Safety properties: one-hot vectors
    // =========================================================================

    // leadingone_vector is one-hot when data is nonzero
    always @(posedge clk)
        if (|data)
            ap_leading_vec_onehot: assert ($onehot(leadingone_vector));

    // leadingone_vector has the bit at leadingone position set
    always @(posedge clk)
        if (|data)
            ap_leading_vec_matches: assert (leadingone_vector == (WIDTH'(1) << leadingone));

    // trailingone_vector is one-hot when data is nonzero
    always @(posedge clk)
        if (|data)
            ap_trailing_vec_onehot: assert ($onehot(trailingone_vector));

    // trailingone_vector has the bit at trailingone position set
    always @(posedge clk)
        if (|data)
            ap_trailing_vec_matches: assert (trailingone_vector == (WIDTH'(1) << trailingone));

    // When data is zero, vectors are all zeros
    always @(posedge clk)
        if (data == '0) begin
            ap_leading_vec_zero: assert (leadingone_vector == '0);
            ap_trailing_vec_zero: assert (trailingone_vector == '0);
        end

    // =========================================================================
    // Safety properties: flags
    // =========================================================================

    // all_zeroes asserted iff data == 0
    always @(posedge clk)
        ap_all_zeroes: assert (all_zeroes == (data == '0));

    // all_ones asserted iff data == all 1s
    always @(posedge clk)
        ap_all_ones: assert (all_ones == (&data));

    // valid asserted iff data != 0
    always @(posedge clk)
        ap_valid: assert (valid == (|data));

    // valid and all_zeroes are mutually exclusive
    always @(posedge clk)
        ap_valid_zeroes_exclusive: assert (!(valid && all_zeroes));

    // =========================================================================
    // Safety properties: index relationships
    // =========================================================================

    // leadingone >= trailingone when data is nonzero
    always @(posedge clk)
        if (|data)
            ap_leading_ge_trailing: assert (leadingone >= trailingone);

    // When exactly one bit is set, both indices are equal
    always @(posedge clk)
        if ($onehot(data))
            ap_single_bit_equal: assert (leadingone == trailingone);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (data == '0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (data == {WIDTH{1'b1}});

    // Cover: single bit set (one-hot)
    always @(posedge clk)
        cp_onehot: cover ($onehot(data));

    // Cover: MSB only set
    always @(posedge clk)
        cp_msb_only: cover (data == (WIDTH'(1) << (WIDTH - 1)));

    // Cover: LSB only set
    always @(posedge clk)
        cp_lsb_only: cover (data == WIDTH'(1));

    // Cover: multiple bits set with leading != trailing
    always @(posedge clk)
        cp_multi_bit: cover (|data && leadingone != trailingone);

    // Cover: alternating pattern
    always @(posedge clk)
        cp_alternating: cover (data == 8'hAA);

endmodule
