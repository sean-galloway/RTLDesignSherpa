// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for grayj2bin (yosys-compatible)
// Proves Johnson-to-binary conversion correctness for valid Johnson codes.
// Johnson counter with JCW bits produces 2*JCW unique states.
// Valid codes: all-zeros, contiguous block of 1s from LSB, or contiguous block
// of 1s wrapping around MSB (falling fill).

module formal_grayj2bin #(
    parameter int JCW   = 8,
    parameter int WIDTH = 4
) (
    input  logic clk
);

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // =========================================================================
    // Free input -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [JCW-1:0] gray_input;
    logic [WIDTH-1:0] binary_output;

    // Instantiate DUT (clk/rst_n are ports but unused in combinational logic)
    grayj2bin #(
        .JCW   (JCW),
        .WIDTH (WIDTH)
    ) dut (
        .clk    (clk),
        .rst_n  (1'b1),
        .gray   (gray_input),
        .binary (binary_output)
    );

    // =========================================================================
    // Johnson code validity check
    // A valid Johnson code is either:
    //   - All zeros:    00000000
    //   - All ones:     11111111
    //   - Rising fill:  00000111 (contiguous 1s from LSB, MSB=0)
    //   - Falling fill: 11111000 (contiguous 1s from MSB, MSB=1)
    // =========================================================================
    logic is_all_zeros;
    logic is_all_ones;
    logic is_rising_fill;
    logic is_falling_fill;
    logic is_valid_johnson;

    assign is_all_zeros = (gray_input == '0);
    assign is_all_ones  = (gray_input == {JCW{1'b1}});

    // Rising fill: contiguous 1s from bit 0 upward, e.g., 00001111
    // gray+1 is a power of 2 when gray is a contiguous block of 1s from LSB
    logic [JCW-1:0] gray_plus_one;
    assign gray_plus_one = gray_input + 1'b1;
    assign is_rising_fill = !is_all_zeros && !is_all_ones &&
                            !gray_input[JCW-1] &&
                            ((gray_input & gray_plus_one) == '0);

    // Falling fill: contiguous 1s from MSB downward, e.g., 11110000
    // ~gray is a rising fill pattern
    logic [JCW-1:0] inv_gray;
    logic [JCW-1:0] inv_gray_plus_one;
    assign inv_gray = ~gray_input;
    assign inv_gray_plus_one = inv_gray + 1'b1;
    assign is_falling_fill = !is_all_zeros && !is_all_ones &&
                             gray_input[JCW-1] &&
                             ((inv_gray & inv_gray_plus_one) == '0);

    assign is_valid_johnson = is_all_zeros || is_all_ones ||
                              is_rising_fill || is_falling_fill;

    // =========================================================================
    // Expected binary output computation
    // Johnson counter sequence (JCW=8, 2*JCW=16 states):
    //   State 0:  00000000 -> binary = 0  (popcount=0)
    //   State 1:  00000001 -> binary = 1  (popcount=1)
    //   State 2:  00000011 -> binary = 2  (popcount=2)
    //   ...
    //   State 7:  01111111 -> binary = 7  (popcount=7)
    //   State 8:  11111111 -> binary = 8  (MSB=1, lower=0, zero_count=0)
    //   State 9:  11111110 -> binary = 9  (MSB=1, lower=1, zero_count=1)
    //   ...
    //   State 15: 10000000 -> binary = 15 (MSB=1, lower=7, zero_count=7)
    //
    // First half (MSB=0): binary[WIDTH-1]=0, binary[WIDTH-2:0]=popcount
    // Second half (MSB=1): binary[WIDTH-1]=1, binary[WIDTH-2:0]=zero_count
    // =========================================================================

    // Count number of 1s in gray input
    logic [$clog2(JCW+1):0] popcount;
    always_comb begin
        popcount = '0;
        for (int i = 0; i < JCW; i++)
            popcount = popcount + gray_input[i];
    end

    // Count number of 0s in gray input
    logic [$clog2(JCW+1):0] zero_count;
    always_comb begin
        zero_count = '0;
        for (int i = 0; i < JCW; i++)
            zero_count = zero_count + ~gray_input[i];
    end

    logic [WIDTH-1:0] expected_binary;
    always_comb begin
        if (is_all_zeros) begin
            expected_binary = '0;
        end else if (is_all_ones) begin
            // All ones: MSB=1, lower bits=0
            expected_binary = {1'b1, {(WIDTH-1){1'b0}}};
        end else if (is_rising_fill) begin
            // First half: MSB=0, lower = popcount of gray
            expected_binary = {1'b0, popcount[WIDTH-2:0]};
        end else if (is_falling_fill) begin
            // Second half: MSB=1, lower = count of zero bits
            expected_binary = {1'b1, zero_count[WIDTH-2:0]};
        end else begin
            // Invalid Johnson code -- no constraint
            expected_binary = binary_output;
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // All-zeros input produces zero output
    always @(posedge clk) begin
        if (is_all_zeros)
            ap_zero: assert (binary_output == '0);
    end

    // MSB of output matches MSB of Johnson code (wrap indicator)
    always @(posedge clk) begin
        ap_msb_wrap: assert (binary_output[WIDTH-1] == gray_input[JCW-1]);
    end

    // Valid Johnson codes produce correct binary output
    always @(posedge clk) begin
        if (is_valid_johnson)
            ap_valid_conversion: assert (binary_output == expected_binary);
    end

    // All-ones input produces JCW value (MSB set, lower bits zero)
    always @(posedge clk) begin
        if (is_all_ones)
            ap_all_ones: assert (binary_output == {1'b1, {(WIDTH-1){1'b0}}});
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover all-zeros input
    always @(posedge clk) begin
        cp_zero: cover (is_all_zeros);
    end

    // Cover all-ones input
    always @(posedge clk) begin
        cp_all_ones: cover (is_all_ones);
    end

    // Cover rising fill (first half)
    always @(posedge clk) begin
        cp_rising: cover (is_rising_fill);
    end

    // Cover falling fill (second half)
    always @(posedge clk) begin
        cp_falling: cover (is_falling_fill);
    end

    // Cover single bit set (state 1)
    always @(posedge clk) begin
        cp_single_bit: cover (gray_input == {{(JCW-1){1'b0}}, 1'b1});
    end

    // Cover single bit clear (state 2*JCW-1)
    always @(posedge clk) begin
        cp_single_clear: cover (gray_input == {{(JCW-1){1'b1}}, 1'b0});
    end

endmodule
