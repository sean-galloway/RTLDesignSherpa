// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for gray2bin (yosys-compatible)
// Proves roundtrip identity: gray2bin(bin2gray(x)) == x, MSB preserved, zero maps to zero.

module formal_gray2bin #(
    parameter int WIDTH = 4
) (
    input  logic clk
);

    // =========================================================================
    // Free input -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] original_binary;

    // =========================================================================
    // Roundtrip: binary -> bin2gray -> gray2bin -> recovered_binary
    // =========================================================================
    logic [WIDTH-1:0] gray;
    logic [WIDTH-1:0] recovered_binary;

    bin2gray #(.WIDTH(WIDTH)) u_encode (
        .binary (original_binary),
        .gray   (gray)
    );

    gray2bin #(.WIDTH(WIDTH)) u_decode (
        .gray   (gray),
        .binary (recovered_binary)
    );

    // =========================================================================
    // Direct gray2bin test with free Gray input
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] free_gray;
    logic [WIDTH-1:0] free_binary;

    gray2bin #(.WIDTH(WIDTH)) u_direct (
        .gray   (free_gray),
        .binary (free_binary)
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

    // Roundtrip identity: gray2bin(bin2gray(x)) == x
    always @(posedge clk) begin
        ap_roundtrip: assert (recovered_binary == original_binary);
    end

    // MSB preserved: gray[WIDTH-1] == binary[WIDTH-1] (through encode)
    always @(posedge clk) begin
        ap_msb_encode: assert (gray[WIDTH-1] == original_binary[WIDTH-1]);
    end

    // MSB preserved: in direct decode, gray MSB == binary MSB
    always @(posedge clk) begin
        ap_msb_decode: assert (free_gray[WIDTH-1] == free_binary[WIDTH-1]);
    end

    // Zero maps to zero: gray == 0 implies binary == 0
    always @(posedge clk) begin
        if (free_gray == '0)
            ap_zero_maps_zero: assert (free_binary == '0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover zero roundtrip
    always @(posedge clk) begin
        cp_zero: cover (original_binary == '0 && recovered_binary == '0);
    end

    // Cover max roundtrip
    always @(posedge clk) begin
        cp_max: cover (original_binary == {WIDTH{1'b1}} && recovered_binary == {WIDTH{1'b1}});
    end

    // Cover midpoint
    always @(posedge clk) begin
        cp_mid: cover (original_binary == {1'b1, {(WIDTH-1){1'b0}}});
    end

    // Cover alternating pattern
    always @(posedge clk) begin
        cp_alt: cover (original_binary == {WIDTH/2{2'b10}});
    end

    // Cover Gray code with single bit set
    always @(posedge clk) begin
        cp_gray_one_hot: cover (free_gray == {{(WIDTH-1){1'b0}}, 1'b1});
    end

endmodule
