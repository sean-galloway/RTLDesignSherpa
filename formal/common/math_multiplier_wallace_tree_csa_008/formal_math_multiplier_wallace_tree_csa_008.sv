// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_multiplier_wallace_tree_csa_008
// Proves 8-bit Wallace tree CSA multiplier: product == a * b

module formal_math_multiplier_wallace_tree_csa_008 #(
    parameter int N = 8
) (
    input logic clk
);

    // =========================================================================
    // Free inputs -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [N-1:0]   a;
    (* anyconst *) logic [N-1:0]   b;
    logic [2*N-1:0] product;

    // Instantiate DUT
    math_multiplier_wallace_tree_csa_008 #(.N(N)) dut (
        .i_multiplier  (a),
        .i_multiplicand(b),
        .ow_product    (product)
    );

    // =========================================================================
    // Reference model
    // =========================================================================
    logic [2*N-1:0] ref_product;
    assign ref_product = {{N{1'b0}}, a} * {{N{1'b0}}, b};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Product matches reference multiplication
    always @(posedge clk) begin
        ap_product: assert (product == ref_product);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover zero * zero
    always @(posedge clk) begin
        cp_zero: cover (a == '0 && b == '0);
    end

    // Cover one * one
    always @(posedge clk) begin
        cp_one: cover (a == 8'd1 && b == 8'd1);
    end

    // Cover max * max
    always @(posedge clk) begin
        cp_max: cover (a == 8'hFF && b == 8'hFF);
    end

    // Cover max * 1
    always @(posedge clk) begin
        cp_max_by_one: cover (a == 8'hFF && b == 8'd1);
    end

    // Cover power-of-2 multiplication
    always @(posedge clk) begin
        cp_pow2: cover (a == 8'd16 && b == 8'd16);
    end

    // Cover near-max product (255 * 254 = 64770 = 0xFD02)
    always @(posedge clk) begin
        cp_near_max: cover (a == 8'hFF && b == 8'hFE);
    end

endmodule
