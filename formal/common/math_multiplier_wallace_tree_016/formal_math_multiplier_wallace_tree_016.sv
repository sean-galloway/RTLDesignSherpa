// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_multiplier_wallace_tree_016
// Two-part strategy: prove_low8 (exhaustive 8-bit) + prove_boundary (power-of-2 edges)

module formal_math_multiplier_wallace_tree_016 #(
    parameter int N = 16
) (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Free inputs -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [N-1:0] a;
    (* anyconst *) logic [N-1:0] b;
    logic [2*N-1:0] product;

    // Instantiate DUT
    math_multiplier_wallace_tree_016 #(.N(N)) dut (
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
    // Core safety property
    // =========================================================================
    always @(posedge clk) begin
        ap_product: assert (product == ref_product);
    end

    // =========================================================================
    // Task-specific constraints
    // =========================================================================

`ifdef PROVE_LOW8
    // Exhaustive over lower 8 bits: 256 x 256 = 65536 combinations
    always @(*) begin
        assume (a[N-1:8] == '0);
        assume (b[N-1:8] == '0);
    end
`endif

`ifdef PROVE_BOUNDARY
    // Power-of-2 boundary values: {2^k-2, 2^k-1, 2^k, 2^k+1, 2^k+2} for k=0..N-1
    // Plus fixed: 0, 1, MAX-1, MAX
    // Uses generate loop (Yosys-compatible) to build the constraint.

    // --- Check if 'a' is an interesting value ---
    wire a_is_zero     = (a == {N{1'b0}});
    wire a_is_one      = (a == {{(N-1){1'b0}}, 1'b1});
    wire a_is_max      = (a == {N{1'b1}});
    wire a_is_max_m1   = (a == ({N{1'b1}} - {{(N-1){1'b0}}, 1'b1}));
    wire a_is_two      = (a == {{(N-2){1'b0}}, 2'b10});
    wire a_is_three    = (a == {{(N-2){1'b0}}, 2'b11});

    // --- Check if 'b' is an interesting value ---
    wire b_is_zero     = (b == {N{1'b0}});
    wire b_is_one      = (b == {{(N-1){1'b0}}, 1'b1});
    wire b_is_max      = (b == {N{1'b1}});
    wire b_is_max_m1   = (b == ({N{1'b1}} - {{(N-1){1'b0}}, 1'b1}));
    wire b_is_two      = (b == {{(N-2){1'b0}}, 2'b10});
    wire b_is_three    = (b == {{(N-2){1'b0}}, 2'b11});

    // Generate per-k boundary checks
    wire [N-1:0] a_pow2_match;
    wire [N-1:0] a_pow2p1_match;
    wire [N-1:0] a_pow2p2_match;
    wire [N-1:0] a_pow2m1_match;
    wire [N-1:0] a_pow2m2_match;
    wire [N-1:0] b_pow2_match;
    wire [N-1:0] b_pow2p1_match;
    wire [N-1:0] b_pow2p2_match;
    wire [N-1:0] b_pow2m1_match;
    wire [N-1:0] b_pow2m2_match;

    generate
        genvar k;
        for (k = 1; k < N; k = k + 1) begin : gen_boundary
            localparam [N-1:0] POW2   = (1 << k);
            localparam [N-1:0] POW2P1 = (1 << k) + 1;
            localparam [N-1:0] POW2P2 = (1 << k) + 2;
            localparam [N-1:0] POW2M1 = (1 << k) - 1;
            localparam [N-1:0] POW2M2 = (k >= 2) ? ((1 << k) - 2) : 0;

            assign a_pow2_match[k]   = (a == POW2);
            assign a_pow2p1_match[k] = (a == POW2P1);
            assign a_pow2p2_match[k] = (a == POW2P2);
            assign a_pow2m1_match[k] = (a == POW2M1);
            assign a_pow2m2_match[k] = (k >= 2) ? (a == POW2M2) : 1'b0;

            assign b_pow2_match[k]   = (b == POW2);
            assign b_pow2p1_match[k] = (b == POW2P1);
            assign b_pow2p2_match[k] = (b == POW2P2);
            assign b_pow2m1_match[k] = (b == POW2M1);
            assign b_pow2m2_match[k] = (k >= 2) ? (b == POW2M2) : 1'b0;
        end
    endgenerate

    // k=0 is unused in the generate loop; tie off bit 0
    assign a_pow2_match[0]   = 1'b0;
    assign a_pow2p1_match[0] = 1'b0;
    assign a_pow2p2_match[0] = 1'b0;
    assign a_pow2m1_match[0] = 1'b0;
    assign a_pow2m2_match[0] = 1'b0;
    assign b_pow2_match[0]   = 1'b0;
    assign b_pow2p1_match[0] = 1'b0;
    assign b_pow2p2_match[0] = 1'b0;
    assign b_pow2m1_match[0] = 1'b0;
    assign b_pow2m2_match[0] = 1'b0;

    wire a_ok = a_is_zero | a_is_one | a_is_max | a_is_max_m1 |
                a_is_two  | a_is_three |
                (|a_pow2_match) | (|a_pow2p1_match) | (|a_pow2p2_match) |
                (|a_pow2m1_match) | (|a_pow2m2_match);

    wire b_ok = b_is_zero | b_is_one | b_is_max | b_is_max_m1 |
                b_is_two  | b_is_three |
                (|b_pow2_match) | (|b_pow2p1_match) | (|b_pow2p2_match) |
                (|b_pow2m1_match) | (|b_pow2m2_match);

    always @(*) begin
        assume (a_ok);
        assume (b_ok);
    end
`endif

endmodule
