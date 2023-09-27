`timescale 1ns / 1ps

module math_subtractor_ripple_carry #(
    parameter int N = 4  // Width of input and output data
) (
    input  logic [N-1:0] i_a,            // Input a
    input  logic [N-1:0] i_b,            // Input b
    input  logic         i_borrow_in,    // Borrow in
    output logic [N-1:0] ow_difference,  // Output difference (a - b)
    output logic         ow_carry_out    // Borrow out (carry out) after subtraction
);

    logic [N-1:0] w_borrow;

    // First stage uses the external borrow-in
    math_subtractor_full fs0 (
        .i_a(i_a[0]),
        .i_b(i_b[0]),
        .i_b_in(i_borrow_in),
        .ow_d(ow_difference[0]),
        .ow_b(w_borrow[0])
    );

    // Generate subsequent stages
    genvar i;
    generate
        for (i = 1; i < N; i++) begin : gen_stages
            math_subtractor_full fs (
                .i_a(i_a[i]),
                .i_b(i_b[i]),
                .i_b_in(w_borrow[i-1]),
                .ow_d(ow_difference[i]),
                .ow_b(w_borrow[i])
            );
        end
    endgenerate

    // Final borrow out (carry out)
    assign ow_carry_out = w_borrow[N-1];

endmodule : math_subtractor_ripple_carry
