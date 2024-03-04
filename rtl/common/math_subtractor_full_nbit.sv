`timescale 1ns / 1ps

module math_subtractor_full_nbit #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_b_in,
    output logic [N-1:0] ow_d,
    output logic         ow_b
);

    logic [N-1:0] w_b_in, w_b_out;

    // Initialize borrow-in for the first bit
    assign w_b_in[0] = i_b_in;

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_subtractor_loop
            math_subtractor_full full_sub (
                .i_a(i_a[i]),
                .i_b(i_b[i]),
                .i_b_in(w_b_in[i]),
                .ow_d(ow_d[i]),
                .ow_b(w_b_out[i])
            );

            if (i < N - 1) assign w_b_in[i+1] = w_b_out[i];
        end
    endgenerate

    // Final borrow-out
    assign ow_b = w_b_out[N-1];

endmodule : math_subtractor_full_nbit
