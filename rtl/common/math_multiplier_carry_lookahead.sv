`timescale 1ns / 1ps

module math_multiplier_carry_lookahead #(
    parameter N = 4
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
    localparam int Nybble = 4;
    localparam int PpSize = N * N;
    localparam int CarrySize = N + 1;  // Just one carry per addition stage needed

    logic [PpSize-1:0] partial_products;
    logic [CarrySize-1:0] carries;

    // Generate partial products
    genvar i, j;
    generate
        for (i = 0; i < N; i++) begin : gen_pp
            for (j = 0; j < N; j++) begin : gen_pp_bit
                assign partial_products[i*N+j] = i_multiplicand[j] & i_multiplier[i];
            end
        end
    endgenerate

    // Initialize carries[0] for the first stage
    initial carries[0] = 0;

    // Carry Look-Ahead Adder Logic for partial products addition
    generate
        for (i = 0; i < N; i += Nybble) begin : gen_cla_logic
            math_adder_carry_lookahead #(
                .N(Nybble)
            ) cla_adder (
                .i_a(partial_products[i*Nybble+:Nybble]),
                .i_b({Nybble{1'b0}}),  // Assuming i_b is not used for your logic
                .i_c(carries[i/Nybble]),
                .ow_sum(ow_product[i*2+:Nybble]),
                .ow_carry(carries[i/Nybble+1])
            );
        end
    endgenerate
endmodule

