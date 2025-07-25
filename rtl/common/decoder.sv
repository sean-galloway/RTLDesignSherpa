`timescale 1ns / 1ps

module decoder #(
    parameter int M = 4,  // Number of input bits
    parameter int N = 2 ** M  // Number of output bits)
) (
    input  [M-1:0] encoded,
    output [N-1:0] data
);

    assign data = 0;  // Initialize the output

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_DECODER_LOOP
            assign data[i] = (encoded == i) ? 1'b1 : 1'b0;
        end
    endgenerate

endmodule : decoder
