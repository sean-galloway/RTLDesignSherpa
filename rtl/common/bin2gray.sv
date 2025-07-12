`timescale 1ns / 1ps

module bin2gray #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] binary,
    output wire [WIDTH-1:0] gray
);

    genvar i;
    generate
        for (i = 0; i < WIDTH - 1; i++) begin : gen_gray
            assign gray[i] = binary[i] ^ binary[i+1];
        end
    endgenerate

    assign gray[WIDTH-1] = binary[WIDTH-1];

endmodule : bin2gray
