`timescale 1ns / 1ps

module gray2bin #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] gray,
    output wire [WIDTH-1:0] binary
);

    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_gray_to_bin
            assign binary[i] = ^(gray >> i);
        end
    endgenerate

endmodule : gray2bin
