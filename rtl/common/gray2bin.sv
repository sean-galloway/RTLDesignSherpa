`timescale 1ns / 1ps

module gray2bin #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] i_gray,
    output wire [WIDTH-1:0] ow_binary
);

    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_gray_to_bin
            assign ow_binary[i] = ^(i_gray >> i);
        end
    endgenerate

endmodule : gray2bin
