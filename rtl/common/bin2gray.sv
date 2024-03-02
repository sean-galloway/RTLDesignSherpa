`timescale 1ns / 1ps

module bin2gray #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] i_binary,
    output wire [WIDTH-1:0] ow_gray
);

    genvar i;
    generate
        for (i = 0; i < WIDTH - 1; i++) begin : gen_gray
            assign ow_gray[i] = i_binary[i] ^ i_binary[i+1];
        end
    endgenerate

    assign ow_gray[WIDTH-1] = i_binary[WIDTH-1];

    // synopsys translate_off
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, bin2gray);
    end
    // synopsys translate_on

endmodule : bin2gray
