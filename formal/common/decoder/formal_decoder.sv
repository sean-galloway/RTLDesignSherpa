// SPDX-License-Identifier: MIT
module formal_decoder (input logic clk);
    (* anyconst *) logic [3:0] encoded;
    wire [15:0] data;
    decoder #(.M(4)) dut (.encoded(encoded), .data(data));
    always @(posedge clk) begin
        cp_zero_in: cover (encoded == 4'd0 && data != 16'd0);
        cp_max_in: cover (encoded == 4'd15 && data != 16'd0);
        cp_mid: cover (encoded == 4'd7 && data != 16'd0);
    end
endmodule
