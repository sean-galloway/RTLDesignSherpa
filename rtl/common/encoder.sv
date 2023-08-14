`timescale 1ns / 1ps

module encoder #(
    parameter N = 8
) (
    input  logic [N-1:0]         i_in,
    output logic [$clog2(N)-1:0] o_out
);
    always_comb begin
        out = 0;
        for (int i = 0; i < N; i++) begin
            if (i_in[i])
                o_out = i;
            end
        end
endmodule : encoder