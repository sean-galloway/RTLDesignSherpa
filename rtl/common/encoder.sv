`timescale 1ns / 1ps

module encoder #(
    parameter int N = 8
) (
    input  logic [        N-1:0] decoded,
    output logic [$clog2(N)-1:0] data
);
    always_comb begin
        data = 0;
        for (int i = 0; i < N; i++) begin
            if (decoded[i]) data = $clog2(N)'(i);
        end
    end
endmodule : encoder
