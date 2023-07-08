`timescale 1ns / 1ps

module leading_one_trailing_one #(parameter N=8) (
    input      [N-1:0]       data,
    output reg [$clog2(N):0] leadingone,
    output reg [$clog2(N):0] trailingone,
    output reg all_zeroes
);

    always @(*) begin
        if (data === 0) begin
            leadingone = $clog2(N);
            trailingone = $clog2(N);
            all_zeroes = 1;
        end
        else begin
            leadingone = $clog2(N) - 1 - $clz(data);
            trailingone = $ffs(data) - 1;
            all_zeroes = 0;
        end
    end

endmodule
