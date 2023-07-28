`timescale 1ns / 1ps

module leading_one_trailing_one #(parameter N=8) (
    input  logic [N-1:0]       data,
    output logic [$clog2(N):0] leadingone,
    output logic [N-1:0]       leadingone_vector,
    output logic [$clog2(N):0] trailingone,
    output logic [N-1:0]       trailingone_vector,
    output logic               all_zeroes,
    output logic               valid
);

    always_comb begin
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

    always_comb begin
        leadingone_vector = '0;
        leadingone_vector[leadingone] = 1'b1;
        trailingone_vector = '0;
        trailingone_vector[trailingone] = 1'b1;
        valid = !all_zeroes;
    end

endmodule : leading_one_trailing_one
