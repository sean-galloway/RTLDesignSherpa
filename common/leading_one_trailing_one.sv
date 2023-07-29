`timescale 1ns / 1ps

module leading_one_trailing_one #(parameter WIDTH=8) (
    input  logic [WIDTH-1:0]           data,
    output logic [$clog2(WIDTH)-1:0]   leadingone,
    output logic [WIDTH-1:0]           leadingone_vector,
    output logic [$clog2(WIDTH)-1:0]   trailingone,
    output logic [WIDTH-1:0]           trailingone_vector,
    output logic                       all_zeroes,
    output logic                       valid
);

    localparam  N = $clog2(WIDTH);

    logic [N-1:0] first_set_index;
    logic [N-1:0] leading_zeros_count;

    find_first_set #(.WIDTH(WIDTH))
    u_find_first_set(
        .data            (data),
        .first_set_index (first_set_index)
    );

    count_leading_zeros #(.WIDTH(WIDTH))
    u_count_leading_zeros(
        .data                (data),
        .leading_zeros_count (leading_zeros_count)
    );

    always_comb begin
        if (data === 0) begin
            leadingone = N;
            trailingone = N;
            all_zeroes = 1;
        end
        else begin
            leadingone = N - leading_zeros_count; // $clog2(N) - $clz(data);
            trailingone = first_set_index; // $ffs(data);
            all_zeroes = 0;
        end
    end

    always_comb begin
        leadingone_vector = '0;
        leadingone_vector[leadingone - 1] = 1'b1; // Subtract 1 to convert to 0-based index
        trailingone_vector = '0;
        trailingone_vector[trailingone - 1] = 1'b1; // Subtract 1 to convert to 0-based index
    end

    assign valid = !all_zeroes;

endmodule : leading_one_trailing_one

