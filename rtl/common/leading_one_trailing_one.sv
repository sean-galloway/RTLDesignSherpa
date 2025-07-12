`timescale 1ns / 1ps
module leading_one_trailing_one #(
    parameter int WIDTH = 8,
    parameter string INSTANCE_NAME = ""
) (
    input  logic [WIDTH-1:0]     data,
    output logic [$clog2(WIDTH)-1:0] leadingone,       // Changed to match arbiter's N
    output logic [WIDTH-1:0]     leadingone_vector,
    output logic [$clog2(WIDTH)-1:0] trailingone,      // Changed to match arbiter's N
    output logic [WIDTH-1:0]     trailingone_vector,
    output logic                 all_zeroes,
    output logic                 all_ones,
    output logic                 valid
);
    localparam int N = $clog2(WIDTH);  // Changed to match arbiter's definition

    find_last_set #(
        .WIDTH         (WIDTH),
        .INSTANCE_NAME (INSTANCE_NAME)
    ) u_find_last_set(
        .data          (data),
        .index         (leadingone)
    );

    find_first_set #(
        .WIDTH         (WIDTH),
        .INSTANCE_NAME (INSTANCE_NAME)
    ) u_find_first_set(
        .data          (data),
        .index         (trailingone)
    );

    always_comb begin
        leadingone_vector = '0;
        trailingone_vector = '0;

        // Only set vector bits if there is valid data
        if (|data) begin
            if (int'(leadingone) < WIDTH) begin
                leadingone_vector[leadingone] = 1'b1;
            end

            if (int'(trailingone) < WIDTH) begin
                trailingone_vector[trailingone] = 1'b1;
            end
        end
    end

    assign all_ones = &data;
    assign all_zeroes = ~(|data);
    assign valid = |data;
endmodule : leading_one_trailing_one
