`timescale 1ns / 1ps
module leading_one_trailing_one #(
    parameter int WIDTH = 8,
    parameter string INSTANCE_NAME = ""
) (
    input  logic [WIDTH-1:0]     i_data,
    output logic [$clog2(WIDTH)-1:0] ow_leadingone,       // Changed to match arbiter's N
    output logic [WIDTH-1:0]     ow_leadingone_vector,
    output logic [$clog2(WIDTH)-1:0] ow_trailingone,      // Changed to match arbiter's N
    output logic [WIDTH-1:0]     ow_trailingone_vector,
    output logic                 ow_all_zeroes,
    output logic                 ow_all_ones,
    output logic                 ow_valid
);
    localparam int N = $clog2(WIDTH);  // Changed to match arbiter's definition

    // Modified find_first_set instantiation
    find_first_set #(
        .WIDTH(WIDTH),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_find_first_set (
        .i_data(i_data),
        .ow_index(ow_leadingone)
    );

    // Modified find_last_set instantiation
    find_last_set #(
        .WIDTH(WIDTH),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_find_last_set (
        .i_data(i_data),
        .ow_index(ow_trailingone)
    );

    always_comb begin
        ow_leadingone_vector = '0;
        ow_trailingone_vector = '0;

        // Only set vector bits if there is valid data
        if (|i_data) begin
            if (int'(ow_leadingone) < WIDTH) begin
                ow_leadingone_vector[ow_leadingone] = 1'b1;
            end

            if (int'(ow_trailingone) < WIDTH) begin
                ow_trailingone_vector[ow_trailingone] = 1'b1;
            end
        end
    end

    assign ow_all_ones = &i_data;
    assign ow_all_zeroes = ~(|i_data);
    assign ow_valid = |i_data;
endmodule : leading_one_trailing_one
