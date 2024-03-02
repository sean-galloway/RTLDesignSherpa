`timescale 1ns / 1ps

module leading_one_trailing_one #(
    parameter int WIDTH = 8,
    parameter int INSTANCE_NAME = ""
) (
    input  logic [      WIDTH-1:0] i_data,
    output logic [$clog2(WIDTH):0] ow_leadingone,
    output logic [      WIDTH-1:0] ow_leadingone_vector,
    output logic [$clog2(WIDTH):0] ow_trailingone,
    output logic [      WIDTH-1:0] ow_trailingone_vector,
    output logic                   ow_all_zeroes,
    output logic                   ow_all_ones,
    output logic                   ow_valid
);

    localparam int N = $clog2(WIDTH) + 1;

    logic [N-1:0] first_set_index;
    logic [N-1:0] leading_zeros_count;

    find_first_set #(
        .WIDTH(WIDTH),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_find_first_set (
        .i_data  (i_data),
        .ow_index(ow_leadingone)
    );

    find_last_set #(
        .WIDTH(WIDTH),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_find_last_set (
        .i_data  (i_data),
        .ow_index(ow_trailingone)
    );

    always_comb begin
        ow_leadingone_vector = '0;
        ow_leadingone_vector[ow_leadingone-1] = 1'b1;  // Subtract 1 to convert to 0-based index
        ow_trailingone_vector = '0;
        ow_trailingone_vector[ow_trailingone-1] = 1'b1;  // Subtract 1 to convert to 0-based index
    end

    assign ow_all_ones   = &i_data;
    assign ow_all_zeroes = ~(|i_data);
    assign ow_valid      = |i_data;

    // synopsys translate_off
    // initial begin
    // $dumpfile("waves.vcd")
    // $dumpvars(0, leading_one_trailing_one);
    // end
    // synopsys translate_on

endmodule : leading_one_trailing_one

