`timescale 1ns / 1ps

module grayj2bin #(
    parameter int    JCW = 10,
    parameter int    WIDTH = 4,
    parameter string INSTANCE_NAME = ""
) (
    input  logic              i_clk,
    input  logic              i_rst_n,
    input  logic  [JCW-1:0]   i_gray,
    output logic  [WIDTH-1:0] ow_binary
);

    localparam int N = $clog2(JCW);

    logic [N-1:0]     w_leading_one;
    logic [N-1:0]     w_trailing_one;
    logic [WIDTH-1:0] w_binary;
    logic [WIDTH-1:0] w_padded_leading;
    logic [WIDTH-1:0] w_padded_trailing;
    logic             w_all_zeroes;
    logic             w_all_ones;
    logic             w_valid;

    // Leading/trailing detection
    leading_one_trailing_one #(
        .WIDTH(JCW),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_leading_one_trailing_one (
        .i_data               (i_gray),
        .ow_leadingone        (w_leading_one),
        .ow_leadingone_vector (),
        .ow_trailingone       (w_trailing_one),
        .ow_trailingone_vector(),
        .ow_all_zeroes        (w_all_zeroes),
        .ow_all_ones          (w_all_ones),
        .ow_valid             (w_valid)
    );

    // Safe padded binary construction
    logic [WIDTH-N-1:0] zero_padding_lead, zero_padding_trail;
    logic [N-1:0]       trail_plus_1;

    always_comb begin
        zero_padding_lead  = '0;
        zero_padding_trail = '0;
        trail_plus_1       = w_trailing_one + 1;

        w_padded_leading  = {zero_padding_lead,  w_leading_one};
        w_padded_trailing = {zero_padding_trail, trail_plus_1};

        if (w_all_zeroes || w_all_ones)
            w_binary = {WIDTH{1'b0}};
        else if (i_gray[JCW-1])
            w_binary = w_padded_leading;
        else
            w_binary = w_padded_trailing;
    end

    assign ow_binary[WIDTH-1]   = i_gray[JCW-1];               // MSB = wrap
    assign ow_binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower binary

endmodule : grayj2bin
