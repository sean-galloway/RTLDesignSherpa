`timescale 1ns / 1ps

module grayj2bin #(
    parameter int    JCW = 10,
    parameter int    WIDTH = 4,
    parameter string INSTANCE_NAME = ""
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic  [JCW-1:0]   gray,
    output logic  [WIDTH-1:0] binary
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
        .data               (gray),
        .leadingone        (w_leading_one),
        .leadingone_vector (),
        .trailingone       (w_trailing_one),
        .trailingone_vector(),
        .all_zeroes        (w_all_zeroes),
        .all_ones          (w_all_ones),
        .valid             (w_valid)
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
        else if (gray[JCW-1])
            w_binary = w_padded_leading;
        else
            w_binary = w_padded_trailing;
    end

    assign binary[WIDTH-1]   = gray[JCW-1];               // MSB = wrap
    assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower binary

endmodule : grayj2bin
