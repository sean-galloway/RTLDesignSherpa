`timescale 1ns / 1ps

module grayj2bin #(
    parameter int JCW = 10,
    parameter int WIDTH = 4,
    parameter int INSTANCE_NAME = ""
) (
    input  logic             i_clk,
    input  logic             i_rst_n,
    input  logic [  JCW-1:0] i_gray,    // Width is DEPTH
    output logic [WIDTH-1:0] ow_binary  // Including the wrap bit
);

    localparam int N = $clog2(JCW) + 1;

    logic [N-1:0] w_leadingone, w_trailingone;
    logic [WIDTH-1:0] w_binary;
    logic w_all_zeroes, w_all_ones, w_valid;

    leading_one_trailing_one #(
        .WIDTH(JCW),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_leading_one_trailing_one (
        .i_data               (i_gray),
        .ow_leadingone        (w_leadingone),
        .ow_leadingone_vector (),
        .ow_trailingone       (w_trailingone),
        .ow_trailingone_vector(),
        .ow_all_zeroes        (w_all_zeroes),
        .ow_all_ones          (w_all_ones),
        .ow_valid             (w_valid)
    );

    always_comb begin
        if (w_all_zeroes || w_all_ones) w_binary = {WIDTH - 1{1'b0}};
        else if (i_gray[JCW-1] == 1'b1) w_binary = w_leadingone;
        else begin
            w_binary = w_trailingone + 1;
        end
    end

    assign ow_binary[WIDTH-1]   = i_gray[JCW-1];  // Wrap bit
    assign ow_binary[WIDTH-2:0] = w_binary[WIDTH-2:0];

endmodule : grayj2bin
