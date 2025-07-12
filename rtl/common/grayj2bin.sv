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
    localparam int PAD_WIDTH = (WIDTH > N+1) ? WIDTH-N-1 : 0;

    logic [N-1:0]     w_leading_one;
    logic [N-1:0]     w_trailing_one;
    logic [WIDTH-1:0] w_binary;
    logic             w_all_zeroes;
    logic             w_all_ones;
    logic             w_valid;

    // Leading/trailing detection
    leading_one_trailing_one #(
        .WIDTH(JCW),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_leading_one_trailing_one (
        .data              (gray),
        .leadingone        (w_leading_one),
        .leadingone_vector (),
        .trailingone       (w_trailing_one),
        .trailingone_vector(),
        .all_zeroes        (w_all_zeroes),
        .all_ones          (w_all_ones),
        .valid             (w_valid)
    );

    // Restore original working logic
    always_comb begin
        if (w_all_zeroes || w_all_ones) begin
            w_binary = {WIDTH{1'b0}};
        end else if (gray[JCW-1]) begin
            // Second half: use leading one position directly
            w_binary = {{(WIDTH-N){1'b0}}, w_trailing_one};
        end else begin
            // First half: use trailing one + 1
            w_binary = {{(WIDTH-N){1'b0}}, (w_leading_one + 1'b1)};
        end
    end

    assign binary[WIDTH-1]   = gray[JCW-1];                 // MSB = wrap
    assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower binary

endmodule : grayj2bin
