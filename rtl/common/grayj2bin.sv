`timescale 1ns / 1ps

module grayj2bin #(parameter JCW=10, parameter WIDTH=4, parameter INSTANCE_NAME="") (
    input wire i_clk,
    input wire i_rst_n,
    input  logic [JCW-1:0] i_gray,    // Width is DEPTH
    output logic [WIDTH-1:0] ow_binary  // Including the wrap bit
);

    localparam  N = $clog2(JCW)+1;

    logic [N-1:0]      leadingone, trailingone;
    logic [WIDTH-1:0]  binary;

    leading_one_trailing_one 
    #(
        .WIDTH (JCW),
        .INSTANCE_NAME(INSTANCE_NAME)
    )
    u_leading_one_trailing_one(
        .data               (i_gray             ),
        .leadingone         (leadingone         ),
        .leadingone_vector  (  ),
        .trailingone        (trailingone        ),
        .trailingone_vector ( ),
        .all_zeroes         (all_zeroes         ),
        .all_ones           (all_ones           ),
        .valid              (valid              )
    );

    always_comb begin
        if (all_zeroes || all_ones) 
            binary = {WIDTH-1{1'b0}};
        else if (i_gray[JCW-1] == 1'b1)
            binary = leadingone;
        else begin
            binary = trailingone + 1;
        end
    end

    assign ow_binary[WIDTH-1]   = i_gray[JCW-1];  // Wrap bit
    assign ow_binary[WIDTH-2:0] = binary[WIDTH-2:0];

    // always_ff @(posedge i_clk or negedge i_rst_n) begin
    //     if (!i_rst_n)
    //         ow_binary <= 'b0;
    //     else begin
    //         ow_binary[WIDTH-1]   <= i_gray[JCW-1];  // Wrap bit
    //         ow_binary[WIDTH-2:0] <= binary[WIDTH-2:0];
    //     end
    // end

endmodule : grayj2bin
