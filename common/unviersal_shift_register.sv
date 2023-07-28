`timescale 1ns / 1ps

module universal_shift_reg #(parameter WIDTH=4)
(
    input                    clk, rst_n,
    input [1:0]              select,       // select operation
                                           // 00 = p_dout = p_dout
                                           // 01 = right shift
                                           // 10 = left shift
                                           // 11 = p_dout = p_din
    input [WIDTH-1:0]        p_din,        // parallel data in
    input                    s_left_din,   // serial left data in
    input                    s_right_din,  // serial right data in
    output logic [WIDTH-1:0] p_dout,       // parallel data out
    output                   s_left_dout,  // serial left data out
    output                   s_right_dout  // serial right data out
);

    logic [WIDTH-1:0] p_dout_d;

    always_comb begin
        case(select)
            2'h1: p_dout_d <= {s_right_din,p_dout[WIDTH-1:1]}; // Right Shift
            2'h2: p_dout_d <= {p_dout[2:0],s_left_din};        // Left Shift
            2'h3: p_dout_d <= p_din;                           // Parallel in - Parallel out
            default: p_dout_d <= p_dout;                       // Do nothing
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if(!rst_n)
            p_dout <= 0;
        else
            p_dout <= p_dout_d;
    end

    assign s_left_dout = p_dout[0];
    assign s_right_dout = p_dout[WIDTH-1];

endmodule : universal_shift_reg