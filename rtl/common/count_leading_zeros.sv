`timescale 1ns / 1ps

// Taken from StackExchange:
// https://electronics.stackexchange.com/questions/196914/verilog-synthesize-high-speed-leading-zero-count
module count_leading_zeros (i_data, ow_leading_zeros_count);
    parameter  WIDTH         = 32;
    localparam DOUT_WIDTH    = $clog2(WIDTH)+1;
    localparam DOUT_LR_WIDTH = DOUT_WIDTH-1;
    input  [WIDTH-1:0]       i_data;

    output [DOUT_WIDTH-1:0]  ow_leading_zeros_count;

    wire  [DOUT_LR_WIDTH-1:0]  w_leading_zeros_count_r;
    wire  [DOUT_LR_WIDTH-1:0]  w_leading_zeros_count_l;

    wire  [WIDTH/2-1:0]  w_data_r;
    wire  [WIDTH/2-1:0]  w_data_l;

    generate 
        if (WIDTH == 2)
            assign ow_leading_zeros_count = (data == 2'b00) ? 'd2 : 
                                            (data == 2'b01) ? 'd1 : 0;
        else begin 
            assign w_data_l = data[WIDTH-1:WIDTH/2];
            assign w_data_r = data[WIDTH/2-1:0];
            count_leading_zeros #(WIDTH/2) u_nv_clz_l(w_data_l, w_leading_zeros_count_l);
            count_leading_zeros #(WIDTH/2) u_nv_clz_r(w_data_r, w_leading_zeros_count_r);
            assign ow_leading_zeros_count = (~w_leading_zeros_count_l[DOUT_LR_WIDTH-1]) ? 
                                            {w_leading_zeros_count_l [DOUT_LR_WIDTH-1] & w_leading_zeros_count_r [DOUT_LR_WIDTH-1], 1'b0                    , w_leading_zeros_count_l[DOUT_LR_WIDTH-2:0]} :
                                            {w_leading_zeros_count_l [DOUT_LR_WIDTH-1] & w_leading_zeros_count_r [DOUT_LR_WIDTH-1], ~w_leading_zeros_count_r[DOUT_LR_WIDTH-1], w_leading_zeros_count_r[DOUT_LR_WIDTH-2:0]};
        end
    endgenerate
endmodule
