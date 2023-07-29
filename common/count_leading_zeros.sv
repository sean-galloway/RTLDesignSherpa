`timescale 1ns / 1ps

// Taken from StackExchange:
// https://electronics.stackexchange.com/questions/196914/verilog-synthesize-high-speed-leading-zero-count
module count_leading_zeros (data, leading_zeros_count);
    parameter  REF_VECTOR_WIDTH=32;
    localparam DOUT_WIDTH    = $clog2(REF_VECTOR_WIDTH)+1;
    localparam DOUT_LR_WIDTH = DOUT_WIDTH-1;
    input  [REF_VECTOR_WIDTH-1:0]  data;

    output [DOUT_WIDTH-1:0]  leading_zeros_count;

    wire  [DOUT_LR_WIDTH-1:0]  leading_zeros_count_r;
    wire  [DOUT_LR_WIDTH-1:0]  leading_zeros_count_l;

    wire  [REF_VECTOR_WIDTH/2-1:0]  data_r;
    wire  [REF_VECTOR_WIDTH/2-1:0]  data_l;

    generate 
        if (REF_VECTOR_WIDTH  == 2)
            assign leading_zeros_count = (data == 2'b00) ? 'd2 : 
                          (data == 2'b01) ? 'd1 : 0;
        else begin 
            assign data_l = data[REF_VECTOR_WIDTH-1:REF_VECTOR_WIDTH/2];
            assign data_r = data[REF_VECTOR_WIDTH/2-1:0];
            count_leading_zeros #(REF_VECTOR_WIDTH/2) u_nv_clz_l(data_l, leading_zeros_count_l);
            count_leading_zeros #(REF_VECTOR_WIDTH/2) u_nv_clz_r(data_r, leading_zeros_count_r);
            assign leading_zeros_count = (~leading_zeros_count_l[DOUT_LR_WIDTH-1]) ? {leading_zeros_count_l [DOUT_LR_WIDTH-1] & leading_zeros_count_r [DOUT_LR_WIDTH-1], 1'b0                    , leading_zeros_count_l[DOUT_LR_WIDTH-2:0]} :
                                                       {leading_zeros_count_l [DOUT_LR_WIDTH-1] & leading_zeros_count_r [DOUT_LR_WIDTH-1], ~leading_zeros_count_r[DOUT_LR_WIDTH-1], leading_zeros_count_r[DOUT_LR_WIDTH-2:0]};
        end
    endgenerate
endmodule
