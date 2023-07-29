`timescale 1ns / 1ps

// Taken from StackExchange:
// https://electronics.stackexchange.com/questions/196914/verilog-synthesize-high-speed-leading-zero-count
module count_leading_zeros (ref_vector, dout);
    parameter  REF_VECTOR_WIDTH=32;
    localparam DOUT_WIDTH    = $clog2(REF_VECTOR_WIDTH)+1;
    localparam DOUT_LR_WIDTH = DOUT_WIDTH-1;
    input  [REF_VECTOR_WIDTH-1:0]  ref_vector;

    output [DOUT_WIDTH-1:0]  dout;

    wire  [DOUT_LR_WIDTH-1:0]  dout_r;
    wire  [DOUT_LR_WIDTH-1:0]  dout_l;

    wire  [REF_VECTOR_WIDTH/2-1:0]  ref_vector_r;
    wire  [REF_VECTOR_WIDTH/2-1:0]  ref_vector_l;

    generate 
        if (REF_VECTOR_WIDTH  == 2)
            assign dout = (ref_vector == 2'b00) ? 'd2 : 
                          (ref_vector == 2'b01) ? 'd1 : 0;
        else begin 
            assign ref_vector_l = ref_vector[REF_VECTOR_WIDTH-1:REF_VECTOR_WIDTH/2];
            assign ref_vector_r = ref_vector[REF_VECTOR_WIDTH/2-1:0];
            count_leading_zeros #(REF_VECTOR_WIDTH/2) u_nv_clz_l(ref_vector_l, dout_l);
            count_leading_zeros #(REF_VECTOR_WIDTH/2) u_nv_clz_r(ref_vector_r, dout_r);
            assign dout = (~dout_l[DOUT_LR_WIDTH-1]) ? {dout_l [DOUT_LR_WIDTH-1] & dout_r [DOUT_LR_WIDTH-1], 1'b0                    , dout_l[DOUT_LR_WIDTH-2:0]} :
                                                       {dout_l [DOUT_LR_WIDTH-1] & dout_r [DOUT_LR_WIDTH-1], ~dout_r[DOUT_LR_WIDTH-1], dout_r[DOUT_LR_WIDTH-2:0]};
        end
    endgenerate
endmodule
