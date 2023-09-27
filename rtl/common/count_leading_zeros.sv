`timescale 1ns / 1ps

// Taken from StackExchange:
// https://electronics.stackexchange.com/questions/196914/verilog-synthesize-high-speed-leading-zero-count
module count_leading_zeros (
    i_data,
    ow_leading_zeros_count
);
    parameter int WIDTH = 32;
    localparam int DoutWidth = $clog2(WIDTH) + 1;
    localparam int DoutLRWidth = DoutWidth - 1;
    input [WIDTH-1:0] i_data;

    output [DoutWidth-1:0] ow_leading_zeros_count;

    wire [DoutLRWidth-1:0] w_leading_zeros_count_r;
    wire [DoutLRWidth-1:0] w_leading_zeros_count_l;

    wire [WIDTH/2-1:0] w_data_r;
    wire [WIDTH/2-1:0] w_data_l;

    generate
        if (WIDTH == 2)
            assign ow_leading_zeros_count = (data == 2'b00) ? 'd2 : (data == 2'b01) ? 'd1 : 0;
        else begin : gen_find_leading_zeroes
            assign w_data_l = data[WIDTH-1:WIDTH/2];
            assign w_data_r = data[WIDTH/2-1:0];
            count_leading_zeros #(WIDTH / 2) u_nv_clz_l (
                .i_data(w_data_l),
                .ow_leading_zeros_count(w_leading_zeros_count_l)
            );
            count_leading_zeros #(WIDTH / 2) u_nv_clz_r (
                .i_data(w_data_r),
                .ow_leading_zeros_count(w_leading_zeros_count_r)
            );
            assign ow_leading_zeros_count = (~w_leading_zeros_count_l[DoutLRWidth-1]) ?
                                                {w_leading_zeros_count_l [DoutLRWidth-1] &
                                                    w_leading_zeros_count_r [DoutLRWidth-1],
                                                    1'b0, w_leading_zeros_count_l[DoutLRWidth-2:0]}:
                                                {w_leading_zeros_count_l [DoutLRWidth-1] &
                                                    w_leading_zeros_count_r [DoutLRWidth-1],
                                                    ~w_leading_zeros_count_r[DoutLRWidth-1],
                                                    w_leading_zeros_count_r[DoutLRWidth-2:0]};
        end
    endgenerate
endmodule
