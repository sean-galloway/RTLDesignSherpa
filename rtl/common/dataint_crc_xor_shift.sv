`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////
// performs CRC manipulations on a single bit
module dataint_crc_xor_shift #(
    parameter int CRC_WIDTH = 32
) (
    input  [CRC_WIDTH-1:0] i_stage_input,
    input  [CRC_WIDTH-1:0] i_poly,
    input                  i_new_bit,
    output [CRC_WIDTH-1:0] ow_stage_output
);

    assign ow_stage_output[0] = i_new_bit ^ i_stage_input[CRC_WIDTH-1];
    assign ow_stage_output[CRC_WIDTH-1:1] = i_stage_input[CRC_WIDTH-2:0] ^
                                        ({CRC_WIDTH-1{ow_stage_output[0]}} & i_poly[CRC_WIDTH-1:1]);

    // // synopsys translate_off
    // initial begin
    //     $dumpfile("waves.vcd");
    //     $dumpvars(0, dataint_crc_xor_shift);
    // end
    // // synopsys translate_on

endmodule : dataint_crc_xor_shift

