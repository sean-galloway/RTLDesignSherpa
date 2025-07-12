`timescale 1ns / 1ps
////////////////////////////////////////////////////////////////////////////
// performs CRC manipulations on a single bit
module dataint_crc_xor_shift #(
 parameter int CRC_WIDTH = 32
) (
input [CRC_WIDTH-1:0] stage_input,
input [CRC_WIDTH-1:0] poly,
input new_bit,
output [CRC_WIDTH-1:0] stage_output
);
    // Break the circular dependency by using an intermediate signal
    logic feedback_bit;

    // Calculate the feedback bit first
    assign feedback_bit = new_bit ^ stage_input[CRC_WIDTH-1];

    // Then use it to calculate the output
    assign stage_output[0] = feedback_bit;
    assign stage_output[CRC_WIDTH-1:1] = stage_input[CRC_WIDTH-2:0] ^
        ({CRC_WIDTH-1{feedback_bit}} & poly[CRC_WIDTH-1:1]);

endmodule : dataint_crc_xor_shift
