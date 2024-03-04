`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////
// Perform cascaded manipulations across 8 bits of data
module dataint_crc_xor_shift_cascade #(
    parameter int CRC_WIDTH = 32
) (
    input  [CRC_WIDTH-1:0] i_block_input,
    input  [CRC_WIDTH-1:0] i_poly,
    input  [          7:0] i_data_input,
    output [CRC_WIDTH-1:0] ow_block_output
);

    wire [(CRC_WIDTH-1):0] w_cascade [0:7]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Generate loop for XOR_Shift blocks
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_xor_shift_cascade
            if (i == 0) begin : gen_xor_shift_0
                // For the first block, use i_block_input as the stage_input
                dataint_crc_xor_shift #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift (
                    .i_stage_input(i_block_input),
                    .i_poly(i_poly),
                    .i_new_bit(i_data_input[7-i]),
                    .ow_stage_output(w_cascade[i])
                );
            end else begin : gen_xor_shift_N
                // For subsequent blocks, chain the output of the previous block
                dataint_crc_xor_shift #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift (
                    .i_stage_input(w_cascade[i-1]),
                    .i_poly(i_poly),
                    .i_new_bit(i_data_input[7-i]),
                    .ow_stage_output(w_cascade[i])
                );
            end
        end
    endgenerate

    assign ow_block_output = w_cascade[7];

    // // synopsys translate_off
    // initial begin
    //     $dumpfile("waves.vcd");
    //     $dumpvars(0, dataint_crc_xor_shift_cascade);
    // end
    // // synopsys translate_on

endmodule : dataint_crc_xor_shift_cascade
