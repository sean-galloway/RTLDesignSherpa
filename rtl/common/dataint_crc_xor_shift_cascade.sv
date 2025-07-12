`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////
// Perform cascaded manipulations across 8 bits of data
module dataint_crc_xor_shift_cascade #(
    parameter int CRC_WIDTH = 32
) (
    input  [CRC_WIDTH-1:0] block_input,
    input  [CRC_WIDTH-1:0] poly,
    input  [          7:0] data_input,
    output [CRC_WIDTH-1:0] block_output
);

    wire [(CRC_WIDTH-1):0] w_cascade [0:7]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Generate loop for XOR_Shift blocks
    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_xor_shift_cascade
            if (i == 0) begin : gen_xor_shift_0
                // For the first block, use block_input as the stage_input
                dataint_crc_xor_shift #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift (
                    .stage_input(block_input),
                    .poly(poly),
                    .new_bit(data_input[7-i]),
                    .stage_output(w_cascade[i])
                );
            end else begin : gen_xor_shift_N
                // For subsequent blocks, chain the output of the previous block
                dataint_crc_xor_shift #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift (
                    .stage_input(w_cascade[i-1]),
                    .poly(poly),
                    .new_bit(data_input[7-i]),
                    .stage_output(w_cascade[i])
                );
            end
        end
    endgenerate

    assign block_output = w_cascade[7];

endmodule : dataint_crc_xor_shift_cascade
