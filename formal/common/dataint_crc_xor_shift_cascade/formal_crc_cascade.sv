// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for dataint_crc_xor_shift_cascade (yosys-compatible)
// Proves zero-in/zero-out property and structural cascade correctness.

module formal_crc_cascade #(
    parameter int CRC_WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [CRC_WIDTH-1:0] block_input;
    (* anyconst *) logic [CRC_WIDTH-1:0] poly;
    (* anyconst *) logic [7:0]           data_input;

    logic [CRC_WIDTH-1:0] block_output;

    // Instantiate DUT
    dataint_crc_xor_shift_cascade #(
        .CRC_WIDTH(CRC_WIDTH)
    ) dut (
        .block_input  (block_input),
        .poly         (poly),
        .data_input   (data_input),
        .block_output (block_output)
    );

    // =========================================================================
    // Reference model: 8 chained single-bit CRC stages
    // =========================================================================
    logic [CRC_WIDTH-1:0] ref_stage [0:8];

    assign ref_stage[0] = block_input;

    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : gen_ref
            logic feedback;
            assign feedback = data_input[7-i] ^ ref_stage[i][CRC_WIDTH-1];
            assign ref_stage[i+1][0] = feedback;
            assign ref_stage[i+1][CRC_WIDTH-1:1] = ref_stage[i][CRC_WIDTH-2:0] ^
                ({(CRC_WIDTH-1){feedback}} & poly[CRC_WIDTH-1:1]);
        end
    endgenerate

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Zero in, zero out: when block_input == 0 and data_input == 0, output == 0
    always @(posedge clk)
        ap_zero_in_zero_out: assert (
            !(block_input == '0 && data_input == 8'b0) || (block_output == '0)
        );

    // Structural: cascade output matches reference model
    always @(posedge clk)
        ap_matches_ref: assert (block_output == ref_stage[8]);

    // Output is purely combinational (depends only on inputs)
    // Verified implicitly: anyconst inputs + combinational DUT = no state

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover non-zero output
    always @(posedge clk)
        cp_nonzero_out: cover (block_output != '0);

    // Cover all-ones input producing some output
    always @(posedge clk)
        cp_all_ones_in: cover (
            block_input == {CRC_WIDTH{1'b1}} &&
            data_input == 8'hFF &&
            poly != '0
        );

    // Cover zero block_input with non-zero data
    always @(posedge clk)
        cp_zero_block_nonzero_data: cover (
            block_input == '0 && data_input != 8'b0
        );

    // Cover non-zero block_input with zero data
    always @(posedge clk)
        cp_nonzero_block_zero_data: cover (
            block_input != '0 && data_input == 8'b0
        );

endmodule
