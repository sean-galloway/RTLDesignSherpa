// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for dataint_crc_xor_shift (yosys-compatible)

module formal_crc_xor_shift #(
    parameter int CRC_WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [CRC_WIDTH-1:0] stage_input;
    (* anyconst *) logic [CRC_WIDTH-1:0] poly;
    (* anyconst *) logic                  new_bit;

    logic [CRC_WIDTH-1:0] stage_output;

    dataint_crc_xor_shift #(.CRC_WIDTH(CRC_WIDTH)) dut (
        .stage_input  (stage_input),
        .poly         (poly),
        .new_bit      (new_bit),
        .stage_output (stage_output)
    );

    // Helper: matches actual RTL implementation exactly
    wire feedback_bit = new_bit ^ stage_input[CRC_WIDTH-1];
    wire [CRC_WIDTH-2:0] upper_expected = stage_input[CRC_WIDTH-2:0] ^
        ({(CRC_WIDTH-1){feedback_bit}} & poly[CRC_WIDTH-1:1]);

    // Structural: LSB is feedback_bit, upper bits are shift+conditional XOR of poly[MSB:1]
    always @(posedge clk)
        ap_lsb: assert (stage_output[0] == feedback_bit);

    always @(posedge clk)
        ap_upper: assert (stage_output[CRC_WIDTH-1:1] == upper_expected);

    // Case 1: feedback=0 (new_bit=MSB) → LSB=0, upper = shift only
    always @(posedge clk)
        if (!feedback_bit)
            ap_fb0: assert (stage_output == {stage_input[CRC_WIDTH-2:0], 1'b0});

    // Case 2: feedback=1 (new_bit!=MSB) → LSB=1, upper = shift XOR poly[MSB:1]
    always @(posedge clk)
        if (feedback_bit)
            ap_fb1: assert (stage_output[CRC_WIDTH-1:1] ==
                (stage_input[CRC_WIDTH-2:0] ^ poly[CRC_WIDTH-1:1]));

    // Cover
    always @(posedge clk) begin
        cover (!new_bit && !stage_input[CRC_WIDTH-1]);
        cover (!new_bit &&  stage_input[CRC_WIDTH-1]);
        cover ( new_bit && !stage_input[CRC_WIDTH-1]);
        cover ( new_bit &&  stage_input[CRC_WIDTH-1]);
        cover (poly == {CRC_WIDTH{1'b1}});
        cover (poly == '0);
        cover (stage_output == stage_input);
    end

endmodule
