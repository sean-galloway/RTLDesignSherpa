`timescale 1ns / 1ps

module dataint_ecc_hamming_decode_secded #(
    parameter int WIDTH = 4
) (
    input  logic [WIDTH+ParityBits:0]  i_hamming_data,
    output logic [WIDTH-1:0]           ow_data,
    output logic                       ow_error_detected,
    output logic                       ow_double_error_detected
);
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;
    // local wires
    logic [ParityBits:0]   w_syndrome;
    logic [TotalWidth-1:0] w_data_with_parity;
    logic                  w_overall_parity;

    // Check parity bits
    genvar i;
    generate
        for (i = 0; i < ParityBits; i = i + 1) begin : gen_parity_check
            assign w_syndrome[i] = ^(i_hamming_data & get_covered_bits(i));
        end
    endgenerate

    // Check overall parity
    assign w_overall_parity = ^i_hamming_data[0:TotalWidth-2];

    // Calculate syndrome for double error detection
    assign w_syndrome[ParityBits] = w_overall_parity ^ i_hamming_data[TotalWidth-1];

    // Correct the data if there is a single-bit error
    integer j;
    always_comb begin
        w_data_with_parity = i_hamming_data;
        if (w_syndrome != 0 && w_syndrome != {ParityBits{1'b1}}) begin
            // Single-bit error detected and corrected
            w_data_with_parity[w_syndrome] = ~w_data_with_parity[w_syndrome];
            ow_error_detected = 1'b1;
            ow_double_error_detected = 1'b0;
        end else if (w_syndrome == {ParityBits{1'b1}}) begin
            // Double-bit error detected
            ow_error_detected = 1'b1;
            ow_double_error_detected = 1'b1;
        end else begin
            // No error detected
            ow_error_detected = 1'b0;
            ow_double_error_detected = 1'b0;
        end
    end

    // Extract the corrected data
    generate
        for (j = 0; j < WIDTH; j = j + 1) begin : gen_data_extract
            assign ow_data[j] = w_data_with_parity[bit_position(j)];
        end
    endgenerate

    // Function to get a bit mask for the bits covered by a given parity bit
    function automatic [TotalWidth-1:0] gen_get_covered_bits(input integer parity_bit);
        integer k;
        begin
            get_covered_bits = 0;
            for (k = 0; k < TotalWidth-1; k = k + 1) begin // Exclude the SECDED bit itself
                if (k[parity_bit] == 1'b1) get_covered_bits[k] = 1'b1;
            end
        end
    endfunction

    // Function to calculate the bit position for data extraction
    function automatic integer bit_position(input integer k);
        integer l, pos;
        begin
            pos = k + 1; // Adjust for the SECDED bit
            for (l = 0; l < ParityBits; l = l + 1) begin
                if (k >= 2**l) pos = pos + 1;
            end
            bit_position = pos;
        end
    endfunction

    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, dataint_ecc_hamming_decode_secded);
    end
    // synopsys translate_on

endmodule : dataint_ecc_hamming_decode_secded
