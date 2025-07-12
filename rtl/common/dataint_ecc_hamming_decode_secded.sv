`timescale 1ns / 1ps

// Hamming Decode SECDEC module
module dataint_ecc_hamming_decode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic                      clk,
    rst_n,
    input  logic                      enable,
    input  logic [WIDTH+ParityBits:0] hamming_data,
    output logic [         WIDTH-1:0] data,
    output logic                      error_detected,
    output logic                      double_error_detected
);
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;

    // local wires
    logic [ParityBits-1:0] w_syndrome;
    logic [ParityBits-1:0] w_syndrome_in;
    logic [ParityBits-1:0] w_syndrome_0_based;
    logic [TotalWidth-1:0] r_data_with_parity;
    logic                  w_overall_parity;
    logic                  w_overall_parity_in;

    initial begin
        if (DEBUG != 0) begin
            // Debug initialization if needed
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Function to calculate the bit position for data extraction
    function automatic integer bit_position(input integer k);
        integer j, pos;
        begin
            pos = k + 1;  // Start at k+1 to account for the parity bit at position 0
            for (j = 0; j < ParityBits; j++) begin
                if (pos >= (2 ** j)) pos = pos + 1;
            end
            bit_position = pos - 1;  // Convert to 0-based index
        end
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Function to get a bit mask for the bits covered by a given parity bit
    function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
        integer j;
        begin
            get_covered_bits = 0;
            // REVERTED: Back to original loop bound - SECDED bit should not be in parity calculations
            for (j = 0; j < TotalWidth - 1; j++) begin
                // Check if the k-th bit position is covered by the parity_bit
                if (|(((j + 1) >> parity_bit) & 1)) get_covered_bits[j] = 1'b1;
            end
        end
        if (DEBUG != 0)
            $display("get_covered_bits for parity bit %d is %b", parity_bit, get_covered_bits);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Check parity bits
    integer i;
    integer bit_index;
    integer parity_pos;
    logic [TotalWidth-1:0] w_covered_bits;
    always_comb begin : create_syndrome_covered_bits
        if (enable) begin
            for (i = 0; i < ParityBits; i++) begin
                parity_pos       = (2 ** i) - 1;
                w_syndrome_in[i] = hamming_data[parity_pos];
                w_syndrome[i]    = 1'b0;
                w_covered_bits   = get_covered_bits(i);
                for (bit_index = 0; bit_index < TotalWidth; bit_index++)
                    // FIXED: Exclude the parity bit itself from the syndrome calculation
                    if (w_covered_bits[bit_index] && (bit_index != parity_pos))
                        w_syndrome[i] = w_syndrome[i] ^ hamming_data[bit_index];
                // Then XOR with the stored parity bit to get the syndrome
                w_syndrome[i] = w_syndrome[i] ^ w_syndrome_in[i];
            end
        end else begin
            parity_pos = 'b0;
            w_syndrome = 'b0;
            w_syndrome_in = 'b0;
            w_covered_bits = 'b0;
            i = 0;
            bit_index = 0;
        end
    end

    // create 0 based version of the syndrome
    assign w_syndrome_0_based = (w_syndrome - 1);

    ////////////////////////////////////////////////////////////////////////////
    // Check overall parity
    always_comb begin : check_overall_parity
        w_overall_parity_in =  hamming_data[TotalWidth-1];
        if (enable) begin
            w_overall_parity = ^hamming_data[TotalWidth-2:0];
        end else begin
            w_overall_parity = 'b0;
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Correct the data if there is a single-bit error
    always_ff @(posedge clk or negedge rst_n)
    begin : correct_the_data_and_flag_errors_output_data
        if (!rst_n) begin
            r_data_with_parity      <= 'b0;
            error_detected        <= 'b0;
            double_error_detected <= 'b0;
        end else if (enable) begin
            r_data_with_parity      <= hamming_data;
            error_detected        <= 'b0;
            double_error_detected <= 'b0;
            if (DEBUG != 0)
                $display(
                    "w_overall_parity, w_overall_parity_in, w_syndrome %b %b %b",
                    w_overall_parity,
                    w_overall_parity_in,
                    w_syndrome
                );
            if ((w_overall_parity != w_overall_parity_in) &&
                (w_syndrome != {ParityBits{1'b0}})) begin
                // Single-bit error detected and corrected
                r_data_with_parity[w_syndrome_0_based] <= ~hamming_data[w_syndrome_0_based];
                error_detected <= 1'b1;
                if (DEBUG != 0)
                    $display(
                        "Single-bit error detected and corrected at position: %d",
                        w_syndrome_0_based
                    );
            end else if ((w_overall_parity == w_overall_parity_in) &&
                    (w_syndrome != {ParityBits{1'b0}})) begin
                // Double-bit error detected
                error_detected <= 1'b1;
                double_error_detected <= 1'b1;
                if (DEBUG != 0) $display("Double-bit error detected.");
            end else begin
                // No error detected
                if (DEBUG != 0) $display("No error detected.");
            end
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Extract the corrected data
    genvar j;
    generate
        for (j = 0; j < WIDTH; j++) begin : gen_block
            assign data[j] = r_data_with_parity[bit_position(j)];
        end
    endgenerate

endmodule : dataint_ecc_hamming_decode_secded
