`timescale 1ns / 1ps

// Hamming Decode SECDEC module
module dataint_ecc_hamming_decode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic                      i_clk,
    i_rst_n,
    input  logic                      i_enable,
    input  logic [WIDTH+ParityBits:0] i_hamming_data,
    output logic [         WIDTH-1:0] o_data,
    output logic                      o_error_detected,
    output logic                      o_double_error_detected
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
        if (DEBUG) begin

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
            for (j = 0; j < TotalWidth - 1; j++) begin
                // Check if the k-th bit position is covered by the parity_bit
                if (((j + 1) >> parity_bit) & 1) get_covered_bits[j] = 1'b1;
            end
        end
        if (DEBUG)
            $display("get_covered_bits for parity bit %d is %b", parity_bit, get_covered_bits);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Check parity bits
    integer i;
    integer bit_index;
    integer parity_pos;
    logic [TotalWidth-1:0] w_covered_bits;
    always_comb begin : create_syndrome_covered_bits
        if (i_enable) begin
            for (i = 0; i < ParityBits; i++) begin
                parity_pos       = (2 ** i) - 1;
                w_syndrome_in[i] = i_hamming_data[parity_pos];
                w_syndrome[i]    = 1'b0;
                w_covered_bits   = get_covered_bits(i);
                for (bit_index = 0; bit_index < TotalWidth; bit_index++)
                    if (w_covered_bits[bit_index])
                        w_syndrome[i] = w_syndrome[i] ^ i_hamming_data[bit_index];
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
        w_overall_parity_in =  i_hamming_data[TotalWidth-1];
        if (i_enable) begin
            w_overall_parity = ^i_hamming_data[TotalWidth-2:0];
        end else begin
            w_overall_parity = 'b0;
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Correct the data if there is a single-bit error
    always_ff @(posedge i_clk or negedge i_rst_n)
    begin : correct_the_data_and_flag_errors_output_data
        if (!i_rst_n) begin
            r_data_with_parity      <= 'b0;
            o_error_detected        <= 'b0;
            o_double_error_detected <= 'b0;
        end else if (i_enable) begin
            r_data_with_parity      <= i_hamming_data;
            o_error_detected        <= 'b0;
            o_double_error_detected <= 'b0;
            if (DEBUG)
                $display(
                    "w_overall_parity, w_overall_parity_in, w_syndrome %b %b %b",
                    w_overall_parity,
                    w_overall_parity_in,
                    w_syndrome
                );
            if ((w_overall_parity != w_overall_parity_in) &&
                (w_syndrome != {ParityBits{1'b1}})) begin
                // Single-bit error detected and corrected
                r_data_with_parity[w_syndrome_0_based] <= ~i_hamming_data[w_syndrome_0_based];
                o_error_detected <= 1'b1;
                if (DEBUG)
                    $display(
                        "Single-bit error detected and corrected at position: %d",
                        w_syndrome_0_based
                    );
            end else if ((w_overall_parity == w_overall_parity_in) &&
                    (w_syndrome != {ParityBits{1'b0}})) begin
                // Double-bit error detected
                o_error_detected <= 1'b1;
                o_double_error_detected <= 1'b1;
                if (DEBUG) $display("Double-bit error detected.");
            end else begin
                // No error detected
                if (DEBUG) $display("No error detected.");
            end
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Extract the corrected data
    genvar j;
    generate
        for (j = 0; j < WIDTH; j++) begin : gen_block
            assign o_data[j] = r_data_with_parity[bit_position(j)];
        end
    endgenerate

endmodule : dataint_ecc_hamming_decode_secded
