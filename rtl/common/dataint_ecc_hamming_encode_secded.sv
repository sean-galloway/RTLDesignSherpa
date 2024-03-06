`timescale 1ns / 1ps

// Hamming Encode SECDEC module
module dataint_ecc_hamming_encode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic [     WIDTH-1:0] i_data,
    output logic [TotalWidth-1:0] ow_encoded_data
);
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;  // Including the SECDED bit

    // local wires
    logic [TotalWidth-1:0] w_data_with_parity;

    ////////////////////////////////////////////////////////////////////////////
    // Function to calculate the bit position for data insertion
    function automatic integer bit_position(input integer k);
        integer j, pos;
        begin
            pos = k + 1;  // Start at k+1 to account for the parity bit at position 0
            for (j = 0; j < ParityBits; j++) begin
                if (pos >= (2 ** j)) pos = pos + 1;
            end
            bit_position = pos - 1;  // Convert back to 0-based index
        end
        if (DEBUG) $display("bit_position for data bit %d is %d", k, bit_position);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Function to get a bit mask for the bits covered by a given parity bit
    function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
        integer j;
        begin
            get_covered_bits = 'b0;
            for (j = 0; j < TotalWidth; j++) begin
                if (((j + 1) >> parity_bit) & 1) get_covered_bits[j] = 1'b1;
            end
        end
        if (DEBUG)
            $display("get_covered_bits for parity bit %d is %b", parity_bit, get_covered_bits);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Insert data bits and calculate parity bits
    integer i;
    integer parity_pos;
    integer bit_index;
    logic [TotalWidth-1:0] w_covered_bits;
    always_comb begin
        // Initialize with zeros
        w_data_with_parity = {TotalWidth{1'b0}};

        // Insert data bits into the correct positions
        for (i = 0; i < WIDTH; i++) begin
            w_data_with_parity[bit_position(i)] = i_data[i];
        end

        // Calculate parity bits
        for (i = 0; i < ParityBits; i++) begin
            parity_pos = (2 ** i) - 1;
            if (DEBUG) $display("Calculate Parity Bits, parity bit position: %d", parity_pos);
            w_data_with_parity[parity_pos] = 1'b0;  // Initialize to 0
            w_covered_bits = get_covered_bits(i);
            for (bit_index = 0; bit_index < TotalWidth; bit_index = bit_index + 1) begin
                if (w_covered_bits[bit_index]) begin
                    w_data_with_parity[parity_pos] =
                        w_data_with_parity[parity_pos] ^ w_data_with_parity[bit_index];
                end
            end
        end

        // Calculate the extra SECDED bit
        w_data_with_parity[TotalWidth-1] = ^w_data_with_parity[TotalWidth-2:0];

        // Assign to output
        ow_encoded_data = w_data_with_parity;
    end

endmodule : dataint_ecc_hamming_encode_secded
