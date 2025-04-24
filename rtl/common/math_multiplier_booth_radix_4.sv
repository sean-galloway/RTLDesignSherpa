`timescale 1ns / 1ps
module math_multiplier_booth_radix_4 #(
    parameter int N = 8  // Width of the multiplier and multiplicand
) (
    input  logic [N-1:0]   i_multiplier,
    input  logic [N-1:0]   i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    // For Booth encoding, we need to examine triplets of bits
    // Add an extra bit (0) at the LSB of the multiplier
    logic [N:0] ext_multiplier;
    assign ext_multiplier = {i_multiplier, 1'b0};

    // Special case for most negative * most negative
    logic is_special_case;
    assign is_special_case = (i_multiplier == {1'b1, {(N-1){1'b0}}}) &&
                                (i_multiplicand == {1'b1, {(N-1){1'b0}}});

    // Calculate number of Booth groups
    localparam int M = (N + 1) / 2;  // Number of Booth-encoded groups

    // Arrays for intermediate values
    logic [2:0]     booth_groups    [M];
    logic [N+1:0]   encoded_values  [M];  // Increased width
    logic [2*N-1:0] partial_products[M];
    logic [2*N-1:0] final_sum;

    // Generate booth groups and encoded values
    genvar i;
    generate
        for (i = 0; i < M; i++) begin : gen_booth_groups
            // For Group 0, use bits [1:0] and an implied 0
            if (i == 0) begin : gen_booth_groups
                assign booth_groups[i] = {ext_multiplier[1], ext_multiplier[0], 1'b0};
            end
            // For other groups, use bits [2i+1:2i-1]
            else begin : gen_booth_groups_next0
                // Handle case where we might go beyond the multiplier width
                if (2*i+1 > N) begin : gen_booth_groups_next1
                    // Sign extend as needed
                    logic top_bit, mid_bit, low_bit;
                    assign top_bit = (2*i+1 <= N) ? ext_multiplier[2*i+1] : ext_multiplier[N];
                    assign mid_bit = (2*i <= N) ? ext_multiplier[2*i] : ext_multiplier[N];
                    assign low_bit = ext_multiplier[2*i-1];
                    assign booth_groups[i] = {top_bit, mid_bit, low_bit};
                end
                else begin : gen_booth_groups_next2
                    assign booth_groups[i] =
                        {ext_multiplier[2*i+1], ext_multiplier[2*i], ext_multiplier[2*i-1]};
                end
            end

            // Instantiate encoder for each group
            math_multiplier_booth_radix_4_encoder #(.N(N)) encoder (
                .i_booth_group(booth_groups[i]),
                .i_multiplicand(i_multiplicand),
                .ow_booth_out(encoded_values[i])
            );

            // Create partial product with proper shift and sign extension
            always_comb begin
                // Sign extend to 2*N bits using the sign bit from encoded_values
                logic [2*N-1:0] extended;
                extended = {{(2*N-N-2){encoded_values[i][N+1]}}, encoded_values[i]};

                // Apply appropriate shift by 2*i positions for the Booth radix-4 algorithm
                partial_products[i] = extended << (2*i);
            end
        end
    endgenerate

    // Sum all partial products with special case handling
    always_comb begin
        final_sum = '0;

        if (is_special_case) begin
            // Most negative * most negative = 2^(2N-2)
            ow_product = 1'b1 << (2*N-2);
        end
        else begin
            for (int j = 0; j < M; j++) begin
                final_sum = final_sum + partial_products[j];
            end

            // Right shift by 2 to correct for the radix-4 algorithm
            // The encoder already left-shifts values by 1 or 2 bits
            ow_product = final_sum >> 2;
        end
    end

endmodule : math_multiplier_booth_radix_4
