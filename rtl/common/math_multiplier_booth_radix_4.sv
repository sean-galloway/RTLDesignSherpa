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
    logic [2:0]     booth_groups    [0:M-1];
    logic [N+1:0]   encoded_values  [0:M-1];  // Increased width
    logic [2*N-1:0] partial_products[0:M-1];
    
    // Generate booth groups and encoded values
    genvar i;
    generate
        for (i = 0; i < M; i++) begin : gen_booth_groups
            // For Group 0, use bits [1:0] and an implied 0
            if (i == 0) begin
                assign booth_groups[i] = {ext_multiplier[1], ext_multiplier[0], 1'b0};
            end
            // For other groups, use bits [2i+1:2i-1]
            else begin
                // Handle case where we might go beyond the multiplier width
                if (2*i+1 > N) begin
                    // Sign extend as needed
                    logic top_bit, mid_bit, low_bit;
                    assign top_bit = (2*i+1 <= N) ? ext_multiplier[2*i+1] : ext_multiplier[N];
                    assign mid_bit = (2*i <= N) ? ext_multiplier[2*i] : ext_multiplier[N];
                    assign low_bit = ext_multiplier[2*i-1];
                    assign booth_groups[i] = {top_bit, mid_bit, low_bit};
                end
                else begin
                    assign booth_groups[i] = {ext_multiplier[2*i+1], ext_multiplier[2*i], ext_multiplier[2*i-1]};
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
                // Sign extend the encoded value and shift by 2*i positions
                // The shift by 1 has already been applied in the encoder
                logic [2*N-1:0] extended;
                extended = {{(2*N-N-2){encoded_values[i][N+1]}}, encoded_values[i]};
                
                // Shift by 2*i positions (but account for pre-shift from encoder)
                partial_products[i] = extended << (2*i);
            end
        end
    endgenerate
    
    // Sum all partial products with special case handling
    always_comb begin
        if (is_special_case) begin
            // Most negative * most negative = 2^(2N-2)
            ow_product = 1'b1 << (2*N-2);
        end
        else begin
            // Sum all partial products and apply final right shift
            logic [2*N-1:0] sum;
            sum = '0;
            for (int j = 0; j < M; j++) begin
                sum = sum + partial_products[j];
            end
            
            // Final right shift by 1 to counteract the pre-shifting in the encoder
            ow_product = sum >> 1;
        end
    end

endmodule : math_multiplier_booth_radix_4
