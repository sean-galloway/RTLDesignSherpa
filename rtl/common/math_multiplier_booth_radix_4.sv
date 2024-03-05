`timescale 1ns / 1ps
module math_multiplier_booth_radix_4 #(
    parameter int N = 8  // Width of the multiplier and multiplicand
) (
    input  logic [N-1:0]   i_multiplier,
    input  logic [N-1:0]   i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    function automatic [2:0] get_booth_group(input logic [N-1:0] multiplier, input integer group);
        begin
            // Calculate the indices for the Booth group
            int low_idx = 2 * group - 1;
            int mid_idx = 2 * group;
            int high_idx = 2 * group + 1;

            // Special case for the least significant group (group 0)
            if (group == 0) begin
                get_booth_group = {multiplier[1], multiplier[0], 1'b0};
            end else begin
                // No boundary condition; normal operation for groups other than the least significant
                get_booth_group = {multiplier[high_idx], multiplier[mid_idx], multiplier[low_idx]};
            end
        end
    endfunction

    localparam int M = (N + 1) / 2;  // Number of Booth-encoded groups for radix-4
    logic [N:0]     w_encoded_values   [0:M-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [N-1:0]   w_neg_multiplicand;
    logic [2*N-1:0] w_partial_products [0:M-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [2*N-1:0] w_product;

    // Booth encoding and partial product generation
    genvar i;
    generate
        for (i = 0; i < M; i++) begin : gen_booth_encoding
            logic [2:0] w_booth_group;

            assign w_booth_group = get_booth_group(i_multiplier, i);

            // Instantiate the Booth encoder for each group
            math_multiplier_booth_radix_4_encoder #(.N(N)) booth_encoder (
                .i_booth_group(w_booth_group),
                .i_multiplicand(i_multiplicand),
                .ow_booth_out(w_encoded_values[i])
            );

            // Determine the sign extension and perform left shift operation
            // This is done in a procedural block where dynamic evaluation is permitted
            always_comb begin
                if (w_encoded_values[i][N]) begin  // Check if the sign bit is set
                    w_partial_products[i] = {{(2*N-N-1){1'b1}}, w_encoded_values[i]} << (2*i);
                end else begin
                    w_partial_products[i] = {{(2*N-N-1){1'b0}}, w_encoded_values[i]} << (2*i);
                end
            end
        end
    endgenerate

    integer j;
    always_comb begin
        ow_product = 'b0;
        for (j=0; j<M; j++) begin
            ow_product = ow_product + w_partial_products[j];
        end
    end

endmodule : math_multiplier_booth_radix_4

