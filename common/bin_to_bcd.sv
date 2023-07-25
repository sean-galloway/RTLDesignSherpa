`timescale 1ns / 1ps

module binary_to_bcd #(
    parameter N = 8  // Width of the input binary number (number of input bits)
) (
    input  logic [N-1:0]       binary_in,  // Input binary number
    output logic [(N/4)*4-1:0] bcd_out     // Output BCD representation
);

    assign bcd_out = 0; // Initialize the output to all zeros

    always_comb begin
        for (int i = 0; i < N; i++) begin
            // Shift and add 3 algorithm for BCD conversion
            for (int j = (N/4)*4-1; j >= 0; j--) begin
                if (bcd_out[j] >= 5) bcd_out[j] = bcd_out[j] + 3;
                    bcd_out = {1'b0, bcd_out} + (binary_in[i] << (N/4)*4-1);
                end
        end
    end

endmodule : binary_to_bcd
