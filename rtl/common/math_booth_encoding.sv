module math_booth_encoding #(
    parameter int N = 4
) (
    input  logic [  2:0] i_sel,           // 3 bits from the multiplier
    input  logic [N-1:0] i_multiplicand,  // N-bit multiplicand
    output logic [N-1:0] ow_result        // N-bit output
);

    // Local variable to hold the result
    wire [N-1:0] result;

    // Control logic for determining the multiple of the multiplicand
    always_comb begin
        case (i_sel)
            3'b000:  result = {N{1'b0}};  // 0
            3'b001:  result = i_multiplicand;  // 1
            3'b010:  result = i_multiplicand << 1;  // 2
            3'b011:  result = i_multiplicand + (i_multiplicand << 1);  // 3
            3'b100:  result = -i_multiplicand << 1;  // -4
            3'b101:  result = -i_multiplicand;  // -3
            3'b110:  result = -(i_multiplicand << 1);  // -2
            3'b111:  result = {N{1'b0}};  // -1 (or effectively 0 in this context)
            default: result = {N{1'b0}};  // Should not occur
        endcase
    end

    // Output the result
    assign ow_result = result;

endmodule : math_booth_encoding
