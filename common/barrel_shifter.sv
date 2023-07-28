`timescale 1ns / 1ps

module BarrelShifter #(
    parameter int WIDTH = 8
) (
    input logic [WIDTH-1:0] data_in,                 // Input data
    input logic [2:0] ctrl,                          // Control signal (3-bit)
                                                     // 000 No shift
                                                     // 001 Logical Right Shift (no wrap)
                                                     // 010 Arithmetic Right Shift
                                                     // 011 Logical Right Shift (wrap)
                                                     // 100 Logical Left Shift (no wrap)
                                                     // 110 Logical Left Shift (wrap)
    
    input logic  [($clog2(WIDTH)-1):0] shift_amount, // Shift amount (number of positions to shift)
    output logic [WIDTH-1:0] data_out                // Output data
);

    logic signed [WIDTH-1:0] signed_data;
    logic [WIDTH-1:0] shifted_data;

    always_comb begin
        casez (ctrl)
            3'b000: shifted_data = data_in;                              // No shift
            3'b001: shifted_data = data_in >>> shift_amount;             // Logical Right Shift (no wrap)
            3'b011: shifted_data = {data_in[WIDTH-1-shift_amount:0], data_in[WIDTH-1:WIDTH-shift_amount]}; // Logical Right Shift (wrap)
            3'b100: shifted_data = data_in << shift_amount;              // Logical Left Shift (no wrap)
            3'b110: shifted_data = {data_in[shift_amount-1:0], data_in[WIDTH-1:shift_amount]}; // Logical Left Shift (wrap)
            3'b010: begin  // Arithmetic Right Shift
                signed_data = $signed(data_in);
                shifted_data = signed_data >> shift_amount;
            end
            default: shifted_data = data_in;                              // Default: No shift
        endcase
    end

    // For arithmetic right shift, convert back to unsigned after shifting
    always_comb begin
        if (ctrl == 3'b010)
            data_out = $unsigned(shifted_data);
        else
            data_out = shifted_data;
    end

endmodule