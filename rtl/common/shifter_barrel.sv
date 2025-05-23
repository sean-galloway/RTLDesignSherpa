`timescale 1ns / 1ps

module shifter_barrel #(
    parameter int WIDTH = 8
) (
    input  logic         [WIDTH-1:0] i_data,          // Input data
    input  logic               [2:0] i_ctrl,          // Control signal (3-bit)
                                                      // 000 No shift
                                                      // 001 Logical Right Shift (no wrap)
                                                      // 010 Arithmetic Right Shift
                                                      // 011 Logical Right Shift (wrap)
                                                      // 100 Logical Left Shift (no wrap)
                                                      // 110 Logical Left Shift (wrap)
    input  logic [($clog2(WIDTH)):0] i_shift_amount,  // Shift amount (number of positions to shift)
    output logic         [WIDTH-1:0] ow_data_out      // Output data
);

    // Internal shift unrolled lookup arrays
    logic [WIDTH-1:0] w_array_rs[WIDTH];  // Right shift (wrap)
    logic [WIDTH-1:0] w_array_ls[WIDTH];  // Left shift (wrap)

    // Concatenate input for wrapping purposes
    logic [WIDTH*2-1:0] w_data_double;
    assign w_data_double = {i_data, i_data};

    // Clamp shift amount modulo WIDTH
    logic [$clog2(WIDTH)-1:0] shift_amount_mod;
    assign shift_amount_mod = i_shift_amount[$clog2(WIDTH)-1:0];

    // Generate lookup values for rotating shifts
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_unrolled_shifts
            assign w_array_rs[i] = w_data_double[WIDTH-1+i:i];
            assign w_array_ls[i] = w_data_double[WIDTH*2-1-i:WIDTH-i];
        end
    endgenerate

    // Main shifter logic
    always_comb begin
        case (i_ctrl)
            3'b000: // No shift
                ow_data_out = i_data;

            3'b001: // Logical Right Shift (no wrap)
                ow_data_out = (shift_amount_mod == 0) ? i_data : i_data >> i_shift_amount;

            3'b010: // Arithmetic Right Shift (preserve sign)
                ow_data_out = $signed(i_data) >>> shift_amount_mod;

            3'b011: // Logical Right Shift with wrap
                ow_data_out = w_array_rs[shift_amount_mod];

            3'b100: // Logical Left Shift (no wrap)
                ow_data_out = (shift_amount_mod == 0) ? i_data : i_data << i_shift_amount;

            3'b110: // Logical Left Shift with wrap
                ow_data_out = w_array_ls[shift_amount_mod];

            default:
                ow_data_out = i_data;
        endcase
    end

endmodule : shifter_barrel
