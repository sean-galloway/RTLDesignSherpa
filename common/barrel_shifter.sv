`timescale 1ns / 1ps

module barrel_shifter #(
    parameter int WIDTH = 8
) (
    input logic [WIDTH-1:0] data_in,                 // Input data
    input logic [2:0]       ctrl,                    // Control signal (3-bit)
                                                     // 000 No shift
                                                     // 001 Logical Right Shift (no wrap)
                                                     // 010 Arithmetic Right Shift
                                                     // 011 Logical Right Shift (wrap)
                                                     // 100 Logical Left Shift (no wrap)
                                                     // 110 Logical Left Shift (wrap)
    input  logic [($clog2(WIDTH)):0] shift_amount,   // Shift amount (number of positions to shift)
    output logic [WIDTH-1:0]         data_out        // Output data
);

    logic [WIDTH-1:0] array_rs[WIDTH*2]; // array to store the unrolled shifted values
    logic [WIDTH-1:0] array_ls[WIDTH*2]; // array to store the unrolled shifted values

    // Concatenate the input signal for wrapping purposes
    logic [WIDTH*2-1:0] data_in_double;
    assign data_in_double = {data_in, data_in};

    logic [($clog2(WIDTH)):0] shift_amount_mod;
    assign shift_amount_mod = shift_amount % WIDTH;

    // Unroll the shift operation using a loop
    genvar i;
    for (i = 0; i < WIDTH; i++) begin : generate_loop
        assign array_rs[i] = data_in_double[WIDTH-1+i:i];
        assign array_ls[i] = data_in_double[WIDTH*2-1-i:WIDTH-1-i];
    end

    // Select the shifted value
    always_comb begin
        case (ctrl)
            3'b000:  data_out = data_in; // No shift
            3'b001:  data_out = (shift_amount_mod) ? data_in >>> shift_amount : data_in; // Logical Right Shift (no wrap)
            3'b100:  data_out = (shift_amount_mod) ? data_in << shift_amount : data_in; // Logical Left Shift (no wrap)
            3'b010:  data_out = $signed(data_in) >>> shift_amount_mod; // Arithmetic Right Shift
            3'b011:  data_out = array_rs[shift_amount_mod]; // riight shift wrap
            3'b110:  data_out = array_ls[shift_amount_mod]; // left shift wrap
            default: data_out = data_in; // Default: No shift
        endcase
    end

	// synopsys translate_off
	initial begin
		$dumpfile("dump.vcd");
		$dumpvars(0, barrel_shifter);
	end
	// synopsys translate_on

endmodule : barrel_shifter

