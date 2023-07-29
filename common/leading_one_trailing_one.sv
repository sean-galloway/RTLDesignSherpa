`timescale 1ns / 1ps

module leading_one_trailing_one #(parameter WIDTH=8) (
    input  logic [WIDTH-1:0]           data,
    output logic [$clog2(WIDTH):0]     leadingone,
    output logic [WIDTH-1:0]           leadingone_vector,
    output logic [$clog2(WIDTH):0]     trailingone,
    output logic [WIDTH-1:0]           trailingone_vector,
    output logic                       all_zeroes,
    output logic                       valid
);

    localparam  N = $clog2(WIDTH)+1;

    logic [N-1:0] first_set_index;
    logic [N-1:0] leading_zeros_count;

    find_first_set #(.WIDTH(WIDTH))
    u_find_first_set(
        .data   (data),
        .index  (leadingone)
    );

    find_last_set #(.WIDTH(WIDTH))
    u_find_last_set (
        .data  (data),
        .index (trailingone)
    );

    always_comb begin
        leadingone_vector = '0;
        leadingone_vector[leadingone - 1] = 1'b1;   // Subtract 1 to convert to 0-based index
        trailingone_vector = '0;
        trailingone_vector[trailingone - 1] = 1'b1; // Subtract 1 to convert to 0-based index
    end

    assign all_zeroes = !(&data);
    assign valid      = |data;

	// synopsys translate_off
	initial begin
		$dumpfile("dump.vcd");
		$dumpvars(0, leading_one_trailing_one);
	end
	// synopsys translate_on

endmodule : leading_one_trailing_one

