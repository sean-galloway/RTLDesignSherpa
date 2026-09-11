module axi_split_combi (
	aclk,
	aresetn,
	current_addr,
	current_len,
	ax_size,
	alignment_mask,
	is_idle_state,
	transaction_valid,
	split_required,
	split_len,
	next_boundary_addr,
	remaining_len_after_split,
	new_split_needed
);
	parameter signed [31:0] AW = 32;
	parameter signed [31:0] DW = 32;
	input wire aclk;
	input wire aresetn;
	input wire [AW - 1:0] current_addr;
	input wire [7:0] current_len;
	input wire [2:0] ax_size;
	input wire [11:0] alignment_mask;
	input wire is_idle_state;
	input wire transaction_valid;
	output wire split_required;
	output wire [7:0] split_len;
	output wire [AW - 1:0] next_boundary_addr;
	output wire [7:0] remaining_len_after_split;
	output wire new_split_needed;
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] LOG2_BYTES_PER_BEAT = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] EXPECTED_AX_SIZE = LOG2_BYTES_PER_BEAT;
	function automatic signed [AW - 1:0] sv2v_cast_DE851_signed;
		input reg signed [AW - 1:0] inp;
		sv2v_cast_DE851_signed = inp;
	endfunction
	localparam [AW - 1:0] ADDR_ALIGN_MASK = sv2v_cast_DE851_signed(BYTES_PER_BEAT - 1);
	wire [AW - 1:0] total_bytes;
	wire [AW - 1:0] transaction_end_addr;
	wire [AW - 1:0] bytes_to_boundary;
	wire [AW - 1:0] beats_to_boundary;
	function automatic [AW - 1:0] sv2v_cast_DE851;
		input reg [AW - 1:0] inp;
		sv2v_cast_DE851 = inp;
	endfunction
	assign total_bytes = (sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1)) << ax_size;
	assign transaction_end_addr = (current_addr + total_bytes) - sv2v_cast_DE851_signed(1);
	assign next_boundary_addr = (current_addr | sv2v_cast_DE851(alignment_mask)) + sv2v_cast_DE851_signed(1);
	assign bytes_to_boundary = next_boundary_addr - current_addr;
	assign beats_to_boundary = bytes_to_boundary >> ax_size;
	wire crosses_boundary;
	wire has_beats_before_boundary;
	wire beats_fit_before_boundary;
	assign crosses_boundary = transaction_end_addr >= next_boundary_addr;
	assign has_beats_before_boundary = beats_to_boundary > 0;
	assign beats_fit_before_boundary = beats_to_boundary <= (sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1));
	assign split_required = (crosses_boundary && has_beats_before_boundary) && beats_fit_before_boundary;
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign split_len = (split_required ? sv2v_cast_8(beats_to_boundary - sv2v_cast_DE851_signed(1)) : current_len);
	wire [AW - 1:0] split_beats_actual;
	wire [AW - 1:0] original_beats_total;
	wire [AW - 1:0] remaining_beats_actual;
	assign original_beats_total = sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1);
	assign split_beats_actual = (split_required ? beats_to_boundary : original_beats_total);
	assign remaining_beats_actual = (split_required ? original_beats_total - split_beats_actual : sv2v_cast_DE851_signed(0));
	assign remaining_len_after_split = (split_required ? (remaining_beats_actual > 0 ? sv2v_cast_8(remaining_beats_actual - sv2v_cast_DE851_signed(1)) : 8'sd0) : 8'sd0);
	assign new_split_needed = (split_required && is_idle_state) && transaction_valid;
	always @(posedge aclk)
		if ((aresetn && transaction_valid) && is_idle_state)
			;
	always @(posedge aclk)
		if (aresetn && transaction_valid) begin
			if (split_required)
				;
		end
endmodule
