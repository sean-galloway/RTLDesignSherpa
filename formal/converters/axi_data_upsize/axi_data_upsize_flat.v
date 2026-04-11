module axi_data_upsize (
	aclk,
	aresetn,
	narrow_valid,
	narrow_ready,
	narrow_data,
	narrow_sideband,
	narrow_last,
	wide_valid,
	wide_ready,
	wide_data,
	wide_sideband,
	wide_last
);
	parameter signed [31:0] NARROW_WIDTH = 32;
	parameter signed [31:0] WIDE_WIDTH = 128;
	parameter signed [31:0] NARROW_SB_WIDTH = 0;
	parameter signed [31:0] WIDE_SB_WIDTH = 0;
	parameter signed [31:0] SB_OR_MODE = 0;
	localparam signed [31:0] WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH;
	localparam signed [31:0] PTR_WIDTH = $clog2(WIDTH_RATIO);
	localparam signed [31:0] NARROW_SB_PORT_WIDTH = (NARROW_SB_WIDTH > 0 ? NARROW_SB_WIDTH : 1);
	localparam signed [31:0] WIDE_SB_PORT_WIDTH = (WIDE_SB_WIDTH > 0 ? WIDE_SB_WIDTH : 1);
	input wire aclk;
	input wire aresetn;
	input wire narrow_valid;
	output wire narrow_ready;
	input wire [NARROW_WIDTH - 1:0] narrow_data;
	input wire [NARROW_SB_PORT_WIDTH - 1:0] narrow_sideband;
	input wire narrow_last;
	output wire wide_valid;
	input wire wide_ready;
	output wire [WIDE_WIDTH - 1:0] wide_data;
	output wire [WIDE_SB_PORT_WIDTH - 1:0] wide_sideband;
	output wire wide_last;
	initial begin
		if (WIDE_WIDTH <= NARROW_WIDTH)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi_data_upsize.sv:78:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be > NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if ((WIDE_WIDTH % NARROW_WIDTH) != 0)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi_data_upsize.sv:80:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi_data_upsize.sv:82:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
	end
	reg [WIDE_WIDTH - 1:0] r_data_accumulator;
	reg [WIDE_SB_PORT_WIDTH - 1:0] r_sideband_accumulator;
	reg [PTR_WIDTH - 1:0] r_beat_ptr;
	reg r_wide_valid;
	reg r_last_buffered;
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	always @(posedge aclk)
		if (!aresetn) begin
			r_data_accumulator <= 1'sb0;
			r_beat_ptr <= 1'sb0;
			r_wide_valid <= 1'b0;
			r_last_buffered <= 1'b0;
		end
		else begin
			if (narrow_valid && narrow_ready) begin
				r_data_accumulator[r_beat_ptr * NARROW_WIDTH+:NARROW_WIDTH] <= narrow_data;
				if ((r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || narrow_last) begin
					r_wide_valid <= 1'b1;
					r_beat_ptr <= 1'sb0;
					r_last_buffered <= narrow_last;
				end
				else
					r_beat_ptr <= r_beat_ptr + 1'b1;
			end
			if (r_wide_valid && wide_ready) begin
				r_wide_valid <= 1'b0;
				r_last_buffered <= 1'b0;
			end
		end
	function automatic [WIDE_SB_PORT_WIDTH - 1:0] sv2v_cast_5BF29;
		input reg [WIDE_SB_PORT_WIDTH - 1:0] inp;
		sv2v_cast_5BF29 = inp;
	endfunction
	generate
		if (NARROW_SB_WIDTH > 0) begin : gen_sideband_accumulation
			if (SB_OR_MODE != 0) begin : gen_or_mode
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						r_sideband_accumulator <= 1'sb0;
					else if (narrow_valid && narrow_ready) begin
						if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
							r_sideband_accumulator <= sv2v_cast_5BF29(narrow_sideband);
						else
							r_sideband_accumulator <= r_sideband_accumulator | sv2v_cast_5BF29(narrow_sideband);
					end
			end
			else begin : gen_concat_mode
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						r_sideband_accumulator <= 1'sb0;
					else if (narrow_valid && narrow_ready)
						r_sideband_accumulator[r_beat_ptr * NARROW_SB_WIDTH+:NARROW_SB_WIDTH] <= narrow_sideband[NARROW_SB_WIDTH - 1:0];
			end
		end
	endgenerate
	assign narrow_ready = !r_wide_valid || wide_ready;
	assign wide_valid = r_wide_valid;
	assign wide_data = r_data_accumulator;
	assign wide_sideband = r_sideband_accumulator;
	assign wide_last = r_last_buffered && r_wide_valid;
endmodule
