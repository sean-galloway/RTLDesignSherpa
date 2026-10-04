module axi_data_dnsize (
	aclk,
	aresetn,
	burst_len,
	burst_start,
	start_lane,
	wide_valid,
	wide_ready,
	wide_data,
	wide_sideband,
	wide_last,
	narrow_valid,
	narrow_ready,
	narrow_data,
	narrow_sideband,
	narrow_last
);
	parameter signed [31:0] WIDE_WIDTH = 128;
	parameter signed [31:0] NARROW_WIDTH = 32;
	parameter signed [31:0] WIDE_SB_WIDTH = 0;
	parameter signed [31:0] NARROW_SB_WIDTH = 0;
	parameter signed [31:0] SB_BROADCAST = 1;
	parameter signed [31:0] TRACK_BURSTS = 0;
	parameter signed [31:0] BURST_LEN_WIDTH = 8;
	localparam signed [31:0] WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH;
	localparam signed [31:0] PTR_WIDTH = $clog2(WIDTH_RATIO);
	localparam signed [31:0] WIDE_SB_PORT_WIDTH = (WIDE_SB_WIDTH > 0 ? WIDE_SB_WIDTH : 1);
	localparam signed [31:0] NARROW_SB_PORT_WIDTH = (NARROW_SB_WIDTH > 0 ? NARROW_SB_WIDTH : 1);
	input wire aclk;
	input wire aresetn;
	input wire [BURST_LEN_WIDTH - 1:0] burst_len;
	input wire burst_start;
	input wire [PTR_WIDTH - 1:0] start_lane;
	input wire wide_valid;
	output wire wide_ready;
	input wire [WIDE_WIDTH - 1:0] wide_data;
	input wire [WIDE_SB_PORT_WIDTH - 1:0] wide_sideband;
	input wire wide_last;
	output wire narrow_valid;
	input wire narrow_ready;
	output wire [NARROW_WIDTH - 1:0] narrow_data;
	output wire [NARROW_SB_PORT_WIDTH - 1:0] narrow_sideband;
	output wire narrow_last;
	initial begin
		if (NARROW_WIDTH >= WIDE_WIDTH)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:91:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "NARROW_WIDTH (%0d) must be < WIDE_WIDTH (%0d)", NARROW_WIDTH, WIDE_WIDTH);
		if ((WIDE_WIDTH % NARROW_WIDTH) != 0)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:93:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:95:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
	end
	reg [PTR_WIDTH - 1:0] r_beat_ptr;
	reg [BURST_LEN_WIDTH - 1:0] r_slave_beat_count;
	reg [BURST_LEN_WIDTH - 1:0] r_slave_total_beats;
	reg r_burst_active;
	reg r_first_wide_of_burst;
	wire w_burst_opening;
	assign w_burst_opening = ((TRACK_BURSTS != 0) && burst_start) && !r_burst_active;
	generate
		if (1) begin : gen_single_buffer
			reg [WIDE_WIDTH - 1:0] r_data_buffer;
			reg [WIDE_SB_PORT_WIDTH - 1:0] r_sideband_buffer;
			reg r_wide_buffered;
			reg r_last_buffered;
		end
	endgenerate
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	generate
		if (1) begin : gen_single_buffer_sm
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					gen_single_buffer.r_data_buffer <= 1'sb0;
					r_beat_ptr <= 1'sb0;
					gen_single_buffer.r_wide_buffered <= 1'b0;
					gen_single_buffer.r_last_buffered <= 1'b0;
					if (TRACK_BURSTS != 0) begin
						r_slave_beat_count <= 1'sb0;
						r_slave_total_beats <= 1'sb0;
						r_burst_active <= 1'b0;
						r_first_wide_of_burst <= 1'b0;
					end
				end
				else begin
					if (w_burst_opening) begin
						r_slave_total_beats <= burst_len + 1'b1;
						r_slave_beat_count <= 1'sb0;
						r_burst_active <= 1'b1;
						r_first_wide_of_burst <= 1'b1;
					end
					if (gen_single_buffer.r_wide_buffered && narrow_ready) begin
						if ((TRACK_BURSTS != 0) && r_burst_active) begin
							if ((r_slave_beat_count + 1'b1) >= r_slave_total_beats) begin
								gen_single_buffer.r_wide_buffered <= 1'b0;
								r_beat_ptr <= 1'sb0;
								r_slave_beat_count <= 1'sb0;
								r_burst_active <= 1'b0;
							end
							else if (r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) begin
								gen_single_buffer.r_wide_buffered <= 1'b0;
								r_beat_ptr <= 1'sb0;
								r_slave_beat_count <= r_slave_beat_count + 1'b1;
							end
							else begin
								r_beat_ptr <= r_beat_ptr + 1'b1;
								r_slave_beat_count <= r_slave_beat_count + 1'b1;
							end
						end
						else if (r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) begin
							gen_single_buffer.r_wide_buffered <= 1'b0;
							r_beat_ptr <= 1'sb0;
						end
						else
							r_beat_ptr <= r_beat_ptr + 1'b1;
					end
					if (wide_valid && wide_ready) begin
						gen_single_buffer.r_data_buffer <= wide_data;
						gen_single_buffer.r_last_buffered <= wide_last;
						gen_single_buffer.r_wide_buffered <= 1'b1;
						if ((TRACK_BURSTS != 0) && (r_first_wide_of_burst || w_burst_opening)) begin
							r_beat_ptr <= start_lane;
							r_first_wide_of_burst <= 1'b0;
						end
						else
							r_beat_ptr <= 1'sb0;
					end
				end
		end
		if (WIDE_SB_WIDTH > 0) begin : gen_sideband_buffer_logic
			if (1) begin : gen_single_sb
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						gen_single_buffer.r_sideband_buffer <= 1'sb0;
					else if (wide_valid && wide_ready)
						gen_single_buffer.r_sideband_buffer <= wide_sideband;
			end
		end
	endgenerate
	wire w_last_narrow_beat;
	assign w_last_narrow_beat = r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1);
	generate
		if (1) begin : gen_single_buffer_outputs
			assign narrow_data = gen_single_buffer.r_data_buffer[r_beat_ptr * NARROW_WIDTH+:NARROW_WIDTH];
			if (NARROW_SB_WIDTH > 0) begin : gen_sideband
				if (SB_BROADCAST != 0) begin : gen_broadcast
					assign narrow_sideband = gen_single_buffer.r_sideband_buffer[NARROW_SB_WIDTH - 1:0];
				end
				else begin : gen_slice
					assign narrow_sideband = gen_single_buffer.r_sideband_buffer[r_beat_ptr * NARROW_SB_WIDTH+:NARROW_SB_WIDTH];
				end
			end
			else begin : gen_no_sideband
				assign narrow_sideband = 1'sb0;
			end
			if (TRACK_BURSTS != 0) begin : gen_tracked_last
				assign narrow_last = (gen_single_buffer.r_wide_buffered && r_burst_active) && ((r_slave_beat_count + 1'b1) >= r_slave_total_beats);
			end
			else begin : gen_simple_last
				assign narrow_last = (gen_single_buffer.r_wide_buffered && gen_single_buffer.r_last_buffered) && w_last_narrow_beat;
			end
			assign narrow_valid = gen_single_buffer.r_wide_buffered;
			if (TRACK_BURSTS != 0) begin : gen_wide_ready_tracked
				wire mid_burst_replace = (r_burst_active && (r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1))) && ((r_slave_beat_count + 1'b1) < r_slave_total_beats);
				assign wide_ready = !gen_single_buffer.r_wide_buffered || (narrow_ready && mid_burst_replace);
			end
			else begin : gen_wide_ready_simple
				assign wide_ready = !gen_single_buffer.r_wide_buffered || (narrow_ready && w_last_narrow_beat);
			end
		end
	endgenerate
endmodule
