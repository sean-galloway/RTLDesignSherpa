module reset_sync (
	clk,
	rst_n,
	sync_rst_n
);
	reg _sv2v_0;
	parameter signed [31:0] N = 3;
	parameter [0:0] KEEP_ATTRS = 1'b1;
	parameter [0:0] IN_ACTIVE_LOW = 1'b1;
	parameter [0:0] OUT_ACTIVE_LOW = 1'b1;
	parameter [0:0] ASYNC_ASSERT = 1'b1;
	input wire clk;
	input wire rst_n;
	output reg sync_rst_n;
	generate
		if (N < 2) begin : g_illegal
			initial $display("Error [%0t] /mnt/data/github/RTLDesignSherpa/rtl/cdc/reset_sync.sv:248:17 - reset_sync.g_illegal.<unnamed_block>\n msg: ", $time, "reset_sync: N must be >= 2 (got %0d)", N);
		end
	endgenerate
	wire rst_in_h = (IN_ACTIVE_LOW ? ~rst_n : rst_n);
	generate
		if (ASYNC_ASSERT) begin : g_async_assert
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
		else begin : g_sync_only
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module counter_bin (
	clk,
	rst_n,
	enable,
	counter_bin_curr,
	counter_bin_next
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 5;
	parameter signed [31:0] MAX = 10;
	input wire clk;
	input wire rst_n;
	input wire enable;
	output reg [WIDTH - 1:0] counter_bin_curr;
	output reg [WIDTH - 1:0] counter_bin_next;
	wire [WIDTH - 2:0] w_max_val;
	function automatic signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] sv2v_cast_00F62_signed;
		input reg signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] inp;
		sv2v_cast_00F62_signed = inp;
	endfunction
	assign w_max_val = sv2v_cast_00F62_signed(MAX - 1);
	always @(*) begin
		if (_sv2v_0)
			;
		if (enable) begin
			if (counter_bin_curr[WIDTH - 2:0] == w_max_val)
				counter_bin_next = {~counter_bin_curr[WIDTH - 1], {WIDTH - 1 {1'b0}}};
			else
				counter_bin_next = counter_bin_curr + 1;
		end
		else
			counter_bin_next = counter_bin_curr;
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			counter_bin_curr <= 'b0;
		else
			counter_bin_curr <= counter_bin_next;
	initial _sv2v_0 = 0;
endmodule
module gaxi_skid_buffer (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	count,
	rd_valid,
	rd_ready,
	rd_count,
	rd_data
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DEPTH = 2;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output reg wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire [3:0] count;
	output reg rd_valid;
	input wire rd_ready;
	output wire [3:0] rd_count;
	output wire [DW - 1:0] rd_data;
	localparam signed [31:0] SLOTS = (DEPTH == 0 ? 1 : DEPTH);
	reg [DW - 1:0] r_data [0:SLOTS - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH != 0) && ((DEPTH < 2) || (DEPTH > 8))) begin : gen_depth_guard
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/amba/gaxi/gaxi_skid_buffer.sv:107:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive, or 0 (pass-through)", DEPTH);
		end
	endgenerate
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		if (DEPTH == 0) begin : g_bypass
			wire [1:1] sv2v_tmp_B1958;
			assign sv2v_tmp_B1958 = rd_ready;
			always @(*) wr_ready = sv2v_tmp_B1958;
			wire [1:1] sv2v_tmp_00E98;
			assign sv2v_tmp_00E98 = wr_valid;
			always @(*) rd_valid = sv2v_tmp_00E98;
			assign rd_data = wr_data;
			wire [4:1] sv2v_tmp_953DA;
			assign sv2v_tmp_953DA = 1'sb0;
			always @(*) r_data_count = sv2v_tmp_953DA;
			wire [DW:1] sv2v_tmp_D35D5;
			assign sv2v_tmp_D35D5 = 1'sb0;
			always @(*) r_data[0] = sv2v_tmp_D35D5;
			assign rd_count = 1'sb0;
			assign count = 1'sb0;
			wire w_bypass_unused;
			assign w_bypass_unused = &{1'b0, axi_aclk, axi_aresetn, r_data[0], r_data_count, w_wr_xfer, w_rd_xfer};
		end
		else begin : g_skid
			genvar _gv_gi_1;
			for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
				localparam gi = _gv_gi_1;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_data[gi] <= 1'sb0;
					else
						(* full_case, parallel_case *)
						case ({w_wr_xfer, w_rd_xfer})
							2'b10:
								if (r_data_count == gi[3:0])
									r_data[gi] <= wr_data;
							2'b01:
								if (gi < (DEPTH - 1))
									r_data[gi] <= r_data[gi + 1];
								else
									r_data[gi] <= 1'sb0;
							2'b11:
								if ((r_data_count >= 1) && (gi[3:0] == (r_data_count - 4'd1)))
									r_data[gi] <= wr_data;
								else if (gi < (DEPTH - 1))
									r_data[gi] <= r_data[gi + 1];
								else
									r_data[gi] <= 1'sb0;
							default:
								;
						endcase
			end
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_data_count <= 1'sb0;
				else
					(* full_case, parallel_case *)
					case ({w_wr_xfer, w_rd_xfer})
						2'b10: r_data_count <= r_data_count + 4'd1;
						2'b01: r_data_count <= r_data_count - 4'd1;
						default:
							;
					endcase
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn) begin
					wr_ready <= 1'b0;
					rd_valid <= 1'b0;
				end
				else begin
					wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
					rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
				end
			assign rd_data = r_data[0];
			assign rd_count = r_data_count;
			assign count = r_data_count;
		end
	endgenerate
endmodule
module axi_data_upsize (
	aclk,
	aresetn,
	narrow_valid,
	narrow_ready,
	narrow_data,
	narrow_sideband,
	narrow_last,
	start_lane,
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
	input wire [PTR_WIDTH - 1:0] start_lane;
	output wire wide_valid;
	input wire wide_ready;
	output wire [WIDE_WIDTH - 1:0] wide_data;
	output wire [WIDE_SB_PORT_WIDTH - 1:0] wide_sideband;
	output wire wide_last;
	initial begin
		if (WIDE_WIDTH <= NARROW_WIDTH)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:87:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be > NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if ((WIDE_WIDTH % NARROW_WIDTH) != 0)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:89:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:91:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
	end
	reg [WIDE_WIDTH - 1:0] r_data_accumulator;
	reg [WIDE_SB_PORT_WIDTH - 1:0] r_sideband_accumulator;
	reg [PTR_WIDTH - 1:0] r_beat_ptr;
	reg r_wide_valid;
	reg r_last_buffered;
	reg r_burst_fresh;
	wire [PTR_WIDTH - 1:0] w_lane;
	assign w_lane = (r_beat_ptr == {PTR_WIDTH {1'sb0}} ? (r_burst_fresh ? start_lane : {PTR_WIDTH {1'sb0}}) : r_beat_ptr);
	wire narrow_completes_group;
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	assign narrow_completes_group = (narrow_valid && narrow_ready) && ((w_lane == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || narrow_last);
	wire wide_accept;
	assign wide_accept = r_wide_valid && wide_ready;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_data_accumulator <= 1'sb0;
			r_beat_ptr <= 1'sb0;
			r_wide_valid <= 1'b0;
			r_last_buffered <= 1'b0;
			r_burst_fresh <= 1'b1;
		end
		else begin
			if (narrow_valid && narrow_ready) begin
				if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
					r_data_accumulator <= {{WIDE_WIDTH - NARROW_WIDTH {1'b0}}, narrow_data} << (w_lane * NARROW_WIDTH);
				else
					r_data_accumulator[w_lane * NARROW_WIDTH+:NARROW_WIDTH] <= narrow_data;
				if (narrow_completes_group)
					r_beat_ptr <= 1'sb0;
				else
					r_beat_ptr <= w_lane + 1'b1;
				r_burst_fresh <= narrow_last;
			end
			if (narrow_completes_group) begin
				r_wide_valid <= 1'b1;
				r_last_buffered <= narrow_last;
			end
			else if (wide_accept) begin
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
						else if (sv2v_cast_5BF29(narrow_sideband) > r_sideband_accumulator)
							r_sideband_accumulator <= sv2v_cast_5BF29(narrow_sideband);
					end
			end
			else begin : gen_concat_mode
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						r_sideband_accumulator <= 1'sb0;
					else if (narrow_valid && narrow_ready) begin
						if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
							r_sideband_accumulator <= {{WIDE_SB_PORT_WIDTH - NARROW_SB_WIDTH {1'b0}}, narrow_sideband[NARROW_SB_WIDTH - 1:0]} << (w_lane * NARROW_SB_WIDTH);
						else
							r_sideband_accumulator[w_lane * NARROW_SB_WIDTH+:NARROW_SB_WIDTH] <= narrow_sideband[NARROW_SB_WIDTH - 1:0];
					end
			end
		end
	endgenerate
	assign narrow_ready = !r_wide_valid || wide_ready;
	assign wide_valid = r_wide_valid;
	assign wide_data = r_data_accumulator;
	assign wide_sideband = r_sideband_accumulator;
	assign wide_last = r_last_buffered && r_wide_valid;
endmodule
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
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:91:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "NARROW_WIDTH (%0d) must be < WIDE_WIDTH (%0d)", NARROW_WIDTH, WIDE_WIDTH);
		if ((WIDE_WIDTH % NARROW_WIDTH) != 0)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:93:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv:95:13 - axi_data_dnsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
	end
	reg [PTR_WIDTH - 1:0] r_beat_ptr;
	reg [BURST_LEN_WIDTH:0] r_slave_beat_count;
	reg [BURST_LEN_WIDTH:0] r_slave_total_beats;
	reg r_burst_active;
	reg r_first_wide_of_burst;
	wire w_burst_opening;
	wire w_burst_final;
	wire w_burst_closing;
	assign w_burst_final = ((TRACK_BURSTS != 0) && r_burst_active) && ((r_slave_beat_count + 1'b1) >= r_slave_total_beats);
	assign w_burst_closing = (narrow_valid && narrow_ready) && w_burst_final;
	assign w_burst_opening = ((TRACK_BURSTS != 0) && burst_start) && (!r_burst_active || w_burst_closing);
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
						r_slave_total_beats <= {1'b0, burst_len} + 1'b1;
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
								if (!w_burst_opening)
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
				assign wide_ready = (!gen_single_buffer.r_wide_buffered || (narrow_ready && mid_burst_replace)) || ((narrow_ready && w_burst_final) && burst_start);
			end
			else begin : gen_wide_ready_simple
				assign wide_ready = !gen_single_buffer.r_wide_buffered || (narrow_ready && w_last_narrow_beat);
			end
		end
	endgenerate
endmodule
module axi4_dwidth_converter_rd (
	aclk,
	aresetn,
	s_axi_arid,
	s_axi_araddr,
	s_axi_arlen,
	s_axi_arsize,
	s_axi_arburst,
	s_axi_arlock,
	s_axi_arcache,
	s_axi_arprot,
	s_axi_arqos,
	s_axi_arregion,
	s_axi_aruser,
	s_axi_arvalid,
	s_axi_arready,
	s_axi_rid,
	s_axi_rdata,
	s_axi_rresp,
	s_axi_rlast,
	s_axi_ruser,
	s_axi_rvalid,
	s_axi_rready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arlock,
	m_axi_arcache,
	m_axi_arprot,
	m_axi_arqos,
	m_axi_arregion,
	m_axi_aruser,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_ruser,
	m_axi_rvalid,
	m_axi_rready
);
	reg _sv2v_0;
	parameter signed [31:0] S_AXI_DATA_WIDTH = 32;
	parameter signed [31:0] M_AXI_DATA_WIDTH = 128;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] SKID_DEPTH_AR = 4;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] RASM_DEPTH = 272;
	parameter signed [31:0] RASM_MAX_OUTSTANDING = 16;
	parameter [0:0] R_INTERLEAVE = 1'b1;
	localparam signed [31:0] S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] WIDTH_RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH : S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
	localparam [0:0] UPSIZE = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam [0:0] DOWNSIZE = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam signed [31:0] NUM_IDS = 1 << AXI_ID_WIDTH;
	localparam signed [31:0] LANE_W = $clog2(WIDTH_RATIO);
	localparam signed [31:0] PSB_W = (R_INTERLEAVE ? 2 : (2 + AXI_ID_WIDTH) + AXI_USER_WIDTH);
	localparam signed [31:0] AR_WIDTH = ((AXI_ID_WIDTH + AXI_ADDR_WIDTH) + 29) + AXI_USER_WIDTH;
	localparam signed [31:0] R_WIDTH = (((S_AXI_DATA_WIDTH + 2) + AXI_USER_WIDTH) + 1) + AXI_ID_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_arid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_araddr;
	input wire [7:0] s_axi_arlen;
	input wire [2:0] s_axi_arsize;
	input wire [1:0] s_axi_arburst;
	input wire s_axi_arlock;
	input wire [3:0] s_axi_arcache;
	input wire [2:0] s_axi_arprot;
	input wire [3:0] s_axi_arqos;
	input wire [3:0] s_axi_arregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_aruser;
	input wire s_axi_arvalid;
	output wire s_axi_arready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_rid;
	output wire [S_AXI_DATA_WIDTH - 1:0] s_axi_rdata;
	output wire [1:0] s_axi_rresp;
	output wire s_axi_rlast;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_ruser;
	output wire s_axi_rvalid;
	input wire s_axi_rready;
	output wire [AXI_ID_WIDTH - 1:0] m_axi_arid;
	output wire [AXI_ADDR_WIDTH - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arlock;
	output wire [3:0] m_axi_arcache;
	output wire [2:0] m_axi_arprot;
	output wire [3:0] m_axi_arqos;
	output wire [3:0] m_axi_arregion;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_aruser;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [AXI_ID_WIDTH - 1:0] m_axi_rid;
	input wire [M_AXI_DATA_WIDTH - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire [AXI_USER_WIDTH - 1:0] m_axi_ruser;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	wire w_aresetn;
	reset_sync #(
		.N(3),
		.KEEP_ATTRS(1'b1),
		.IN_ACTIVE_LOW(1'b1),
		.OUT_ACTIVE_LOW(1'b1),
		.ASYNC_ASSERT(1'b1)
	) u_reset_sync(
		.clk(aclk),
		.rst_n(aresetn),
		.sync_rst_n(w_aresetn)
	);
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:182:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:184:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:186:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:188:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
	end
	wire [AR_WIDTH - 1:0] int_ar_data;
	wire int_ar_valid;
	wire int_ar_ready;
	wire [AXI_ID_WIDTH - 1:0] int_arid;
	wire [AXI_ADDR_WIDTH - 1:0] int_araddr;
	wire [7:0] int_arlen;
	wire [2:0] int_arsize;
	wire [1:0] int_arburst;
	wire int_arlock;
	wire [3:0] int_arcache;
	wire [2:0] int_arprot;
	wire [3:0] int_arqos;
	wire [3:0] int_arregion;
	wire [AXI_USER_WIDTH - 1:0] int_aruser;
	wire [R_WIDTH - 1:0] int_r_data;
	wire int_r_valid;
	wire int_r_ready;
	wire [AXI_ID_WIDTH - 1:0] int_rid;
	reg [S_AXI_DATA_WIDTH - 1:0] int_rdata;
	wire [1:0] int_rresp;
	wire int_rlast;
	wire [AXI_USER_WIDTH - 1:0] int_ruser;
	reg rasm_rec_valid [0:NUM_IDS - 1];
	wire w_rasm_push;
	wire [AXI_ID_WIDTH - 1:0] w_rasm_push_id;
	reg rasm_rec_final [0:NUM_IDS - 1];
	reg [8:0] rasm_rec_beats [0:NUM_IDS - 1];
	reg [7:0] rasm_rec_nlen [0:NUM_IDS - 1];
	reg [$clog2(WIDTH_RATIO) - 1:0] rasm_rec_lane [0:NUM_IDS - 1];
	localparam [1:0] CM_PACK = 2'd0;
	localparam [1:0] CM_PASS = 2'd1;
	localparam [1:0] CM_EXPAND = 2'd2;
	reg [1:0] rasm_rec_mode [0:NUM_IDS - 1];
	reg [LANE_W - 1:0] rasm_rec_rmask [0:NUM_IDS - 1];
	reg [2:0] rasm_rec_size [0:NUM_IDS - 1];
	reg [1:0] rasm_rec_burst [0:NUM_IDS - 1];
	wire [AXI_ADDR_WIDTH - 1:0] w_rasm_push_addr;
	wire [LANE_W - 1:0] w_rasm_push_lane;
	wire w_rasm_push_plain;
	wire w_blen_wr_ready;
	wire w_blen_rd_valid;
	wire [7:0] w_blen_rd_data;
	wire [7:0] w_blen_rd_lane;
	wire w_blen_pop;
	wire arsplit_final;
	wire arsplit_pop;
	wire [AXI_ID_WIDTH - 1:0] prim_rid;
	wire [M_AXI_DATA_WIDTH - 1:0] prim_rdata;
	wire [1:0] prim_rresp;
	wire prim_rlast;
	wire [AXI_USER_WIDTH - 1:0] prim_ruser;
	wire prim_rvalid;
	wire prim_rready;
	wire w_cur_final;
	wire w_bstart;
	wire [7:0] w_blen;
	wire [7:0] w_blane;
	wire [PSB_W - 1:0] prim_sb;
	wire [PSB_W - 1:0] int_sb;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(AR_WIDTH)
	) ar_skid(
		.axi_aclk(aclk),
		.axi_aresetn(w_aresetn),
		.wr_valid(s_axi_arvalid),
		.wr_ready(s_axi_arready),
		.wr_data({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos, s_axi_arregion, s_axi_aruser}),
		.rd_valid(int_ar_valid),
		.rd_ready(int_ar_ready),
		.rd_data(int_ar_data),
		.count(),
		.rd_count()
	);
	assign {int_arid, int_araddr, int_arlen, int_arsize, int_arburst, int_arlock, int_arcache, int_arprot, int_arqos, int_arregion, int_aruser} = int_ar_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(R_WIDTH)
	) r_skid(
		.axi_aclk(aclk),
		.axi_aresetn(w_aresetn),
		.wr_valid(int_r_valid),
		.wr_ready(int_r_ready),
		.wr_data(int_r_data),
		.rd_valid(s_axi_rvalid),
		.rd_ready(s_axi_rready),
		.rd_data({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
		.count(),
		.rd_count()
	);
	assign int_r_data = {int_rid, int_rdata, int_rresp, int_rlast, int_ruser};
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	function automatic [9:0] sv2v_cast_10;
		input reg [9:0] inp;
		sv2v_cast_10 = inp;
	endfunction
	function automatic signed [9:0] sv2v_cast_10_signed;
		input reg signed [9:0] inp;
		sv2v_cast_10_signed = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	function automatic [LANE_W - 1:0] sv2v_cast_3FA0D;
		input reg [LANE_W - 1:0] inp;
		sv2v_cast_3FA0D = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_ar_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] MAX_BEATS = 256;
			localparam signed [31:0] CNTW = 9 + $clog2(WIDTH_RATIO);
			localparam signed [31:0] AW = AXI_ADDR_WIDTH;
			reg [CNTW - 1:0] r_split_remaining;
			reg [AW - 1:0] r_split_addr;
			reg [8:0] r_beats_left;
			reg r_split_active;
			wire [1:0] w_mode;
			wire [2:0] w_rlog;
			wire [AW - 1:0] w_bmask;
			wire [AW - 1:0] w_wmask;
			wire [AW - 1:0] w_next_beat;
			wire [8:0] w_lane_in_beat;
			wire [8:0] w_cap;
			reg [8:0] w_this_beats;
			reg w_this_last;
			wire w_ar_issue;
			wire w_id_free;
			assign w_mode = (int_arsize <= sv2v_cast_3_signed(MASTER_SIZE) ? CM_PASS : (int_arburst == 2'b01 ? CM_PACK : CM_EXPAND));
			assign w_rlog = int_arsize - sv2v_cast_3_signed(MASTER_SIZE);
			function automatic signed [AW - 1:0] sv2v_cast_DE851_signed;
				input reg signed [AW - 1:0] inp;
				sv2v_cast_DE851_signed = inp;
			endfunction
			assign w_bmask = (sv2v_cast_DE851_signed(1) << int_arsize) - sv2v_cast_DE851_signed(1);
			function automatic [AW - 1:0] sv2v_cast_DE851;
				input reg [AW - 1:0] inp;
				sv2v_cast_DE851 = inp;
			endfunction
			assign w_wmask = ((sv2v_cast_DE851(int_arlen) + sv2v_cast_DE851_signed(1)) << int_arsize) - sv2v_cast_DE851_signed(1);
			assign w_lane_in_beat = sv2v_cast_9((r_split_addr & w_bmask) >> MASTER_SIZE);
			assign w_cap = sv2v_cast_9_signed(MAX_BEATS) - w_lane_in_beat;
			assign w_next_beat = (int_arburst == 2'b10 ? (r_split_addr & ~w_wmask) | ((((r_split_addr & ~w_bmask) + w_bmask) + sv2v_cast_DE851_signed(1)) & w_wmask) : r_split_addr);
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_mode)
					CM_PASS: begin
						w_this_beats = sv2v_cast_9(int_arlen) + 9'd1;
						w_this_last = 1'b1;
					end
					CM_EXPAND: begin
						w_this_beats = (9'd1 << w_rlog) - w_lane_in_beat;
						w_this_last = r_beats_left == 9'd1;
					end
					default: begin
						begin : sv2v_autoblock_1
							reg [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = w_cap;
							w_this_beats = (r_split_remaining > sv2v_tmp_cast ? w_cap : sv2v_cast_9(r_split_remaining));
						end
						begin : sv2v_autoblock_2
							reg [CNTW - 1:0] sv2v_tmp_cast_1;
							sv2v_tmp_cast_1 = w_cap;
							w_this_last = r_split_remaining <= sv2v_tmp_cast_1;
						end
					end
				endcase
			end
			assign w_ar_issue = m_axi_arvalid && m_axi_arready;
			assign w_id_free = !rasm_rec_valid[int_arid];
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					r_split_remaining <= 1'sb0;
					r_split_addr <= 1'sb0;
					r_beats_left <= 1'sb0;
					r_split_active <= 1'b0;
				end
				else if (!r_split_active) begin
					if (int_ar_valid) begin
						begin : sv2v_autoblock_3
							reg [CNTW - 1:0] sv2v_tmp_cast;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_1;
							reg [CNTW - 1:0] sv2v_tmp_cast_2;
							sv2v_tmp_cast = int_arlen;
							sv2v_tmp_cast_1 = 1;
							sv2v_tmp_cast_2 = (int_araddr & w_bmask) >> MASTER_SIZE;
							r_split_remaining <= ((sv2v_tmp_cast + sv2v_tmp_cast_1) << w_rlog) - sv2v_tmp_cast_2;
						end
						r_split_addr <= int_araddr;
						r_beats_left <= sv2v_cast_9(int_arlen) + 9'd1;
						r_split_active <= 1'b1;
					end
				end
				else if (w_ar_issue) begin
					if (w_this_last) begin
						r_split_remaining <= 1'sb0;
						r_split_active <= 1'b0;
					end
					else begin
						begin : sv2v_autoblock_4
							reg [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = w_this_beats;
							r_split_remaining <= r_split_remaining - sv2v_tmp_cast;
						end
						r_beats_left <= r_beats_left - 9'd1;
						begin : sv2v_autoblock_5
							reg signed [AW - 1:0] sv2v_tmp_cast_1;
							sv2v_tmp_cast_1 = MAX_BEATS * M_STRB_WIDTH;
							r_split_addr <= (w_mode == CM_EXPAND ? w_next_beat : (r_split_addr & ~w_bmask) + sv2v_tmp_cast_1);
						end
					end
				end
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = r_split_addr;
			assign m_axi_arlen = sv2v_cast_8(w_this_beats - 9'd1);
			assign m_axi_arsize = (w_mode == CM_PASS ? int_arsize : MASTER_SIZE[2:0]);
			assign m_axi_arburst = (w_mode == CM_PASS ? int_arburst : 2'b01);
			assign m_axi_arlock = int_arlock;
			assign m_axi_arcache = int_arcache;
			assign m_axi_arprot = int_arprot;
			assign m_axi_arqos = int_arqos;
			assign m_axi_arregion = int_arregion;
			assign m_axi_aruser = int_aruser;
			assign m_axi_arvalid = r_split_active && w_id_free;
			assign int_ar_ready = w_ar_issue && w_this_last;
			assign w_rasm_push = w_ar_issue;
			assign w_rasm_push_id = int_arid;
			assign w_rasm_push_addr = r_split_addr;
			assign w_rasm_push_lane = sv2v_cast_3FA0D(r_split_addr[$clog2(S_STRB_WIDTH) - 1:0] >> MASTER_SIZE);
			assign w_rasm_push_plain = ((w_mode == CM_PACK) && (int_arsize == sv2v_cast_3_signed($clog2(S_STRB_WIDTH)))) && (w_rasm_push_lane == {LANE_W {1'sb0}});
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin : sv2v_autoblock_6
					reg signed [31:0] i;
					for (i = 0; i < NUM_IDS; i = i + 1)
						begin
							rasm_rec_final[i] <= 1'b0;
							rasm_rec_beats[i] <= 1'sb0;
							rasm_rec_mode[i] <= CM_PACK;
							rasm_rec_rmask[i] <= 1'sb0;
							rasm_rec_lane[i] <= 1'sb0;
							rasm_rec_nlen[i] <= 1'sb0;
							rasm_rec_size[i] <= 1'sb0;
							rasm_rec_burst[i] <= 1'sb0;
						end
				end
				else if (w_ar_issue) begin
					rasm_rec_final[int_arid] <= w_this_last;
					rasm_rec_beats[int_arid] <= w_this_beats;
					rasm_rec_mode[int_arid] <= w_mode;
					rasm_rec_rmask[int_arid] <= (w_mode == CM_PASS ? {LANE_W {1'sb0}} : sv2v_cast_3FA0D((9'd1 << w_rlog) - 9'd1));
					rasm_rec_lane[int_arid] <= w_rasm_push_lane;
				end
		end
		else begin : gen_ar_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] ALIGN_BITS = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] R_LANE_W = $clog2(WIDTH_RATIO);
			assign arsplit_final = 1'b1;
			wire [1:0] w_mode;
			wire [7:0] master_arlen;
			wire [AXI_ADDR_WIDTH - 1:0] aligned_araddr;
			assign w_mode = ((int_arburst == 2'b01) && (int_arsize == sv2v_cast_3_signed($clog2(S_STRB_WIDTH))) ? CM_PACK : CM_PASS);
			wire [R_LANE_W - 1:0] w_ar_lane;
			function automatic [R_LANE_W - 1:0] sv2v_cast_DBCFE;
				input reg [R_LANE_W - 1:0] inp;
				sv2v_cast_DBCFE = inp;
			endfunction
			assign w_ar_lane = sv2v_cast_DBCFE(int_araddr[ALIGN_BITS - 1:0] >> $clog2(S_STRB_WIDTH));
			assign master_arlen = sv2v_cast_8((((sv2v_cast_10(w_ar_lane) + sv2v_cast_10(int_arlen)) + sv2v_cast_10_signed(WIDTH_RATIO)) / sv2v_cast_10_signed(WIDTH_RATIO)) - 10'd1);
			assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH - 1:ALIGN_BITS], {ALIGN_BITS {1'b0}}};
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = (w_mode == CM_PASS ? int_araddr : aligned_araddr);
			assign m_axi_arlen = (w_mode == CM_PASS ? int_arlen : master_arlen);
			assign m_axi_arsize = (w_mode == CM_PASS ? int_arsize : MASTER_SIZE[2:0]);
			assign m_axi_arburst = int_arburst;
			assign m_axi_arlock = int_arlock;
			assign m_axi_arcache = int_arcache;
			assign m_axi_arprot = int_arprot;
			assign m_axi_arqos = int_arqos;
			assign m_axi_arregion = int_arregion;
			assign m_axi_aruser = int_aruser;
			assign m_axi_arvalid = int_ar_valid && !rasm_rec_valid[int_arid];
			assign int_ar_ready = m_axi_arready && !rasm_rec_valid[int_arid];
			assign w_rasm_push = int_ar_valid && int_ar_ready;
			assign w_rasm_push_id = int_arid;
			assign w_rasm_push_addr = int_araddr;
			assign w_rasm_push_lane = 1'sb0;
			assign w_rasm_push_plain = w_mode == CM_PACK;
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin : sv2v_autoblock_7
					reg signed [31:0] i;
					for (i = 0; i < NUM_IDS; i = i + 1)
						begin
							rasm_rec_beats[i] <= 1'sb0;
							rasm_rec_nlen[i] <= 1'sb0;
							rasm_rec_lane[i] <= 1'sb0;
							rasm_rec_mode[i] <= CM_PACK;
							rasm_rec_size[i] <= 1'sb0;
							rasm_rec_burst[i] <= 1'sb0;
							rasm_rec_final[i] <= 1'b1;
							rasm_rec_rmask[i] <= 1'sb0;
						end
				end
				else if (int_ar_valid && int_ar_ready) begin
					rasm_rec_beats[int_arid] <= (w_mode == CM_PASS ? sv2v_cast_9(int_arlen) + 9'd1 : sv2v_cast_9(master_arlen) + 9'd1);
					rasm_rec_nlen[int_arid] <= int_arlen;
					rasm_rec_lane[int_arid] <= w_ar_lane;
					rasm_rec_mode[int_arid] <= w_mode;
					rasm_rec_size[int_arid] <= int_arsize;
					rasm_rec_burst[int_arid] <= int_arburst;
				end
		end
	endgenerate
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	generate
		if (R_INTERLEAVE) begin : gen_rilv
			localparam signed [31:0] LW = (WIDTH_RATIO > 1 ? $clog2(WIDTH_RATIO) : 1);
			localparam signed [31:0] RQ_W = ((AXI_ID_WIDTH + M_AXI_DATA_WIDTH) + 3) + AXI_USER_WIDTH;
			wire q_rvalid;
			wire q_rready;
			wire [AXI_ID_WIDTH - 1:0] q_rid;
			wire [M_AXI_DATA_WIDTH - 1:0] q_rdata;
			wire [1:0] q_rresp;
			wire q_rlast;
			wire [AXI_USER_WIDTH - 1:0] q_ruser;
			wire [RQ_W - 1:0] q_rpkt;
			wire w_out_hs;
			gaxi_skid_buffer #(
				.DEPTH(2),
				.DATA_WIDTH(RQ_W)
			) r_in_skid(
				.axi_aclk(aclk),
				.axi_aresetn(w_aresetn),
				.wr_valid(m_axi_rvalid),
				.wr_ready(m_axi_rready),
				.wr_data({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
				.rd_valid(q_rvalid),
				.rd_ready(q_rready),
				.rd_data(q_rpkt),
				.count(),
				.rd_count()
			);
			assign {q_rid, q_rdata, q_rresp, q_rlast, q_ruser} = q_rpkt;
			assign w_out_hs = int_r_valid && int_r_ready;
			assign prim_rvalid = 1'b0;
			assign prim_rid = 1'sb0;
			assign prim_rdata = 1'sb0;
			assign prim_rresp = 1'sb0;
			assign prim_rlast = 1'b0;
			assign prim_ruser = 1'sb0;
			assign prim_sb = 1'sb0;
			assign int_sb = 1'sb0;
			assign w_cur_final = 1'b0;
			assign w_bstart = 1'b0;
			assign w_blen = 1'sb0;
			assign w_blane = 1'sb0;
			if (DOWNSIZE) begin : gen_pack
				wire [M_AXI_DATA_WIDTH - 1:0] w_acc_rd [0:WIDTH_RATIO - 2];
				reg [LW - 1:0] cnt [0:NUM_IDS - 1];
				reg [1:0] worst [0:NUM_IDS - 1];
				wire [LW - 1:0] w_lane;
				wire [LW - 1:0] w_rmask;
				wire w_pass;
				wire w_final;
				wire w_emit;
				wire w_take;
				wire [1:0] w_resp;
				assign w_lane = cnt[q_rid];
				function automatic [LW - 1:0] sv2v_cast_4587C;
					input reg [LW - 1:0] inp;
					sv2v_cast_4587C = inp;
				endfunction
				assign w_rmask = sv2v_cast_4587C(rasm_rec_rmask[q_rid]);
				assign w_pass = rasm_rec_mode[q_rid] == CM_PASS;
				assign w_final = q_rlast && rasm_rec_final[q_rid];
				assign w_emit = (w_pass || ((w_lane & w_rmask) == w_rmask)) || w_final;
				assign w_take = q_rvalid && (!w_emit || int_r_ready);
				assign q_rready = !w_emit || int_r_ready;
				assign w_resp = (q_rresp > worst[q_rid] ? q_rresp : worst[q_rid]);
				always @(*) begin
					if (_sv2v_0)
						;
					int_rdata = 1'sb0;
					begin : sv2v_autoblock_8
						reg signed [31:0] k;
						for (k = 0; k < WIDTH_RATIO; k = k + 1)
							begin : sv2v_autoblock_9
								reg signed [LW - 1:0] sv2v_tmp_cast;
								sv2v_tmp_cast = k;
								if (w_pass || (sv2v_tmp_cast == w_lane))
									int_rdata[k * M_AXI_DATA_WIDTH+:M_AXI_DATA_WIDTH] = q_rdata;
								else begin : sv2v_autoblock_10
									reg signed [LW - 1:0] sv2v_tmp_cast_1;
									sv2v_tmp_cast_1 = k;
									if ((k < (WIDTH_RATIO - 1)) && (sv2v_tmp_cast_1 < w_lane))
										int_rdata[k * M_AXI_DATA_WIDTH+:M_AXI_DATA_WIDTH] = w_acc_rd[k];
								end
							end
					end
				end
				assign int_r_valid = q_rvalid && w_emit;
				assign int_rid = q_rid;
				assign int_rresp = w_resp;
				assign int_rlast = w_final;
				assign int_ruser = q_ruser;
				genvar _gv_k_1;
				for (_gv_k_1 = 0; _gv_k_1 < (WIDTH_RATIO - 1); _gv_k_1 = _gv_k_1 + 1) begin : gen_lane
					localparam k = _gv_k_1;
					reg [M_AXI_DATA_WIDTH - 1:0] acc [0:NUM_IDS - 1];
					always @(posedge aclk) begin : sv2v_autoblock_11
						reg signed [LW - 1:0] sv2v_tmp_cast;
						sv2v_tmp_cast = k;
						if ((w_take && !w_emit) && (w_lane == sv2v_tmp_cast))
							acc[q_rid] <= q_rdata;
					end
					assign w_acc_rd[k] = acc[q_rid];
				end
				always @(posedge aclk or negedge w_aresetn)
					if (!w_aresetn) begin : sv2v_autoblock_12
						reg signed [31:0] i;
						for (i = 0; i < NUM_IDS; i = i + 1)
							begin
								cnt[i] <= 1'sb0;
								worst[i] <= 2'b00;
								rasm_rec_valid[i] <= 1'b0;
							end
					end
					else begin
						if (w_take) begin
							begin : sv2v_autoblock_13
								reg signed [LW - 1:0] sv2v_tmp_cast;
								sv2v_tmp_cast = 1;
								cnt[q_rid] <= w_lane + sv2v_tmp_cast;
							end
							worst[q_rid] <= (w_emit ? 2'b00 : w_resp);
							if (q_rlast)
								rasm_rec_valid[q_rid] <= 1'b0;
						end
						if (w_rasm_push) begin
							rasm_rec_valid[w_rasm_push_id] <= 1'b1;
							begin : sv2v_autoblock_14
								reg [LW - 1:0] sv2v_tmp_cast;
								sv2v_tmp_cast = w_rasm_push_lane;
								cnt[w_rasm_push_id] <= sv2v_tmp_cast;
							end
						end
					end
			end
			else begin : gen_slice
				reg cur_valid;
				reg [AXI_ID_WIDTH - 1:0] cur_rid;
				reg [M_AXI_DATA_WIDTH - 1:0] cur_data;
				reg [1:0] cur_resp;
				reg [AXI_USER_WIDTH - 1:0] cur_user;
				reg [LW - 1:0] cur_lane;
				reg [8:0] cur_rem;
				reg [8:0] rem [0:NUM_IDS - 1];
				reg start [0:NUM_IDS - 1];
				wire w_last_narrow;
				wire w_wide_done;
				wire w_cur_free;
				wire w_load;
				wire w_byp;
				wire [LW - 1:0] w_ld_lane;
				wire [8:0] w_ld_rem;
				localparam signed [31:0] PAW = $clog2(M_STRB_WIDTH);
				reg [PAW - 1:0] pa [0:NUM_IDS - 1];
				reg cur_pass;
				reg cur_rlast;
				wire w_ld_pass;
				wire [PAW - 1:0] w_pa;
				wire [PAW - 1:0] w_pa_bm;
				wire [PAW - 1:0] w_pa_wm;
				wire [PAW - 1:0] w_pa_step;
				wire [PAW - 1:0] w_pa_next;
				wire [15:0] w_pa_span;
				assign w_ld_pass = rasm_rec_mode[q_rid] == CM_PASS;
				assign w_pa = pa[q_rid];
				function automatic [PAW - 1:0] sv2v_cast_B30D0;
					input reg [PAW - 1:0] inp;
					sv2v_cast_B30D0 = inp;
				endfunction
				assign w_pa_bm = sv2v_cast_B30D0((16'd1 << rasm_rec_size[q_rid]) - 16'd1);
				assign w_pa_span = (sv2v_cast_16(rasm_rec_nlen[q_rid]) + 16'd1) << rasm_rec_size[q_rid];
				assign w_pa_wm = sv2v_cast_B30D0(w_pa_span - 16'd1);
				function automatic signed [PAW - 1:0] sv2v_cast_B30D0_signed;
					input reg signed [PAW - 1:0] inp;
					sv2v_cast_B30D0_signed = inp;
				endfunction
				assign w_pa_step = ((w_pa & ~w_pa_bm) + w_pa_bm) + sv2v_cast_B30D0_signed(1);
				assign w_pa_next = (rasm_rec_burst[q_rid] == 2'b00 ? w_pa : (rasm_rec_burst[q_rid] == 2'b10 ? (w_pa & ~w_pa_wm) | (w_pa_step & w_pa_wm) : w_pa_step));
				assign w_last_narrow = (cur_pass ? cur_rlast : cur_rem == 9'd1);
				function automatic signed [LW - 1:0] sv2v_cast_4587C_signed;
					input reg signed [LW - 1:0] inp;
					sv2v_cast_4587C_signed = inp;
				endfunction
				assign w_wide_done = (cur_pass || w_last_narrow) || (cur_lane == sv2v_cast_4587C_signed(WIDTH_RATIO - 1));
				assign w_cur_free = !cur_valid || (w_out_hs && w_wide_done);
				assign q_rready = w_cur_free;
				assign w_load = q_rvalid && w_cur_free;
				assign w_byp = ((cur_valid && !cur_pass) && (cur_rid == q_rid)) && !w_last_narrow;
				function automatic [LW - 1:0] sv2v_cast_4587C;
					input reg [LW - 1:0] inp;
					sv2v_cast_4587C = inp;
				endfunction
				assign w_ld_lane = (w_ld_pass ? sv2v_cast_4587C(w_pa >> $clog2(S_STRB_WIDTH)) : (start[q_rid] || w_byp ? {LW {1'sb0}} : sv2v_cast_4587C(rasm_rec_lane[q_rid])));
				assign w_ld_rem = (w_byp ? cur_rem - 9'd1 : (start[q_rid] ? rem[q_rid] : sv2v_cast_9(rasm_rec_nlen[q_rid]) + 9'd1));
				assign int_r_valid = cur_valid;
				wire [S_AXI_DATA_WIDTH:1] sv2v_tmp_EC17E;
				assign sv2v_tmp_EC17E = cur_data[cur_lane * S_AXI_DATA_WIDTH+:S_AXI_DATA_WIDTH];
				always @(*) int_rdata = sv2v_tmp_EC17E;
				assign int_rid = cur_rid;
				assign int_rresp = cur_resp;
				assign int_rlast = w_last_narrow;
				assign int_ruser = cur_user;
				always @(posedge aclk or negedge w_aresetn)
					if (!w_aresetn) begin
						cur_valid <= 1'b0;
						cur_rid <= 1'sb0;
						cur_data <= 1'sb0;
						cur_resp <= 1'sb0;
						cur_user <= 1'sb0;
						cur_lane <= 1'sb0;
						cur_rem <= 1'sb0;
						cur_pass <= 1'b0;
						cur_rlast <= 1'b0;
						begin : sv2v_autoblock_15
							reg signed [31:0] i;
							for (i = 0; i < NUM_IDS; i = i + 1)
								begin
									rem[i] <= 1'sb0;
									start[i] <= 1'b0;
									pa[i] <= 1'sb0;
									rasm_rec_valid[i] <= 1'b0;
								end
						end
					end
					else begin
						if (w_out_hs) begin
							begin : sv2v_autoblock_16
								reg signed [LW - 1:0] sv2v_tmp_cast;
								sv2v_tmp_cast = 1;
								cur_lane <= cur_lane + sv2v_tmp_cast;
							end
							cur_rem <= cur_rem - 9'd1;
							if (w_last_narrow) begin
								start[cur_rid] <= 1'b0;
								rasm_rec_valid[cur_rid] <= 1'b0;
							end
							else if (w_wide_done && !cur_pass)
								rem[cur_rid] <= cur_rem - 9'd1;
							if (w_wide_done)
								cur_valid <= 1'b0;
						end
						if (w_load) begin
							cur_valid <= 1'b1;
							cur_rid <= q_rid;
							cur_data <= q_rdata;
							cur_resp <= q_rresp;
							cur_user <= q_ruser;
							cur_lane <= w_ld_lane;
							cur_rem <= w_ld_rem;
							cur_pass <= w_ld_pass;
							cur_rlast <= q_rlast;
							if (w_ld_pass)
								pa[q_rid] <= w_pa_next;
							else
								start[q_rid] <= 1'b1;
						end
						if (w_rasm_push) begin
							rasm_rec_valid[w_rasm_push_id] <= 1'b1;
							begin : sv2v_autoblock_17
								reg [PAW - 1:0] sv2v_tmp_cast;
								sv2v_tmp_cast = w_rasm_push_addr;
								pa[w_rasm_push_id] <= sv2v_tmp_cast;
							end
						end
					end
			end
		end
		else begin : gen_rbypass
			localparam signed [31:0] RQ_W = ((AXI_ID_WIDTH + M_AXI_DATA_WIDTH) + 3) + AXI_USER_WIDTH;
			wire q_rvalid;
			wire q_rready;
			wire [AXI_ID_WIDTH - 1:0] q_rid;
			wire [M_AXI_DATA_WIDTH - 1:0] q_rdata;
			wire [1:0] q_rresp;
			wire q_rlast;
			wire [AXI_USER_WIDTH - 1:0] q_ruser;
			wire [RQ_W - 1:0] q_rpkt;
			gaxi_skid_buffer #(
				.DEPTH(2),
				.DATA_WIDTH(RQ_W)
			) r_in_skid(
				.axi_aclk(aclk),
				.axi_aresetn(w_aresetn),
				.wr_valid(m_axi_rvalid),
				.wr_ready(m_axi_rready),
				.wr_data({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
				.rd_valid(q_rvalid),
				.rd_ready(q_rready),
				.rd_data(q_rpkt),
				.count(),
				.rd_count()
			);
			assign {q_rid, q_rdata, q_rresp, q_rlast, q_ruser} = q_rpkt;
			reg r_in_open;
			reg r_out_open;
			wire w_gate;
			wire w_prim_hs;
			wire w_out_hs;
			assign w_prim_hs = prim_rvalid && prim_rready;
			assign w_out_hs = int_r_valid && int_r_ready;
			assign w_gate = (DOWNSIZE ? 1'b1 : (r_in_open || !r_out_open) || (w_out_hs && int_rlast));
			assign prim_rvalid = q_rvalid && w_gate;
			assign q_rready = prim_rready && w_gate;
			assign prim_rid = q_rid;
			assign prim_rdata = q_rdata;
			assign prim_rresp = q_rresp;
			assign prim_rlast = q_rlast;
			assign prim_ruser = q_ruser;
			assign w_cur_final = rasm_rec_final[q_rid];
			assign w_bstart = (q_rvalid && w_gate) && !r_in_open;
			assign w_blen = rasm_rec_nlen[q_rid];
			assign w_blane = sv2v_cast_8(rasm_rec_lane[q_rid]);
			assign prim_sb = {prim_rresp, prim_rid, prim_ruser};
			assign int_rid = int_sb[AXI_USER_WIDTH+:AXI_ID_WIDTH];
			assign int_ruser = int_sb[AXI_USER_WIDTH - 1:0];
			assign int_rresp = int_sb[PSB_W - 1-:2];
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					begin : sv2v_autoblock_18
						reg signed [31:0] i;
						for (i = 0; i < NUM_IDS; i = i + 1)
							rasm_rec_valid[i] <= 1'b0;
					end
					r_in_open <= 1'b0;
					r_out_open <= 1'b0;
				end
				else begin
					if (w_prim_hs)
						r_in_open <= !prim_rlast;
					if (!DOWNSIZE) begin
						if (w_out_hs && int_rlast)
							r_out_open <= 1'b0;
						if (w_prim_hs && !r_in_open)
							r_out_open <= 1'b1;
					end
					if ((DOWNSIZE && w_prim_hs) && prim_rlast)
						rasm_rec_valid[q_rid] <= 1'b0;
					if ((!DOWNSIZE && w_out_hs) && int_rlast)
						rasm_rec_valid[int_rid] <= 1'b0;
					if (w_rasm_push)
						rasm_rec_valid[w_rasm_push_id] <= 1'b1;
				end
		end
		if (R_INTERLEAVE) begin : gen_r_none
			assign arsplit_pop = 1'b0;
			if (DOWNSIZE) begin : gen_tie_dn
				assign arsplit_final = 1'b1;
			end
			assign w_blen_wr_ready = 1'b1;
			assign w_blen_rd_valid = 1'b0;
			assign w_blen_rd_data = 1'sb0;
			assign w_blen_rd_lane = 1'sb0;
			assign w_blen_pop = 1'b0;
		end
		else if (DOWNSIZE) begin : gen_r_downsize
			assign arsplit_final = w_cur_final;
			assign arsplit_pop = ((prim_rvalid && prim_rready) && prim_rlast) && w_cur_final;
			localparam signed [31:0] sv2v_uu_u_r_upsize_NARROW_WIDTH = M_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_WIDE_WIDTH = S_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_WIDTH_RATIO = sv2v_uu_u_r_upsize_WIDE_WIDTH / sv2v_uu_u_r_upsize_NARROW_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_PTR_WIDTH = $clog2(sv2v_uu_u_r_upsize_WIDTH_RATIO);
			localparam [sv2v_uu_u_r_upsize_PTR_WIDTH - 1:0] sv2v_uu_u_r_upsize_ext_start_lane_0 = 1'sb0;
			wire [S_AXI_DATA_WIDTH:1] sv2v_tmp_u_r_upsize_wide_data;
			always @(*) int_rdata = sv2v_tmp_u_r_upsize_wide_data;
			axi_data_upsize #(
				.NARROW_WIDTH(M_AXI_DATA_WIDTH),
				.WIDE_WIDTH(S_AXI_DATA_WIDTH),
				.NARROW_SB_WIDTH(PSB_W),
				.WIDE_SB_WIDTH(PSB_W),
				.SB_OR_MODE(1)
			) u_r_upsize(
				.aclk(aclk),
				.aresetn(w_aresetn),
				.narrow_valid(prim_rvalid),
				.narrow_ready(prim_rready),
				.narrow_data(prim_rdata),
				.narrow_sideband(prim_sb),
				.narrow_last(prim_rlast && arsplit_final),
				.start_lane(sv2v_uu_u_r_upsize_ext_start_lane_0),
				.wide_valid(int_r_valid),
				.wide_ready(int_r_ready),
				.wide_data(sv2v_tmp_u_r_upsize_wide_data),
				.wide_sideband(int_sb),
				.wide_last(int_rlast)
			);
			assign w_blen_wr_ready = 1'b1;
			assign w_blen_rd_valid = 1'b0;
			assign w_blen_rd_data = 1'sb0;
			assign w_blen_rd_lane = 1'sb0;
		end
		else begin : gen_r_upsize
			assign arsplit_pop = 1'b0;
			localparam signed [31:0] BLEN_FIFO_DEPTH = 16;
			localparam signed [31:0] BLEN_AW = 4;
			localparam signed [31:0] R_LANE_W = $clog2(WIDTH_RATIO);
			assign w_blen_wr_ready = 1'b1;
			assign w_blen_rd_valid = w_bstart;
			assign w_blen_rd_data = w_blen;
			assign w_blen_rd_lane = w_blane;
			assign w_blen_pop = (prim_rvalid && prim_rready) && prim_rlast;
			wire [S_AXI_DATA_WIDTH:1] sv2v_tmp_u_r_dnsize_narrow_data;
			always @(*) int_rdata = sv2v_tmp_u_r_dnsize_narrow_data;
			axi_data_dnsize #(
				.WIDE_WIDTH(M_AXI_DATA_WIDTH),
				.NARROW_WIDTH(S_AXI_DATA_WIDTH),
				.WIDE_SB_WIDTH(PSB_W),
				.NARROW_SB_WIDTH(PSB_W),
				.SB_BROADCAST(1),
				.TRACK_BURSTS(1),
				.BURST_LEN_WIDTH(8)
			) u_r_dnsize(
				.aclk(aclk),
				.aresetn(w_aresetn),
				.burst_len(w_blen_rd_data),
				.burst_start(w_blen_rd_valid),
				.start_lane(w_blen_rd_lane[$clog2(WIDTH_RATIO) - 1:0]),
				.wide_valid(prim_rvalid),
				.wide_ready(prim_rready),
				.wide_data(prim_rdata),
				.wide_sideband(prim_sb),
				.wide_last(prim_rlast),
				.narrow_valid(int_r_valid),
				.narrow_ready(int_r_ready),
				.narrow_data(sv2v_tmp_u_r_dnsize_narrow_data),
				.narrow_sideband(int_sb),
				.narrow_last(int_rlast)
			);
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
