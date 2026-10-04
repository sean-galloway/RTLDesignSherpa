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
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/amba/gaxi/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_1;
	generate
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
	endgenerate
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
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
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
module axi4_dwidth_converter_wr (
	aclk,
	aresetn,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
	m_axi_awid,
	m_axi_awaddr,
	m_axi_awlen,
	m_axi_awsize,
	m_axi_awburst,
	m_axi_awlock,
	m_axi_awcache,
	m_axi_awprot,
	m_axi_awqos,
	m_axi_awregion,
	m_axi_awuser,
	m_axi_awvalid,
	m_axi_awready,
	m_axi_wdata,
	m_axi_wstrb,
	m_axi_wlast,
	m_axi_wuser,
	m_axi_wvalid,
	m_axi_wready,
	m_axi_bid,
	m_axi_bresp,
	m_axi_buser,
	m_axi_bvalid,
	m_axi_bready
);
	reg _sv2v_0;
	parameter signed [31:0] S_AXI_DATA_WIDTH = 32;
	parameter signed [31:0] M_AXI_DATA_WIDTH = 128;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	localparam signed [31:0] S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] WIDTH_RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH : S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
	localparam [0:0] UPSIZE = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam [0:0] DOWNSIZE = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam signed [31:0] AW_WIDTH = ((AXI_ID_WIDTH + AXI_ADDR_WIDTH) + 29) + AXI_USER_WIDTH;
	localparam signed [31:0] W_WIDTH = ((S_AXI_DATA_WIDTH + S_STRB_WIDTH) + 1) + AXI_USER_WIDTH;
	localparam signed [31:0] B_WIDTH = (AXI_ID_WIDTH + 2) + AXI_USER_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_awid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [S_AXI_DATA_WIDTH - 1:0] s_axi_wdata;
	input wire [S_STRB_WIDTH - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
	output wire [AXI_ID_WIDTH - 1:0] m_axi_awid;
	output wire [AXI_ADDR_WIDTH - 1:0] m_axi_awaddr;
	output wire [7:0] m_axi_awlen;
	output wire [2:0] m_axi_awsize;
	output wire [1:0] m_axi_awburst;
	output wire m_axi_awlock;
	output wire [3:0] m_axi_awcache;
	output wire [2:0] m_axi_awprot;
	output wire [3:0] m_axi_awqos;
	output wire [3:0] m_axi_awregion;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_awuser;
	output wire m_axi_awvalid;
	input wire m_axi_awready;
	output wire [M_AXI_DATA_WIDTH - 1:0] m_axi_wdata;
	output wire [M_STRB_WIDTH - 1:0] m_axi_wstrb;
	output wire m_axi_wlast;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_wuser;
	output wire m_axi_wvalid;
	input wire m_axi_wready;
	input wire [AXI_ID_WIDTH - 1:0] m_axi_bid;
	input wire [1:0] m_axi_bresp;
	input wire [AXI_USER_WIDTH - 1:0] m_axi_buser;
	input wire m_axi_bvalid;
	output wire m_axi_bready;
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:143:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:145:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:147:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:149:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
	end
	wire [AW_WIDTH - 1:0] int_aw_data;
	wire int_aw_valid;
	wire int_aw_ready;
	wire [AXI_ID_WIDTH - 1:0] int_awid;
	wire [AXI_ADDR_WIDTH - 1:0] int_awaddr;
	wire [7:0] int_awlen;
	wire [2:0] int_awsize;
	wire [1:0] int_awburst;
	wire int_awlock;
	wire [3:0] int_awcache;
	wire [2:0] int_awprot;
	wire [3:0] int_awqos;
	wire [3:0] int_awregion;
	wire [AXI_USER_WIDTH - 1:0] int_awuser;
	wire [W_WIDTH - 1:0] int_w_data;
	wire int_w_valid;
	wire int_w_ready;
	wire [S_AXI_DATA_WIDTH - 1:0] int_wdata;
	wire [S_STRB_WIDTH - 1:0] int_wstrb;
	wire int_wlast;
	wire [AXI_USER_WIDTH - 1:0] int_wuser;
	wire [B_WIDTH - 1:0] int_b_data;
	wire int_b_valid;
	wire w_aw_issue;
	wire w_this_last;
	wire w_b_cam_slot_free;
	localparam signed [31:0] SPLITQ_DEPTH = 16;
	wire split_w_avail;
	wire [8:0] split_w_beats;
	wire split_w_pop;
	wire [7:0] w_upsize_start_lane;
	wire w_upsize_w_gate;
	wire int_b_ready;
	wire [AXI_ID_WIDTH - 1:0] int_bid;
	wire [1:0] int_bresp;
	wire [AXI_USER_WIDTH - 1:0] int_buser;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AW_WIDTH)
	) aw_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_awvalid),
		.wr_ready(s_axi_awready),
		.wr_data({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awregion, s_axi_awuser}),
		.rd_valid(int_aw_valid),
		.rd_ready(int_aw_ready),
		.rd_data(int_aw_data),
		.count(),
		.rd_count()
	);
	assign {int_awid, int_awaddr, int_awlen, int_awsize, int_awburst, int_awlock, int_awcache, int_awprot, int_awqos, int_awregion, int_awuser} = int_aw_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(W_WIDTH)
	) w_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_wvalid),
		.wr_ready(s_axi_wready),
		.wr_data({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
		.rd_valid(int_w_valid),
		.rd_ready(int_w_ready),
		.rd_data(int_w_data),
		.count(),
		.rd_count()
	);
	assign {int_wdata, int_wstrb, int_wlast, int_wuser} = int_w_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(B_WIDTH)
	) b_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(int_b_valid),
		.wr_ready(int_b_ready),
		.wr_data(int_b_data),
		.rd_valid(s_axi_bvalid),
		.rd_ready(s_axi_bready),
		.rd_data({s_axi_bid, s_axi_bresp, s_axi_buser}),
		.count(),
		.rd_count()
	);
	assign int_b_data = {int_bid, int_bresp, int_buser};
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [9:0] sv2v_cast_10;
		input reg [9:0] inp;
		sv2v_cast_10 = inp;
	endfunction
	function automatic signed [9:0] sv2v_cast_10_signed;
		input reg signed [9:0] inp;
		sv2v_cast_10_signed = inp;
	endfunction
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic signed [AXI_ADDR_WIDTH - 1:0] sv2v_cast_6D0DE_signed;
		input reg signed [AXI_ADDR_WIDTH - 1:0] inp;
		sv2v_cast_6D0DE_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_aw_downsize
			assign w_upsize_start_lane = 8'd0;
			assign w_upsize_w_gate = 1'b1;
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] MAX_BEATS = 256;
			localparam signed [31:0] CNTW = 9 + $clog2(WIDTH_RATIO);
			localparam signed [31:0] SPLITQ_AW = 4;
			reg [CNTW - 1:0] r_split_remaining;
			reg [AXI_ADDR_WIDTH - 1:0] r_split_addr;
			reg r_split_active;
			wire [8:0] w_this_beats;
			function automatic signed [CNTW - 1:0] sv2v_cast_1954F_signed;
				input reg signed [CNTW - 1:0] inp;
				sv2v_cast_1954F_signed = inp;
			endfunction
			assign w_this_beats = (r_split_remaining > sv2v_cast_1954F_signed(MAX_BEATS) ? sv2v_cast_9_signed(MAX_BEATS) : sv2v_cast_9(r_split_remaining));
			assign w_this_last = r_split_remaining <= sv2v_cast_1954F_signed(MAX_BEATS);
			assign w_aw_issue = m_axi_awvalid && m_axi_awready;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_split_remaining <= 1'sb0;
					r_split_addr <= 1'sb0;
					r_split_active <= 1'b0;
				end
				else if (!r_split_active) begin
					if (int_aw_valid) begin
						begin : sv2v_autoblock_1
							reg [CNTW - 1:0] sv2v_tmp_cast;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_1;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_2;
							sv2v_tmp_cast = int_awlen;
							sv2v_tmp_cast_1 = 1;
							sv2v_tmp_cast_2 = WIDTH_RATIO;
							r_split_remaining <= (sv2v_tmp_cast + sv2v_tmp_cast_1) * sv2v_tmp_cast_2;
						end
						r_split_addr <= int_awaddr;
						r_split_active <= 1'b1;
					end
				end
				else if (w_aw_issue) begin
					if (w_this_last) begin
						r_split_remaining <= 1'sb0;
						r_split_active <= 1'b0;
					end
					else begin
						begin : sv2v_autoblock_2
							reg signed [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = MAX_BEATS;
							r_split_remaining <= r_split_remaining - sv2v_tmp_cast;
						end
						if (int_awburst != 2'b00)
							r_split_addr <= r_split_addr + sv2v_cast_6D0DE_signed(MAX_BEATS * M_STRB_WIDTH);
					end
				end
			reg [9:0] splitq_mem [0:15];
			reg [SPLITQ_AW:0] splitq_wptr;
			reg [SPLITQ_AW:0] splitq_rptr_w;
			wire w_splitq_full;
			assign w_splitq_full = (splitq_wptr[3:0] == splitq_rptr_w[3:0]) && (splitq_wptr[SPLITQ_AW] != splitq_rptr_w[SPLITQ_AW]);
			assign split_w_avail = splitq_wptr != splitq_rptr_w;
			assign split_w_beats = splitq_mem[splitq_rptr_w[3:0]][8:0];
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					splitq_wptr <= 1'sb0;
					splitq_rptr_w <= 1'sb0;
				end
				else begin
					if (w_aw_issue) begin
						splitq_mem[splitq_wptr[3:0]] <= {w_this_last, w_this_beats};
						splitq_wptr <= splitq_wptr + 1'b1;
					end
					if (split_w_pop)
						splitq_rptr_w <= splitq_rptr_w + 1'b1;
				end
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = r_split_addr;
			assign m_axi_awlen = sv2v_cast_8(w_this_beats - 9'd1);
			assign m_axi_awsize = MASTER_SIZE[2:0];
			assign m_axi_awburst = int_awburst;
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = (r_split_active && !w_splitq_full) && (!w_this_last || w_b_cam_slot_free);
			assign int_aw_ready = w_aw_issue && w_this_last;
		end
		else begin : gen_aw_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] LANE_W = $clog2(WIDTH_RATIO);
			assign split_w_avail = 1'b0;
			assign split_w_beats = 9'd0;
			wire [LANE_W - 1:0] w_aw_lane;
			function automatic [LANE_W - 1:0] sv2v_cast_3FA0D;
				input reg [LANE_W - 1:0] inp;
				sv2v_cast_3FA0D = inp;
			endfunction
			assign w_aw_lane = sv2v_cast_3FA0D(int_awaddr[$clog2(M_STRB_WIDTH) - 1:0] >> $clog2(S_STRB_WIDTH));
			localparam signed [31:0] WLANE_DEPTH = 16;
			localparam signed [31:0] WLANE_AW = 4;
			reg [LANE_W - 1:0] wlane_mem [0:15];
			reg [WLANE_AW:0] wlane_wptr;
			reg [WLANE_AW:0] wlane_rptr;
			wire w_wlane_full;
			wire w_wlane_avail;
			assign w_wlane_full = (wlane_wptr[WLANE_AW] != wlane_rptr[WLANE_AW]) && (wlane_wptr[3:0] == wlane_rptr[3:0]);
			assign w_wlane_avail = wlane_wptr != wlane_rptr;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					wlane_wptr <= 1'sb0;
					wlane_rptr <= 1'sb0;
				end
				else begin
					if (int_aw_valid && int_aw_ready) begin
						wlane_mem[wlane_wptr[3:0]] <= w_aw_lane;
						wlane_wptr <= wlane_wptr + 1'b1;
					end
					if ((int_w_valid && int_w_ready) && int_wlast)
						wlane_rptr <= wlane_rptr + 1'b1;
				end
			assign w_upsize_start_lane = sv2v_cast_8(wlane_mem[wlane_rptr[3:0]]);
			assign w_upsize_w_gate = w_wlane_avail;
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = int_awaddr;
			assign m_axi_awlen = sv2v_cast_8((((sv2v_cast_10(w_aw_lane) + sv2v_cast_10(int_awlen)) + sv2v_cast_10_signed(WIDTH_RATIO)) / sv2v_cast_10_signed(WIDTH_RATIO)) - 10'd1);
			assign m_axi_awsize = MASTER_SIZE[2:0];
			assign m_axi_awburst = int_awburst;
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = int_aw_valid && !w_wlane_full;
			assign int_aw_ready = m_axi_awready && !w_wlane_full;
		end
	endgenerate
	reg [AXI_USER_WIDTH - 1:0] r_wuser_held;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_wuser_held <= 1'sb0;
		else if (int_w_valid && int_w_ready)
			r_wuser_held <= int_wuser;
	assign m_axi_wuser = r_wuser_held;
	generate
		if (DOWNSIZE) begin : gen_w_downsize
			wire w_dnsize_valid;
			wire w_dnsize_ready;
			localparam signed [31:0] sv2v_uu_u_w_dnsize_NARROW_WIDTH = M_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_w_dnsize_WIDE_WIDTH = S_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_w_dnsize_WIDTH_RATIO = sv2v_uu_u_w_dnsize_WIDE_WIDTH / sv2v_uu_u_w_dnsize_NARROW_WIDTH;
			localparam signed [31:0] sv2v_uu_u_w_dnsize_PTR_WIDTH = $clog2(sv2v_uu_u_w_dnsize_WIDTH_RATIO);
			localparam [sv2v_uu_u_w_dnsize_PTR_WIDTH - 1:0] sv2v_uu_u_w_dnsize_ext_start_lane_0 = 1'sb0;
			axi_data_dnsize #(
				.WIDE_WIDTH(S_AXI_DATA_WIDTH),
				.NARROW_WIDTH(M_AXI_DATA_WIDTH),
				.WIDE_SB_WIDTH(S_STRB_WIDTH),
				.NARROW_SB_WIDTH(M_STRB_WIDTH),
				.SB_BROADCAST(0),
				.TRACK_BURSTS(0),
				.BURST_LEN_WIDTH(8)
			) u_w_dnsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.burst_len(8'd0),
				.burst_start(1'b0),
				.start_lane(sv2v_uu_u_w_dnsize_ext_start_lane_0),
				.wide_valid(int_w_valid),
				.wide_ready(int_w_ready),
				.wide_data(int_wdata),
				.wide_sideband(int_wstrb),
				.wide_last(int_wlast),
				.narrow_valid(w_dnsize_valid),
				.narrow_ready(w_dnsize_ready),
				.narrow_data(m_axi_wdata),
				.narrow_sideband(m_axi_wstrb),
				.narrow_last()
			);
			reg [8:0] r_w_beats_left;
			assign split_w_pop = (r_w_beats_left == 9'd0) && split_w_avail;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn)
					r_w_beats_left <= 9'd0;
				else if (r_w_beats_left == 9'd0) begin
					if (split_w_avail)
						r_w_beats_left <= split_w_beats;
				end
				else if (m_axi_wvalid && m_axi_wready)
					r_w_beats_left <= r_w_beats_left - 9'd1;
			assign m_axi_wvalid = w_dnsize_valid && (r_w_beats_left != 9'd0);
			assign w_dnsize_ready = m_axi_wready && (r_w_beats_left != 9'd0);
			assign m_axi_wlast = r_w_beats_left == 9'd1;
		end
		else begin : gen_w_upsize
			assign split_w_pop = 1'b0;
			wire w_upz_nready;
			assign int_w_ready = w_upz_nready && w_upsize_w_gate;
			axi_data_upsize #(
				.NARROW_WIDTH(S_AXI_DATA_WIDTH),
				.WIDE_WIDTH(M_AXI_DATA_WIDTH),
				.NARROW_SB_WIDTH(S_STRB_WIDTH),
				.WIDE_SB_WIDTH(M_STRB_WIDTH),
				.SB_OR_MODE(0)
			) u_w_upsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.narrow_valid(int_w_valid && w_upsize_w_gate),
				.narrow_ready(w_upz_nready),
				.narrow_data(int_wdata),
				.narrow_sideband(int_wstrb),
				.narrow_last(int_wlast),
				.start_lane(w_upsize_start_lane[$clog2(WIDTH_RATIO) - 1:0]),
				.wide_valid(m_axi_wvalid),
				.wide_ready(m_axi_wready),
				.wide_data(m_axi_wdata),
				.wide_sideband(m_axi_wstrb),
				.wide_last(m_axi_wlast)
			);
		end
		if (DOWNSIZE) begin : gen_b_fold
			localparam signed [31:0] B_CAM_DEPTH = SPLITQ_DEPTH;
			localparam signed [31:0] B_CAM_AW = 4;
			reg [AXI_ID_WIDTH + 14:0] b_cam [0:15];
			reg [15:0] b_cam_valid;
			reg [B_CAM_AW:0] r_b_cam_next_age;
			reg r_b_open_valid;
			reg [AXI_ID_WIDTH - 1:0] r_b_open_id;
			reg [7:0] r_b_open_count;
			wire [7:0] w_b_cam_push_count;
			assign w_b_cam_push_count = (r_b_open_valid ? r_b_open_count + 8'd1 : 8'd1);
			reg [3:0] w_b_cam_free_idx;
			reg w_b_cam_free_found;
			always @(*) begin
				if (_sv2v_0)
					;
				w_b_cam_free_found = 1'b0;
				w_b_cam_free_idx = 1'sb0;
				begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < B_CAM_DEPTH; i = i + 1)
						if (!b_cam_valid[i] && !w_b_cam_free_found) begin
							w_b_cam_free_found = 1'b1;
							begin : sv2v_autoblock_4
								reg signed [3:0] sv2v_tmp_cast;
								sv2v_tmp_cast = i;
								w_b_cam_free_idx = sv2v_tmp_cast;
							end
						end
				end
			end
			assign w_b_cam_slot_free = w_b_cam_free_found;
			reg [3:0] w_b_cam_idx;
			reg w_b_cam_match;
			reg [B_CAM_AW:0] w_b_cam_best_age;
			always @(*) begin
				if (_sv2v_0)
					;
				w_b_cam_match = 1'b0;
				w_b_cam_idx = 1'sb0;
				w_b_cam_best_age = 1'sb1;
				begin : sv2v_autoblock_5
					reg signed [31:0] i;
					for (i = 0; i < B_CAM_DEPTH; i = i + 1)
						if ((b_cam_valid[i] && (b_cam[i][AXI_ID_WIDTH + 14-:((AXI_ID_WIDTH + 14) >= 15 ? AXI_ID_WIDTH : 16 - (AXI_ID_WIDTH + 14))] == m_axi_bid)) && (b_cam[i][4-:5] < w_b_cam_best_age)) begin
							w_b_cam_best_age = b_cam[i][4-:5];
							begin : sv2v_autoblock_6
								reg signed [3:0] sv2v_tmp_cast;
								sv2v_tmp_cast = i;
								w_b_cam_idx = sv2v_tmp_cast;
							end
							w_b_cam_match = 1'b1;
						end
				end
			end
			assign int_bid = m_axi_bid;
			assign int_buser = m_axi_buser;
			assign int_b_valid = (m_axi_bvalid && w_b_cam_match) && (b_cam[w_b_cam_idx][14-:8] == 8'd1);
			assign int_bresp = (m_axi_bresp > b_cam[w_b_cam_idx][6-:2] ? m_axi_bresp : b_cam[w_b_cam_idx][6-:2]);
			assign m_axi_bready = ((m_axi_bvalid && w_b_cam_match) && (b_cam[w_b_cam_idx][14-:8] == 8'd1) ? int_b_ready : 1'b1);
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_b_open_valid <= 1'b0;
					r_b_open_id <= 1'sb0;
					r_b_open_count <= 1'sb0;
					r_b_cam_next_age <= 1'sb0;
					begin : sv2v_autoblock_7
						reg signed [31:0] i;
						for (i = 0; i < B_CAM_DEPTH; i = i + 1)
							begin
								b_cam_valid[i] <= 1'b0;
								b_cam[i] <= 1'sb0;
							end
					end
				end
				else begin
					if (w_aw_issue) begin
						if (!r_b_open_valid) begin
							r_b_open_valid <= 1'b1;
							r_b_open_id <= int_awid;
							r_b_open_count <= 8'd1;
						end
						else
							r_b_open_count <= r_b_open_count + 8'd1;
					end
					if (int_aw_valid && int_aw_ready)
						r_b_open_valid <= 1'b0;
					if (w_aw_issue && w_this_last) begin
						if (w_b_cam_free_found) begin
							b_cam_valid[w_b_cam_free_idx] <= 1'b1;
							b_cam[w_b_cam_free_idx][AXI_ID_WIDTH + 14-:((AXI_ID_WIDTH + 14) >= 15 ? AXI_ID_WIDTH : 16 - (AXI_ID_WIDTH + 14))] <= int_awid;
							b_cam[w_b_cam_free_idx][14-:8] <= w_b_cam_push_count;
							b_cam[w_b_cam_free_idx][6-:2] <= 2'b00;
							b_cam[w_b_cam_free_idx][4-:5] <= r_b_cam_next_age;
							r_b_cam_next_age <= r_b_cam_next_age + 1'b1;
						end
					end
					if ((m_axi_bvalid && m_axi_bready) && w_b_cam_match) begin
						if (b_cam[w_b_cam_idx][14-:8] == 8'd1)
							b_cam_valid[w_b_cam_idx] <= 1'b0;
						else begin
							b_cam[w_b_cam_idx][14-:8] <= b_cam[w_b_cam_idx][14-:8] - 8'd1;
							if (m_axi_bresp > b_cam[w_b_cam_idx][6-:2])
								b_cam[w_b_cam_idx][6-:2] <= m_axi_bresp;
						end
					end
				end
		end
		else begin : gen_b_pass
			assign w_b_cam_slot_free = 1'b1;
			assign int_bid = m_axi_bid;
			assign int_bresp = m_axi_bresp;
			assign int_buser = m_axi_buser;
			assign int_b_valid = m_axi_bvalid;
			assign m_axi_bready = int_b_ready;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
