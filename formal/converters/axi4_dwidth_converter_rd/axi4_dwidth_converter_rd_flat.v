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
	localparam signed [31:0] S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] WIDTH_RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH : S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
	localparam [0:0] UPSIZE = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam [0:0] DOWNSIZE = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam signed [31:0] NUM_IDS = 1 << AXI_ID_WIDTH;
	localparam signed [31:0] RASM_POOL_DEPTH = RASM_MAX_OUTSTANDING * RASM_DEPTH;
	localparam signed [31:0] RASM_PTRW = $clog2(RASM_POOL_DEPTH);
	localparam signed [31:0] RASM_CNTW = $clog2(RASM_DEPTH + 1);
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
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:157:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:159:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:161:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:163:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
		if (RASM_DEPTH < 256)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:170:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "RASM_DEPTH must cover the 256-beat AXI4 maximum");
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
	wire [S_AXI_DATA_WIDTH - 1:0] int_rdata;
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
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(AR_WIDTH)
	) ar_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
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
		.axi_aresetn(aresetn),
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
	function automatic signed [AXI_ADDR_WIDTH - 1:0] sv2v_cast_6D0DE_signed;
		input reg signed [AXI_ADDR_WIDTH - 1:0] inp;
		sv2v_cast_6D0DE_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_ar_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] MAX_BEATS = 256;
			localparam signed [31:0] CNTW = 9 + $clog2(WIDTH_RATIO);
			reg [CNTW - 1:0] r_split_remaining;
			reg [AXI_ADDR_WIDTH - 1:0] r_split_addr;
			reg r_split_active;
			wire [8:0] w_this_beats;
			wire w_this_last;
			wire w_ar_issue;
			wire w_id_free;
			function automatic signed [CNTW - 1:0] sv2v_cast_1954F_signed;
				input reg signed [CNTW - 1:0] inp;
				sv2v_cast_1954F_signed = inp;
			endfunction
			assign w_this_beats = (r_split_remaining > sv2v_cast_1954F_signed(MAX_BEATS) ? sv2v_cast_9_signed(MAX_BEATS) : sv2v_cast_9(r_split_remaining));
			assign w_this_last = r_split_remaining <= sv2v_cast_1954F_signed(MAX_BEATS);
			assign w_ar_issue = m_axi_arvalid && m_axi_arready;
			assign w_id_free = !rasm_rec_valid[int_arid];
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_split_remaining <= 1'sb0;
					r_split_addr <= 1'sb0;
					r_split_active <= 1'b0;
				end
				else if (!r_split_active) begin
					if (int_ar_valid) begin
						begin : sv2v_autoblock_1
							reg [CNTW - 1:0] sv2v_tmp_cast;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_1;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_2;
							sv2v_tmp_cast = int_arlen;
							sv2v_tmp_cast_1 = 1;
							sv2v_tmp_cast_2 = WIDTH_RATIO;
							r_split_remaining <= (sv2v_tmp_cast + sv2v_tmp_cast_1) * sv2v_tmp_cast_2;
						end
						r_split_addr <= int_araddr;
						r_split_active <= 1'b1;
					end
				end
				else if (w_ar_issue) begin
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
						if (int_arburst != 2'b00)
							r_split_addr <= r_split_addr + sv2v_cast_6D0DE_signed(MAX_BEATS * M_STRB_WIDTH);
					end
				end
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = r_split_addr;
			assign m_axi_arlen = sv2v_cast_8(w_this_beats - 9'd1);
			assign m_axi_arsize = MASTER_SIZE[2:0];
			assign m_axi_arburst = int_arburst;
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
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < NUM_IDS; i = i + 1)
						begin
							rasm_rec_final[i] <= 1'b0;
							rasm_rec_beats[i] <= 1'sb0;
						end
				end
				else if (w_ar_issue) begin
					rasm_rec_final[int_arid] <= w_this_last;
					rasm_rec_beats[int_arid] <= w_this_beats;
				end
		end
		else begin : gen_ar_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] ALIGN_BITS = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] R_LANE_W = $clog2(WIDTH_RATIO);
			assign arsplit_final = 1'b1;
			wire [7:0] master_arlen;
			wire [AXI_ADDR_WIDTH - 1:0] aligned_araddr;
			wire [R_LANE_W - 1:0] w_ar_lane;
			function automatic [R_LANE_W - 1:0] sv2v_cast_DBCFE;
				input reg [R_LANE_W - 1:0] inp;
				sv2v_cast_DBCFE = inp;
			endfunction
			assign w_ar_lane = sv2v_cast_DBCFE(int_araddr[ALIGN_BITS - 1:0] >> $clog2(S_STRB_WIDTH));
			assign master_arlen = sv2v_cast_8((((sv2v_cast_10(w_ar_lane) + sv2v_cast_10(int_arlen)) + sv2v_cast_10_signed(WIDTH_RATIO)) / sv2v_cast_10_signed(WIDTH_RATIO)) - 10'd1);
			assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH - 1:ALIGN_BITS], {ALIGN_BITS {1'b0}}};
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = aligned_araddr;
			assign m_axi_arlen = master_arlen;
			assign m_axi_arsize = MASTER_SIZE[2:0];
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
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin : sv2v_autoblock_4
					reg signed [31:0] i;
					for (i = 0; i < NUM_IDS; i = i + 1)
						begin
							rasm_rec_beats[i] <= 1'sb0;
							rasm_rec_nlen[i] <= 1'sb0;
							rasm_rec_lane[i] <= 1'sb0;
						end
				end
				else if (int_ar_valid && int_ar_ready) begin
					rasm_rec_beats[int_arid] <= sv2v_cast_9(master_arlen) + 9'd1;
					rasm_rec_nlen[int_arid] <= int_arlen;
					rasm_rec_lane[int_arid] <= w_ar_lane;
				end
		end
	endgenerate
	reg [M_AXI_DATA_WIDTH - 1:0] rasm_pool_data [0:RASM_POOL_DEPTH - 1];
	reg [1:0] rasm_pool_resp [0:RASM_POOL_DEPTH - 1];
	reg rasm_pool_last [0:RASM_POOL_DEPTH - 1];
	reg [RASM_PTRW - 1:0] rasm_pool_next [0:RASM_POOL_DEPTH - 1];
	reg [RASM_PTRW - 1:0] rasm_free_head;
	reg [RASM_PTRW:0] rasm_free_count;
	reg [RASM_PTRW - 1:0] rasm_head [0:NUM_IDS - 1];
	reg [RASM_PTRW - 1:0] rasm_tail [0:NUM_IDS - 1];
	reg [RASM_CNTW - 1:0] rasm_count [0:NUM_IDS - 1];
	reg rasm_assembled [0:NUM_IDS - 1];
	reg [AXI_USER_WIDTH - 1:0] rasm_ruser [0:NUM_IDS - 1];
	reg [AXI_ID_WIDTH - 1:0] rasm_sched_ptr;
	reg [AXI_ID_WIDTH - 1:0] rasm_feed_id;
	reg rasm_feed_active;
	reg [AXI_ID_WIDTH - 1:0] rasm_out_id;
	reg rasm_out_active;
	reg rasm_bstart_pending;
	wire w_id_has_room;
	function automatic signed [RASM_CNTW - 1:0] sv2v_cast_E42E0_signed;
		input reg signed [RASM_CNTW - 1:0] inp;
		sv2v_cast_E42E0_signed = inp;
	endfunction
	assign w_id_has_room = (rasm_count[m_axi_rid] < sv2v_cast_E42E0_signed(RASM_DEPTH)) && (rasm_free_count > {(RASM_PTRW >= 0 ? RASM_PTRW + 1 : 1 - RASM_PTRW) {1'sb0}});
	assign m_axi_rready = m_axi_rvalid && w_id_has_room;
	wire [RASM_PTRW - 1:0] w_alloc_ptr;
	wire [RASM_PTRW - 1:0] w_feed_next;
	wire w_push;
	wire w_pop;
	wire [RASM_PTRW - 1:0] w_old_free_head;
	wire [RASM_PTRW - 1:0] w_old_free_next;
	assign w_alloc_ptr = rasm_free_head;
	wire [RASM_PTRW - 1:0] w_feed_ptr;
	assign w_feed_next = rasm_pool_next[w_feed_ptr];
	assign w_push = m_axi_rvalid && m_axi_rready;
	assign w_pop = rasm_feed_active && prim_rready;
	assign w_old_free_head = rasm_free_head;
	assign w_old_free_next = rasm_pool_next[rasm_free_head];
	reg w_sched_found;
	reg [AXI_ID_WIDTH - 1:0] w_sched_pick;
	function automatic signed [((RASM_PTRW + 0) >= 0 ? RASM_PTRW + 1 : 1 - (RASM_PTRW + 0)) - 1:0] sv2v_cast_8AF0B_signed;
		input reg signed [((RASM_PTRW + 0) >= 0 ? RASM_PTRW + 1 : 1 - (RASM_PTRW + 0)) - 1:0] inp;
		sv2v_cast_8AF0B_signed = inp;
	endfunction
	function automatic signed [RASM_PTRW - 1:0] sv2v_cast_71C6F_signed;
		input reg signed [RASM_PTRW - 1:0] inp;
		sv2v_cast_71C6F_signed = inp;
	endfunction
	function automatic [RASM_CNTW - 1:0] sv2v_cast_E42E0;
		input reg [RASM_CNTW - 1:0] inp;
		sv2v_cast_E42E0 = inp;
	endfunction
	function automatic signed [AXI_ID_WIDTH - 1:0] sv2v_cast_14482_signed;
		input reg signed [AXI_ID_WIDTH - 1:0] inp;
		sv2v_cast_14482_signed = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			rasm_free_head <= 1'sb0;
			rasm_free_count <= sv2v_cast_8AF0B_signed(RASM_POOL_DEPTH);
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < RASM_POOL_DEPTH; i = i + 1)
					rasm_pool_next[i] <= sv2v_cast_71C6F_signed(i + 1);
			end
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < NUM_IDS; i = i + 1)
					rasm_rec_valid[i] <= 1'b0;
			end
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = 0; i < NUM_IDS; i = i + 1)
					begin
						rasm_head[i] <= 1'sb0;
						rasm_tail[i] <= 1'sb0;
						rasm_count[i] <= 1'sb0;
						rasm_assembled[i] <= 1'b0;
						rasm_ruser[i] <= 1'sb0;
					end
			end
			rasm_sched_ptr <= 1'sb0;
			rasm_feed_active <= 1'b0;
			rasm_feed_id <= 1'sb0;
			rasm_out_active <= 1'b0;
			rasm_out_id <= 1'sb0;
			rasm_bstart_pending <= 1'b0;
		end
		else begin
			if (w_rasm_push)
				rasm_rec_valid[w_rasm_push_id] <= 1'b1;
			if (w_push || w_pop) begin
				if (w_push && w_pop) begin
					rasm_free_head <= w_feed_ptr;
					rasm_pool_next[w_feed_ptr] <= w_old_free_next;
				end
				else if (w_push)
					rasm_free_head <= w_old_free_next;
				else begin
					rasm_free_head <= w_feed_ptr;
					rasm_pool_next[w_feed_ptr] <= w_old_free_head;
				end
				rasm_free_count <= (rasm_free_count + sv2v_cast_8AF0B_signed((w_pop ? 1 : 0))) - sv2v_cast_8AF0B_signed((w_push ? 1 : 0));
			end
			if (w_push) begin
				rasm_pool_data[w_alloc_ptr] <= m_axi_rdata;
				rasm_pool_resp[w_alloc_ptr] <= m_axi_rresp;
				rasm_pool_last[w_alloc_ptr] <= m_axi_rlast;
				rasm_pool_next[w_alloc_ptr] <= 1'sb0;
				if (rasm_count[m_axi_rid] == {RASM_CNTW {1'sb0}})
					rasm_head[m_axi_rid] <= w_alloc_ptr;
				else
					rasm_pool_next[rasm_tail[m_axi_rid]] <= w_alloc_ptr;
				rasm_tail[m_axi_rid] <= w_alloc_ptr;
				rasm_count[m_axi_rid] <= rasm_count[m_axi_rid] + sv2v_cast_E42E0_signed(1);
				if (rasm_count[m_axi_rid] == {RASM_CNTW {1'sb0}})
					rasm_ruser[m_axi_rid] <= m_axi_ruser;
			end
			if (w_push) begin
				if (rasm_rec_valid[m_axi_rid]) begin
					if (((rasm_count[m_axi_rid] + sv2v_cast_E42E0_signed(1)) == sv2v_cast_E42E0(rasm_rec_beats[m_axi_rid])) && m_axi_rlast)
						rasm_assembled[m_axi_rid] <= 1'b1;
				end
			end
			if (w_pop) begin
				rasm_count[rasm_feed_id] <= rasm_count[rasm_feed_id] - sv2v_cast_E42E0_signed(1);
				rasm_head[rasm_feed_id] <= w_feed_next;
				if (prim_rlast) begin
					rasm_assembled[rasm_feed_id] <= 1'b0;
					rasm_bstart_pending <= 1'b0;
					if (DOWNSIZE) begin
						rasm_feed_active <= 1'b0;
						rasm_rec_valid[rasm_feed_id] <= 1'b0;
					end
				end
			end
			if (!rasm_out_active && rasm_feed_active) begin
				rasm_out_active <= 1'b1;
				rasm_out_id <= rasm_feed_id;
			end
			if ((int_r_valid && int_r_ready) && int_rlast)
				rasm_out_active <= 1'b0;
			if (((!DOWNSIZE && int_r_valid) && int_r_ready) && int_rlast) begin
				rasm_feed_active <= 1'b0;
				rasm_rec_valid[rasm_feed_id] <= 1'b0;
			end
			if ((rasm_feed_active && prim_rready) && rasm_bstart_pending)
				rasm_bstart_pending <= 1'b0;
			if (!rasm_feed_active && w_sched_found) begin
				if ((!DOWNSIZE || !rasm_out_active) || (w_sched_pick == rasm_out_id)) begin
					rasm_feed_active <= 1'b1;
					rasm_feed_id <= w_sched_pick;
					rasm_sched_ptr <= w_sched_pick + sv2v_cast_14482_signed(1);
					rasm_bstart_pending <= !DOWNSIZE;
				end
			end
		end
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_sched_found = 1'b0;
		w_sched_pick = rasm_sched_ptr;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < NUM_IDS; i = i + 1)
				begin : sv2v_autoblock_9
					reg signed [31:0] raw_idx;
					reg signed [31:0] idx;
					raw_idx = sv2v_cast_32_signed(rasm_sched_ptr) + i;
					idx = raw_idx % NUM_IDS;
					if (!w_sched_found && rasm_assembled[idx]) begin
						w_sched_found = 1'b1;
						w_sched_pick = sv2v_cast_14482_signed(idx);
					end
				end
		end
	end
	assign w_feed_ptr = rasm_head[rasm_feed_id];
	assign prim_rvalid = rasm_feed_active;
	assign prim_rdata = rasm_pool_data[w_feed_ptr];
	assign prim_rresp = rasm_pool_resp[w_feed_ptr];
	assign prim_rlast = rasm_pool_last[w_feed_ptr];
	assign prim_rid = rasm_feed_id;
	assign prim_ruser = rasm_ruser[rasm_feed_id];
	assign int_rid = rasm_out_id;
	assign int_ruser = rasm_ruser[rasm_out_id];
	generate
		if (DOWNSIZE) begin : gen_r_downsize
			assign arsplit_final = rasm_rec_final[rasm_feed_id];
			assign arsplit_pop = ((rasm_feed_active && prim_rready) && prim_rlast) && rasm_rec_final[rasm_feed_id];
			localparam signed [31:0] sv2v_uu_u_r_upsize_NARROW_WIDTH = M_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_WIDE_WIDTH = S_AXI_DATA_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_WIDTH_RATIO = sv2v_uu_u_r_upsize_WIDE_WIDTH / sv2v_uu_u_r_upsize_NARROW_WIDTH;
			localparam signed [31:0] sv2v_uu_u_r_upsize_PTR_WIDTH = $clog2(sv2v_uu_u_r_upsize_WIDTH_RATIO);
			localparam [sv2v_uu_u_r_upsize_PTR_WIDTH - 1:0] sv2v_uu_u_r_upsize_ext_start_lane_0 = 1'sb0;
			axi_data_upsize #(
				.NARROW_WIDTH(M_AXI_DATA_WIDTH),
				.WIDE_WIDTH(S_AXI_DATA_WIDTH),
				.NARROW_SB_WIDTH(2),
				.WIDE_SB_WIDTH(2),
				.SB_OR_MODE(1)
			) u_r_upsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.narrow_valid(prim_rvalid),
				.narrow_ready(prim_rready),
				.narrow_data(prim_rdata),
				.narrow_sideband(prim_rresp),
				.narrow_last(prim_rlast && arsplit_final),
				.start_lane(sv2v_uu_u_r_upsize_ext_start_lane_0),
				.wide_valid(int_r_valid),
				.wide_ready(int_r_ready),
				.wide_data(int_rdata),
				.wide_sideband(int_rresp),
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
			assign w_blen_rd_valid = rasm_bstart_pending;
			assign w_blen_rd_data = rasm_rec_nlen[rasm_feed_id];
			assign w_blen_rd_lane = sv2v_cast_8(rasm_rec_lane[rasm_feed_id]);
			assign w_blen_pop = (rasm_feed_active && prim_rready) && prim_rlast;
			axi_data_dnsize #(
				.WIDE_WIDTH(M_AXI_DATA_WIDTH),
				.NARROW_WIDTH(S_AXI_DATA_WIDTH),
				.WIDE_SB_WIDTH(2),
				.NARROW_SB_WIDTH(2),
				.SB_BROADCAST(1),
				.TRACK_BURSTS(1),
				.BURST_LEN_WIDTH(8)
			) u_r_dnsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.burst_len(w_blen_rd_data),
				.burst_start(w_blen_rd_valid),
				.start_lane(w_blen_rd_lane[$clog2(WIDTH_RATIO) - 1:0]),
				.wide_valid(prim_rvalid),
				.wide_ready(prim_rready),
				.wide_data(prim_rdata),
				.wide_sideband(prim_rresp),
				.wide_last(prim_rlast),
				.narrow_valid(int_r_valid),
				.narrow_ready(int_r_ready),
				.narrow_data(int_rdata),
				.narrow_sideband(int_rresp),
				.narrow_last(int_rlast)
			);
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
