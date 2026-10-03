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
module ctrlrd_engine (
	clk,
	rst_n,
	ctrlrd_valid,
	ctrlrd_ready,
	ctrlrd_pkt_addr,
	ctrlrd_pkt_data,
	ctrlrd_pkt_mask,
	ctrlrd_error,
	ctrlrd_result,
	cfg_ctrlrd_max_try,
	cfg_channel_reset,
	tick_1us,
	ctrlrd_engine_idle,
	ar_valid,
	ar_ready,
	ar_addr,
	ar_len,
	ar_size,
	ar_burst,
	ar_id,
	ar_lock,
	ar_cache,
	ar_prot,
	ar_qos,
	ar_region,
	r_valid,
	r_ready,
	r_data,
	r_id,
	r_resp,
	r_last,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 32;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] AXI_DATA_WIDTH = 64;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter [15:0] MON_AGENT_ID = 16'h0030;
	parameter [7:0] MON_UNIT_ID = 8'h02;
	parameter [8:0] MON_CHANNEL_ID = 9'h000;
	input wire clk;
	input wire rst_n;
	input wire ctrlrd_valid;
	output wire ctrlrd_ready;
	input wire [ADDR_WIDTH - 1:0] ctrlrd_pkt_addr;
	input wire [31:0] ctrlrd_pkt_data;
	input wire [31:0] ctrlrd_pkt_mask;
	output wire ctrlrd_error;
	output wire [31:0] ctrlrd_result;
	input wire [8:0] cfg_ctrlrd_max_try;
	input wire cfg_channel_reset;
	input wire tick_1us;
	output wire ctrlrd_engine_idle;
	output wire ar_valid;
	input wire ar_ready;
	output wire [ADDR_WIDTH - 1:0] ar_addr;
	output wire [7:0] ar_len;
	output wire [2:0] ar_size;
	output wire [1:0] ar_burst;
	output wire [AXI_ID_WIDTH - 1:0] ar_id;
	output wire ar_lock;
	output wire [3:0] ar_cache;
	output wire [2:0] ar_prot;
	output wire [3:0] ar_qos;
	output wire [3:0] ar_region;
	input wire r_valid;
	output wire r_ready;
	input wire [AXI_DATA_WIDTH - 1:0] r_data;
	input wire [AXI_ID_WIDTH - 1:0] r_id;
	input wire [1:0] r_resp;
	input wire r_last;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	initial begin
		if (AXI_ID_WIDTH < CHAN_WIDTH) begin
			$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dma-ip/rapids/rtl/fub/ctrlrd_engine.sv:93:13 - ctrlrd_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
			$finish(1);
		end
		if (AXI_DATA_WIDTH < 32) begin
			$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dma-ip/rapids/rtl/fub/ctrlrd_engine.sv:96:13 - ctrlrd_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_DATA_WIDTH (%0d) must be >= 32 for 32-bit reads", AXI_DATA_WIDTH);
			$finish(1);
		end
	end
	reg [2:0] r_current_state;
	reg [2:0] w_next_state;
	reg r_channel_reset_active;
	wire w_safe_to_reset;
	wire w_fifo_empty;
	wire w_no_active_transaction;
	reg r_drain_ar;
	reg r_drain_pending;
	wire w_draining;
	reg [ADDR_WIDTH - 1:0] r_ctrlrd_addr;
	reg [31:0] r_expected_data;
	reg [31:0] r_mask;
	reg [31:0] r_axi_read_data;
	localparam signed [31:0] AXI_WORDS = AXI_DATA_WIDTH / 32;
	localparam signed [31:0] WORD_SEL_W = (AXI_WORDS > 1 ? $clog2(AXI_WORDS) : 1);
	wire [WORD_SEL_W - 1:0] w_rd_word_sel;
	wire [31:0] w_rd_word;
	assign w_rd_word_sel = (AXI_WORDS > 1 ? r_ctrlrd_addr[WORD_SEL_W + 1:2] : {WORD_SEL_W {1'sb0}});
	assign w_rd_word = r_data[32 * w_rd_word_sel+:32];
	reg [8:0] r_retry_counter;
	reg r_retry_wait_complete;
	reg r_addr_issued;
	reg [1:0] r_read_resp;
	reg [AXI_ID_WIDTH - 1:0] r_expected_axi_id;
	reg r_ctrlrd_error;
	wire w_null_address;
	wire w_axi_response_error;
	wire w_transaction_complete;
	wire w_our_axi_response;
	wire [31:0] w_masked_expected;
	wire [31:0] w_masked_actual;
	wire w_data_match;
	wire w_retries_remaining;
	wire w_ctrlrd_req_skid_valid_in;
	wire w_ctrlrd_req_skid_ready_in;
	wire w_ctrlrd_req_skid_valid_out;
	wire w_ctrlrd_req_skid_ready_out;
	wire [ADDR_WIDTH + 63:0] w_ctrlrd_req_skid_din;
	wire [ADDR_WIDTH + 63:0] w_ctrlrd_req_skid_dout;
	reg r_mon_valid;
	reg [127:0] r_mon_packet;
	reg [63:0] r_mon_timestamp;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	assign w_draining = r_drain_ar || r_drain_pending;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_drain_ar <= 1'b0;
			r_drain_pending <= 1'b0;
		end
		else if (r_drain_ar) begin
			if (ar_ready) begin
				r_drain_ar <= 1'b0;
				r_drain_pending <= 1'b1;
			end
		end
		else if (r_drain_pending) begin
			if (r_valid && r_ready)
				r_drain_pending <= 1'b0;
		end
		else if (r_channel_reset_active) begin
			if (ar_valid && !ar_ready)
				r_drain_ar <= 1'b1;
			else if ((r_addr_issued || (ar_valid && ar_ready)) && !(r_valid && r_ready))
				r_drain_pending <= 1'b1;
		end
	assign w_fifo_empty = !w_ctrlrd_req_skid_valid_out;
	assign w_no_active_transaction = !r_addr_issued;
	assign w_safe_to_reset = (w_fifo_empty && w_no_active_transaction) && (r_current_state == 3'b000);
	assign ctrlrd_engine_idle = (((r_current_state == 3'b000) && !r_channel_reset_active) && w_fifo_empty) && !w_draining;
	assign w_ctrlrd_req_skid_valid_in = ctrlrd_valid && !r_channel_reset_active;
	assign ctrlrd_ready = w_ctrlrd_req_skid_ready_in && !r_channel_reset_active;
	assign w_ctrlrd_req_skid_din = {ctrlrd_pkt_addr, ctrlrd_pkt_data, ctrlrd_pkt_mask};
	gaxi_skid_buffer #(
		.DATA_WIDTH(ADDR_WIDTH + 64),
		.DEPTH(2)
	) i_ctrlrd_req_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_ctrlrd_req_skid_valid_in),
		.wr_ready(w_ctrlrd_req_skid_ready_in),
		.wr_data(w_ctrlrd_req_skid_din),
		.rd_valid(w_ctrlrd_req_skid_valid_out),
		.rd_ready(w_ctrlrd_req_skid_ready_out),
		.rd_data(w_ctrlrd_req_skid_dout),
		.count(),
		.rd_count()
	);
	assign w_ctrlrd_req_skid_ready_out = (((r_current_state == 3'b000) && w_ctrlrd_req_skid_valid_out) && !r_channel_reset_active) && !w_draining;
	assign w_null_address = r_ctrlrd_addr == 64'h0000000000000000;
	assign w_axi_response_error = r_read_resp != 2'b00;
	assign w_transaction_complete = w_our_axi_response && r_valid;
	assign w_retries_remaining = r_retry_counter > 0;
	assign w_masked_expected = r_expected_data & r_mask;
	assign w_masked_actual = r_axi_read_data[31:0] & r_mask;
	assign w_data_match = w_masked_expected == w_masked_actual;
	assign w_our_axi_response = r_valid && (r_id == r_expected_axi_id);
	assign r_ready = ((r_current_state == 3'b010) || r_drain_pending) && w_our_axi_response;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_current_state <= 3'b000;
		else
			r_current_state <= w_next_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		case (r_current_state)
			3'b000:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_ctrlrd_req_skid_valid_out && w_ctrlrd_req_skid_ready_out)
					w_next_state = 3'b001;
			3'b001:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_null_address)
					w_next_state = 3'b101;
				else if (r_addr_issued)
					w_next_state = 3'b010;
			3'b010:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_transaction_complete)
					w_next_state = 3'b011;
			3'b011:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_axi_response_error)
					w_next_state = 3'b110;
				else if (w_data_match)
					w_next_state = 3'b101;
				else if (w_retries_remaining)
					w_next_state = 3'b100;
				else
					w_next_state = 3'b110;
			3'b100:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (r_retry_wait_complete)
					w_next_state = 3'b001;
			3'b101: w_next_state = 3'b000;
			3'b110: w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_ctrlrd_addr <= 64'h0000000000000000;
			r_expected_data <= 32'h00000000;
			r_mask <= 32'h00000000;
			r_axi_read_data <= 32'h00000000;
			r_retry_counter <= 9'h000;
			r_retry_wait_complete <= 1'b0;
			r_addr_issued <= 1'b0;
			r_read_resp <= 2'b00;
			r_expected_axi_id <= 1'sb0;
			r_ctrlrd_error <= 1'b0;
		end
		else begin
			case (r_current_state)
				3'b000: begin
					if (w_ctrlrd_req_skid_valid_out && w_ctrlrd_req_skid_ready_out) begin
						{r_ctrlrd_addr, r_expected_data, r_mask} <= w_ctrlrd_req_skid_dout;
						r_expected_axi_id <= {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, CHANNEL_ID[CHAN_WIDTH - 1:0]};
						r_retry_counter <= cfg_ctrlrd_max_try;
					end
					r_addr_issued <= 1'b0;
					r_read_resp <= 2'b00;
					r_retry_wait_complete <= 1'b0;
				end
				3'b001:
					if (!w_null_address && ar_ready)
						r_addr_issued <= 1'b1;
				3'b010:
					if (w_transaction_complete) begin
						r_axi_read_data <= w_rd_word;
						r_read_resp <= r_resp;
						r_addr_issued <= 1'b0;
					end
				3'b011:
					if ((!w_data_match && w_retries_remaining) && !w_axi_response_error)
						r_retry_counter <= r_retry_counter - 1;
				3'b100:
					if (tick_1us)
						r_retry_wait_complete <= 1'b1;
				3'b101: r_ctrlrd_error <= 1'b0;
				3'b110: r_ctrlrd_error <= 1'b1;
				default:
					;
			endcase
			if (r_channel_reset_active) begin
				r_addr_issued <= 1'b0;
				r_read_resp <= 2'b00;
				r_retry_counter <= 9'h000;
				r_retry_wait_complete <= 1'b0;
				r_ctrlrd_error <= 1'b0;
			end
		end
	assign ar_valid = (((r_current_state == 3'b001) && !w_null_address) && !r_addr_issued) || r_drain_ar;
	assign ar_addr = r_ctrlrd_addr;
	assign ar_len = 8'h00;
	assign ar_size = 3'b010;
	assign ar_burst = 2'b01;
	assign ar_id = r_expected_axi_id;
	assign ar_lock = 1'b0;
	assign ar_cache = 4'b0010;
	assign ar_prot = 3'b000;
	assign ar_qos = 4'h0;
	assign ar_region = 4'h0;
	assign ctrlrd_error = r_ctrlrd_error;
	assign ctrlrd_result = r_axi_read_data;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	function automatic [127:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [3:0] protocol;
		input reg [7:0] event_code;
		input reg [8:0] channel_id;
		input reg [7:0] unit_id;
		input reg [15:0] agent_id;
		input reg [63:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, 15'h0000, protocol, event_code, channel_id, agent_id, unit_id, event_data};
	endfunction
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			r_mon_timestamp <= 1'sb0;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			case (r_current_state)
				3'b110:
					if (w_axi_response_error) begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h0, (r_read_resp == 2'b10 ? 8'h00 : 8'h01), MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {46'h000000000000, r_read_resp, 16'h0000});
						r_mon_timestamp <= i_mon_time;
					end
					else begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h4, 8'h0d, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_ctrlrd_addr));
						r_mon_timestamp <= i_mon_time;
					end
				3'b101:
					if (!w_null_address) begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, 8'h02, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_ctrlrd_addr));
						r_mon_timestamp <= i_mon_time;
					end
				3'b100: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypePerf, 4'h4, 8'h07, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_retry_counter));
					r_mon_timestamp <= i_mon_time;
				end
				default:
					;
			endcase
		end
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	assign mon_timestamp = r_mon_timestamp;
	initial _sv2v_0 = 0;
endmodule
