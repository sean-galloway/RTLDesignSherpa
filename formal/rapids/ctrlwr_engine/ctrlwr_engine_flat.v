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
module ctrlwr_engine (
	clk,
	rst_n,
	ctrlwr_valid,
	ctrlwr_ready,
	ctrlwr_pkt_addr,
	ctrlwr_pkt_data,
	ctrlwr_error,
	cfg_channel_reset,
	ctrlwr_engine_idle,
	aw_valid,
	aw_ready,
	aw_addr,
	aw_len,
	aw_size,
	aw_burst,
	aw_id,
	aw_lock,
	aw_cache,
	aw_prot,
	aw_qos,
	aw_region,
	w_valid,
	w_ready,
	w_data,
	w_strb,
	w_last,
	b_valid,
	b_ready,
	b_id,
	b_resp,
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
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter [15:0] MON_AGENT_ID = 16'h0020;
	parameter [7:0] MON_UNIT_ID = 8'h01;
	parameter [8:0] MON_CHANNEL_ID = 9'h000;
	input wire clk;
	input wire rst_n;
	input wire ctrlwr_valid;
	output wire ctrlwr_ready;
	input wire [ADDR_WIDTH - 1:0] ctrlwr_pkt_addr;
	input wire [31:0] ctrlwr_pkt_data;
	output wire ctrlwr_error;
	input wire cfg_channel_reset;
	output wire ctrlwr_engine_idle;
	output wire aw_valid;
	input wire aw_ready;
	output wire [ADDR_WIDTH - 1:0] aw_addr;
	output wire [7:0] aw_len;
	output wire [2:0] aw_size;
	output wire [1:0] aw_burst;
	output wire [AXI_ID_WIDTH - 1:0] aw_id;
	output wire aw_lock;
	output wire [3:0] aw_cache;
	output wire [2:0] aw_prot;
	output wire [3:0] aw_qos;
	output wire [3:0] aw_region;
	output wire w_valid;
	input wire w_ready;
	output wire [31:0] w_data;
	output wire [3:0] w_strb;
	output wire w_last;
	input wire b_valid;
	output wire b_ready;
	input wire [AXI_ID_WIDTH - 1:0] b_id;
	input wire [1:0] b_resp;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	initial if (AXI_ID_WIDTH < CHAN_WIDTH) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dma-ip/rapids/rtl/fub/ctrlwr_engine.sv:92:13 - ctrlwr_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
		$finish(1);
	end
	reg [2:0] r_current_state;
	reg [2:0] w_next_state;
	reg r_channel_reset_active;
	wire w_safe_to_reset;
	wire w_fifo_empty;
	wire w_no_active_transaction;
	reg r_drain_aw;
	reg r_drain_w;
	reg r_drain_b;
	wire w_draining;
	reg [ADDR_WIDTH - 1:0] r_ctrlwr_addr;
	reg [31:0] r_ctrlwr_data;
	reg r_addr_issued;
	reg r_data_issued;
	reg [1:0] r_write_resp;
	reg [AXI_ID_WIDTH - 1:0] r_expected_axi_id;
	reg r_ctrlwr_error;
	wire w_null_address;
	wire w_address_error;
	wire w_axi_response_error;
	wire w_both_phases_issued;
	wire w_transaction_complete;
	wire w_our_axi_response;
	wire w_ctrlwr_req_skid_valid_in;
	wire w_ctrlwr_req_skid_ready_in;
	wire w_ctrlwr_req_skid_valid_out;
	wire w_ctrlwr_req_skid_ready_out;
	wire [ADDR_WIDTH + 31:0] w_ctrlwr_req_skid_din;
	wire [ADDR_WIDTH + 31:0] w_ctrlwr_req_skid_dout;
	reg r_mon_valid;
	reg [127:0] r_mon_packet;
	reg [63:0] r_mon_timestamp;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	assign w_draining = (r_drain_aw || r_drain_w) || r_drain_b;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_drain_aw <= 1'b0;
			r_drain_w <= 1'b0;
			r_drain_b <= 1'b0;
		end
		else if (r_drain_aw) begin
			if (aw_ready) begin
				r_drain_aw <= 1'b0;
				r_drain_w <= 1'b1;
			end
		end
		else if (r_drain_w) begin
			if (w_ready) begin
				r_drain_w <= 1'b0;
				r_drain_b <= 1'b1;
			end
		end
		else if (r_drain_b) begin
			if (b_valid && b_ready)
				r_drain_b <= 1'b0;
		end
		else if (r_channel_reset_active) begin
			if (aw_valid && !aw_ready)
				r_drain_aw <= 1'b1;
			else if (((r_addr_issued || (aw_valid && aw_ready)) && !r_data_issued) && !(w_valid && w_ready))
				r_drain_w <= 1'b1;
			else if (((r_addr_issued || (aw_valid && aw_ready)) && (r_data_issued || (w_valid && w_ready))) && !(b_valid && b_ready))
				r_drain_b <= 1'b1;
		end
	assign w_fifo_empty = !w_ctrlwr_req_skid_valid_out;
	assign w_no_active_transaction = !r_addr_issued && !r_data_issued;
	assign w_safe_to_reset = (w_fifo_empty && w_no_active_transaction) && (r_current_state == 3'b000);
	assign ctrlwr_engine_idle = (((r_current_state == 3'b000) && !r_channel_reset_active) && w_fifo_empty) && !w_draining;
	assign w_ctrlwr_req_skid_valid_in = ctrlwr_valid && !r_channel_reset_active;
	assign ctrlwr_ready = w_ctrlwr_req_skid_ready_in && !r_channel_reset_active;
	assign w_ctrlwr_req_skid_din = {ctrlwr_pkt_addr, ctrlwr_pkt_data};
	gaxi_skid_buffer #(
		.DATA_WIDTH(ADDR_WIDTH + 32),
		.DEPTH(2)
	) i_ctrlwr_req_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_ctrlwr_req_skid_valid_in),
		.wr_ready(w_ctrlwr_req_skid_ready_in),
		.wr_data(w_ctrlwr_req_skid_din),
		.rd_valid(w_ctrlwr_req_skid_valid_out),
		.rd_ready(w_ctrlwr_req_skid_ready_out),
		.rd_data(w_ctrlwr_req_skid_dout),
		.count(),
		.rd_count()
	);
	assign w_ctrlwr_req_skid_ready_out = (((r_current_state == 3'b000) && w_ctrlwr_req_skid_valid_out) && !r_channel_reset_active) && !w_draining;
	assign w_null_address = r_ctrlwr_addr == 64'h0000000000000000;
	assign w_address_error = (r_ctrlwr_addr[1:0] != 2'b00) && !w_null_address;
	assign w_axi_response_error = ((b_resp != 2'b00) && b_valid) && w_our_axi_response;
	assign w_both_phases_issued = r_addr_issued && r_data_issued;
	assign w_transaction_complete = w_our_axi_response && b_valid;
	assign w_our_axi_response = b_valid && (b_id == r_expected_axi_id);
	assign b_ready = ((r_current_state == 3'b011) || r_drain_b) && w_our_axi_response;
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
				else if (w_ctrlwr_req_skid_valid_out && w_ctrlwr_req_skid_ready_out)
					w_next_state = 3'b001;
			3'b001:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_address_error)
					w_next_state = 3'b101;
				else if (w_null_address)
					w_next_state = 3'b000;
				else if (r_addr_issued)
					w_next_state = 3'b010;
			3'b010:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_both_phases_issued)
					w_next_state = 3'b011;
			3'b011:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_transaction_complete) begin
					if (w_axi_response_error)
						w_next_state = 3'b101;
					else
						w_next_state = 3'b100;
				end
			3'b100: w_next_state = 3'b000;
			3'b101: w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_ctrlwr_addr <= 64'h0000000000000000;
			r_ctrlwr_data <= 32'h00000000;
			r_addr_issued <= 1'b0;
			r_data_issued <= 1'b0;
			r_write_resp <= 2'b00;
			r_expected_axi_id <= 1'sb0;
			r_ctrlwr_error <= 1'b0;
		end
		else begin
			case (r_current_state)
				3'b000: begin
					if (w_ctrlwr_req_skid_valid_out && w_ctrlwr_req_skid_ready_out) begin
						{r_ctrlwr_addr, r_ctrlwr_data} <= w_ctrlwr_req_skid_dout;
						r_expected_axi_id <= {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, CHANNEL_ID[CHAN_WIDTH - 1:0]};
					end
					r_addr_issued <= 1'b0;
					r_data_issued <= 1'b0;
					r_write_resp <= 2'b00;
				end
				3'b001:
					if (w_address_error)
						r_ctrlwr_error <= 1'b1;
					else if (!w_null_address && aw_ready)
						r_addr_issued <= 1'b1;
				3'b010:
					if (w_ready)
						r_data_issued <= 1'b1;
				3'b011:
					if (w_transaction_complete) begin
						r_write_resp <= b_resp;
						if (w_axi_response_error)
							r_ctrlwr_error <= 1'b1;
					end
				3'b101: r_ctrlwr_error <= 1'b1;
				default:
					;
			endcase
			if (r_channel_reset_active) begin
				r_addr_issued <= 1'b0;
				r_data_issued <= 1'b0;
				r_write_resp <= 2'b00;
				r_ctrlwr_error <= 1'b0;
			end
		end
	assign aw_valid = ((((r_current_state == 3'b001) && !w_null_address) && !w_address_error) && !r_addr_issued) || r_drain_aw;
	assign aw_addr = r_ctrlwr_addr;
	assign aw_len = 8'h00;
	assign aw_size = 3'b010;
	assign aw_burst = 2'b01;
	assign aw_id = r_expected_axi_id;
	assign aw_lock = 1'b0;
	assign aw_cache = 4'b0010;
	assign aw_prot = 3'b000;
	assign aw_qos = 4'h0;
	assign aw_region = 4'h0;
	assign w_valid = ((((r_current_state == 3'b010) && !w_null_address) && r_addr_issued) && !r_data_issued) || r_drain_w;
	assign w_data = r_ctrlwr_data;
	assign w_strb = 4'b1111;
	assign w_last = 1'b1;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
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
				3'b101:
					if (w_address_error) begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h4, 8'h08, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_ctrlwr_addr));
						r_mon_timestamp <= i_mon_time;
					end
					else if (r_ctrlwr_error) begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h0, (r_write_resp == 2'b10 ? 8'h00 : 8'h01), MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {46'h000000000000, r_write_resp, 16'h0000});
						r_mon_timestamp <= i_mon_time;
					end
				3'b100:
					if (!w_null_address) begin
						r_mon_valid <= 1'b1;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, 8'h03, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_ctrlwr_addr));
						r_mon_timestamp <= i_mon_time;
					end
				default:
					;
			endcase
		end
	assign ctrlwr_error = r_ctrlwr_error;
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	assign mon_timestamp = r_mon_timestamp;
	initial _sv2v_0 = 0;
endmodule
