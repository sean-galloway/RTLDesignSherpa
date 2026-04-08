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
	always @(posedge clk)
		if (!rst_n)
			counter_bin_curr <= 'b0;
		else
			counter_bin_curr <= counter_bin_next;
	initial _sv2v_0 = 0;
endmodule
module fifo_control (
	wr_clk,
	wr_rst_n,
	rd_clk,
	rd_rst_n,
	wr_ptr_bin,
	wdom_rd_ptr_bin,
	rd_ptr_bin,
	rdom_wr_ptr_bin,
	count,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] ADDR_WIDTH = 3;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 0;
	input wire wr_clk;
	input wire wr_rst_n;
	input wire rd_clk;
	input wire rd_rst_n;
	input wire [ADDR_WIDTH:0] wr_ptr_bin;
	input wire [ADDR_WIDTH:0] wdom_rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rdom_wr_ptr_bin;
	output wire [ADDR_WIDTH:0] count;
	output reg wr_full;
	output reg wr_almost_full;
	output reg rd_empty;
	output reg rd_almost_empty;
	localparam signed [31:0] D = DEPTH;
	localparam signed [31:0] AW = ADDR_WIDTH;
	localparam signed [31:0] AFULL = ALMOST_WR_MARGIN;
	localparam signed [31:0] AEMPTY = ALMOST_RD_MARGIN;
	localparam signed [31:0] AFT = D - AFULL;
	localparam signed [31:0] AET = AEMPTY;
	wire w_wdom_ptr_xor;
	wire w_rdom_ptr_xor;
	wire w_wr_full_d;
	wire w_wr_almost_full_d;
	wire w_rd_empty_d;
	wire w_rd_almost_empty_d;
	wire [AW:0] w_almost_full_count;
	wire [AW:0] w_almost_empty_count;
	assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
	assign w_rdom_ptr_xor = rd_ptr_bin[AW] ^ rdom_wr_ptr_bin[AW];
	assign w_wr_full_d = w_wdom_ptr_xor && (wr_ptr_bin[AW - 1:0] == wdom_rd_ptr_bin[AW - 1:0]);
	function automatic signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65_signed;
		input reg signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65_signed = inp;
	endfunction
	assign w_almost_full_count = (w_wdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - wdom_rd_ptr_bin[AW - 1:0]) + wr_ptr_bin[AW - 1:0] : wr_ptr_bin[AW - 1:0] - wdom_rd_ptr_bin[AW - 1:0]);
	assign w_wr_almost_full_d = w_almost_full_count >= sv2v_cast_2BB65_signed(AFT);
	always @(posedge wr_clk or negedge wr_rst_n)
		if (!wr_rst_n) begin
			wr_full <= 'b0;
			wr_almost_full <= 'b0;
		end
		else begin
			wr_full <= w_wr_full_d;
			wr_almost_full <= w_wr_almost_full_d;
		end
	wire [ADDR_WIDTH:0] w_wr_ptr_for_empty;
	wire w_rdom_ptr_xor_for_empty;
	generate
		if (REGISTERED == 1) begin : gen_flop_mode
			reg [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;
			always @(posedge rd_clk)
				if (!rd_rst_n)
					r_rdom_wr_ptr_bin_delayed <= 1'sb0;
				else
					r_rdom_wr_ptr_bin_delayed <= rdom_wr_ptr_bin;
			assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
		end
		else begin : gen_mux_mode
			assign w_wr_ptr_for_empty = rdom_wr_ptr_bin;
		end
	endgenerate
	assign w_rdom_ptr_xor_for_empty = rd_ptr_bin[AW] ^ w_wr_ptr_for_empty[AW];
	assign w_rd_empty_d = !w_rdom_ptr_xor_for_empty && (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]);
	assign w_almost_empty_count = (w_rdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - rd_ptr_bin[AW - 1:0]) + rdom_wr_ptr_bin[AW - 1:0] : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign w_rd_almost_empty_d = w_almost_empty_count <= sv2v_cast_2BB65_signed(AET);
	wire [ADDR_WIDTH:0] w_count;
	reg [ADDR_WIDTH:0] r_count;
	assign w_count = (w_rdom_ptr_xor ? (rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]) + sv2v_cast_2BB65_signed(D) : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign count = (REGISTERED == 1 ? r_count : w_count);
	always @(posedge rd_clk or negedge rd_rst_n)
		if (!rd_rst_n) begin
			rd_empty <= 'b1;
			rd_almost_empty <= 'b0;
			r_count <= 'b0;
		end
		else begin
			rd_empty <= w_rd_empty_d;
			rd_almost_empty <= w_rd_almost_empty_d;
			r_count <= w_count;
		end
endmodule
module gaxi_fifo_sync (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_ready,
	count,
	rd_valid,
	rd_data
);
	reg _sv2v_0;
	parameter signed [31:0] MEM_STYLE = 32'sd0;
	parameter signed [31:0] REGISTERED = 0;
	parameter signed [31:0] DATA_WIDTH = 4;
	parameter signed [31:0] DEPTH = 4;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(DEPTH);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire [DW - 1:0] wr_data;
	input wire rd_ready;
	output wire [AW:0] count;
	output wire rd_valid;
	output wire [DW - 1:0] rd_data;
	wire [AW - 1:0] r_wr_addr;
	wire [AW - 1:0] r_rd_addr;
	wire [AW:0] r_wr_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	reg [DW - 1:0] w_rd_data;
	wire w_write;
	wire w_read;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) write_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_write && !r_wr_full),
		.counter_bin_curr(r_wr_ptr_bin),
		.counter_bin_next(w_wr_ptr_bin_next)
	);
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) read_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_read && !r_rd_empty),
		.counter_bin_curr(r_rd_ptr_bin),
		.counter_bin_next(w_rd_ptr_bin_next)
	);
	fifo_control #(
		.DEPTH(D),
		.ADDR_WIDTH(AW),
		.ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
		.ALMOST_WR_MARGIN(ALMOST_WR_MARGIN),
		.REGISTERED(REGISTERED)
	) fifo_control_inst(
		.wr_clk(axi_aclk),
		.wr_rst_n(axi_aresetn),
		.rd_clk(axi_aclk),
		.rd_rst_n(axi_aresetn),
		.wr_ptr_bin(w_wr_ptr_bin_next),
		.wdom_rd_ptr_bin(w_rd_ptr_bin_next),
		.rd_ptr_bin(w_rd_ptr_bin_next),
		.rdom_wr_ptr_bin(w_wr_ptr_bin_next),
		.count(count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_valid = !r_rd_empty;
	assign r_wr_addr = r_wr_ptr_bin[AW - 1:0];
	assign r_rd_addr = r_rd_ptr_bin[AW - 1:0];
	generate
		if (MEM_STYLE == 32'sd1) begin : gen_srl
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				always @(posedge axi_aclk)
					if (!axi_aresetn)
						w_rd_data <= 1'sb0;
					else
						w_rd_data <= mem[r_rd_addr];
			end
			else begin : g_mux
				always @(*) begin
					if (_sv2v_0)
						;
					w_rd_data = mem[r_rd_addr];
				end
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			always @(posedge axi_aclk)
				if (!axi_aresetn)
					w_rd_data <= 1'sb0;
				else
					w_rd_data <= mem[r_rd_addr];
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				always @(posedge axi_aclk)
					if (!axi_aresetn)
						w_rd_data <= 1'sb0;
					else
						w_rd_data <= mem[r_rd_addr];
			end
			else begin : g_mux
				always @(*) begin
					if (_sv2v_0)
						;
					w_rd_data = mem[r_rd_addr];
				end
			end
		end
	endgenerate
	assign rd_data = w_rd_data;
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
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
	parameter signed [31:0] BUF_WIDTH = DATA_WIDTH * DEPTH;
	parameter signed [31:0] BW = BUF_WIDTH;
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
	reg [BW - 1:0] r_data;
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	wire [DW - 1:0] zeros;
	assign zeros = 'b0;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			r_data <= 'b0;
			r_data_count <= 'b0;
		end
		else
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: begin
					r_data[DW * r_data_count+:DW] <= wr_data;
					r_data_count <= r_data_count + 1;
				end
				2'b01: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data_count <= r_data_count - 1;
				end
				2'b11: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data[DW * (sv2v_cast_32(r_data_count) - 1)+:DW] <= wr_data;
				end
				default:
					;
			endcase
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[DW - 1:0];
	assign rd_count = r_data_count;
	assign count = r_data_count;
endmodule
module apb_monitor (
	aclk,
	aresetn,
	cmd_valid,
	cmd_ready,
	cmd_pwrite,
	cmd_paddr,
	cmd_pwdata,
	cmd_pstrb,
	cmd_pprot,
	rsp_valid,
	rsp_ready,
	rsp_prdata,
	rsp_pslverr,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_protocol_enable,
	cfg_slverr_enable,
	cfg_perf_enable,
	cfg_latency_enable,
	cfg_throughput_enable,
	cfg_debug_enable,
	cfg_trans_debug_enable,
	cfg_debug_level,
	cfg_cmd_timeout_cnt,
	cfg_rsp_timeout_cnt,
	cfg_latency_threshold,
	cfg_throughput_threshold,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	active_count,
	error_count,
	transaction_count
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] UNIT_ID = 1;
	parameter signed [31:0] AGENT_ID = 10;
	parameter signed [31:0] MAX_TRANSACTIONS = 4;
	parameter signed [31:0] MONITOR_FIFO_DEPTH = 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = DW / 8;
	input wire aclk;
	input wire aresetn;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cmd_pwrite;
	input wire [AW - 1:0] cmd_paddr;
	input wire [DW - 1:0] cmd_pwdata;
	input wire [SW - 1:0] cmd_pstrb;
	input wire [2:0] cmd_pprot;
	input wire rsp_valid;
	input wire rsp_ready;
	input wire [DW - 1:0] rsp_prdata;
	input wire rsp_pslverr;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_protocol_enable;
	input wire cfg_slverr_enable;
	input wire cfg_perf_enable;
	input wire cfg_latency_enable;
	input wire cfg_throughput_enable;
	input wire cfg_debug_enable;
	input wire cfg_trans_debug_enable;
	input wire [3:0] cfg_debug_level;
	input wire [15:0] cfg_cmd_timeout_cnt;
	input wire [15:0] cfg_rsp_timeout_cnt;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_throughput_threshold;
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [63:0] monbus_packet;
	output wire [7:0] active_count;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	reg [280:0] r_trans_table [0:MAX_TRANSACTIONS - 1];
	reg [7:0] r_active_count;
	reg [15:0] r_error_count;
	reg [31:0] r_transaction_count;
	reg [1:0] r_trans_state;
	reg [1:0] w_next_trans_state;
	wire w_state_change;
	reg [31:0] r_timestamp;
	reg [31:0] r_cmd_start_time;
	reg [15:0] r_cmd_timeout_timer;
	reg [15:0] r_rsp_timeout_timer;
	reg [MAX_TRANSACTIONS - 1:0] w_free_slot;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_free_idx;
	reg w_has_free_slot;
	reg [MAX_TRANSACTIONS - 1:0] w_active_trans;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_active_idx;
	reg w_has_active_trans;
	reg [MAX_TRANSACTIONS - 1:0] w_completed_trans;
	wire w_cmd_handshake;
	wire w_rsp_handshake;
	wire w_cmd_timeout;
	wire w_rsp_timeout;
	reg w_protocol_violation;
	reg w_latency_threshold_exceeded;
	reg [31:0] w_current_latency;
	reg [15:0] r_throughput_counter;
	reg [31:0] r_throughput_timer;
	reg w_generate_error_event;
	reg w_generate_timeout_event;
	reg w_generate_perf_event;
	reg w_generate_debug_event;
	reg w_generate_completion_event;
	reg [3:0] w_error_event_code;
	reg [3:0] w_timeout_event_code;
	reg w_fifo_wr_valid;
	wire w_fifo_wr_ready;
	reg [47:0] w_fifo_wr_data;
	wire w_fifo_rd_valid;
	wire w_fifo_rd_ready;
	wire [47:0] w_fifo_rd_data;
	wire [7:0] w_fifo_count;
	assign active_count = r_active_count;
	assign error_count = r_error_count;
	assign transaction_count = r_transaction_count;
	assign w_cmd_handshake = cmd_valid && cmd_ready;
	assign w_rsp_handshake = rsp_valid && rsp_ready;
	always @(posedge aclk)
		if (!aresetn)
			r_timestamp <= 1'sb0;
		else
			r_timestamp <= r_timestamp + 1'b1;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_trans_state = r_trans_state;
		case (r_trans_state)
			2'b00:
				if (w_cmd_handshake)
					w_next_trans_state = 2'b01;
			2'b01:
				if (w_rsp_handshake)
					w_next_trans_state = 2'b10;
			2'b10: w_next_trans_state = 2'b00;
			default: w_next_trans_state = 2'b00;
		endcase
	end
	assign w_state_change = w_next_trans_state != r_trans_state;
	always @(posedge aclk)
		if (!aresetn)
			r_trans_state <= 2'b00;
		else
			r_trans_state <= w_next_trans_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_free_slot = 1'sb0;
		w_free_idx = 1'sb0;
		w_has_free_slot = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
				if (!r_trans_table[i][280] && !w_has_free_slot) begin
					w_free_slot[i] = 1'b1;
					w_free_idx = i[$clog2(MAX_TRANSACTIONS) - 1:0];
					w_has_free_slot = 1'b1;
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_active_trans = 1'sb0;
		w_active_idx = 1'sb0;
		w_has_active_trans = 1'b0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
				if ((r_trans_table[i][280] && ((r_trans_table[i][273-:3] == 3'h1) || (r_trans_table[i][273-:3] == 3'h2))) && !w_has_active_trans) begin
					w_active_trans[i] = 1'b1;
					w_active_idx = i[$clog2(MAX_TRANSACTIONS) - 1:0];
					w_has_active_trans = 1'b1;
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_completed_trans = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
				if ((r_trans_table[i][280] && ((r_trans_table[i][273-:3] == 3'h3) || (r_trans_table[i][273-:3] == 3'h4))) && r_trans_table[i][275])
					w_completed_trans[i] = 1'b1;
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
					r_trans_table[i] <= 1'sb0;
			end
			r_active_count <= 1'sb0;
			r_transaction_count <= 1'sb0;
			r_cmd_start_time <= 1'sb0;
		end
		else begin
			if (w_cmd_handshake && w_has_free_slot) begin
				r_trans_table[w_free_idx][280] <= 1'b1;
				r_trans_table[w_free_idx][273-:3] <= 3'h1;
				r_trans_table[w_free_idx][270-:32] <= {{64 - AW {1'b0}}, cmd_paddr};
				r_trans_table[w_free_idx][219-:2] <= {1'b0, cmd_pwrite};
				r_trans_table[w_free_idx][217-:6] <= {cmd_pprot, cmd_pstrb[2:0]};
				r_trans_table[w_free_idx][279] <= 1'b1;
				r_trans_table[w_free_idx][278] <= cmd_pwrite;
				r_trans_table[w_free_idx][115-:32] <= r_timestamp;
				r_trans_table[w_free_idx][3-:4] <= 1'sb0;
				r_trans_table[w_free_idx][275] <= 1'b0;
				r_trans_table[w_free_idx][211-:32] <= 1'sb0;
				r_trans_table[w_free_idx][147-:32] <= 1'sb0;
				r_active_count <= r_active_count + 1'b1;
				r_cmd_start_time <= r_timestamp;
				r_trans_table[w_free_idx][273-:3] <= 3'h2;
				r_trans_table[w_free_idx][83-:32] <= r_timestamp;
			end
			if (w_rsp_handshake && w_has_active_trans) begin
				r_trans_table[w_active_idx][277] <= 1'b1;
				r_trans_table[w_active_idx][276] <= 1'b1;
				r_trans_table[w_active_idx][51-:32] <= r_timestamp;
				if (rsp_pslverr)
					r_trans_table[w_active_idx][217] <= 1'b1;
				if (rsp_pslverr && cfg_slverr_enable) begin
					r_trans_table[w_active_idx][273-:3] <= 3'h4;
					r_trans_table[w_active_idx][3-:4] <= 4'h0;
					r_error_count <= r_error_count + 1'b1;
				end
				else begin
					r_trans_table[w_active_idx][273-:3] <= 3'h3;
					r_trans_table[w_active_idx][3-:4] <= 4'h0;
				end
				r_transaction_count <= r_transaction_count + 1'b1;
			end
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
					if (w_completed_trans[i]) begin
						r_trans_table[i][280] <= 1'b0;
						r_active_count <= r_active_count - 1'b1;
					end
			end
		end
	always @(posedge aclk)
		if (!aresetn) begin
			r_cmd_timeout_timer <= 1'sb0;
			r_rsp_timeout_timer <= 1'sb0;
		end
		else begin
			if (((r_trans_state == 2'b00) && cmd_valid) && !cmd_ready)
				r_cmd_timeout_timer <= r_cmd_timeout_timer + 1'b1;
			else
				r_cmd_timeout_timer <= 1'sb0;
			if ((r_trans_state == 2'b01) && (!rsp_valid || !rsp_ready))
				r_rsp_timeout_timer <= r_rsp_timeout_timer + 1'b1;
			else
				r_rsp_timeout_timer <= 1'sb0;
		end
	assign w_cmd_timeout = (cfg_timeout_enable && (r_cmd_timeout_timer >= cfg_cmd_timeout_cnt)) && (r_cmd_timeout_timer != {16 {1'sb0}});
	assign w_rsp_timeout = (cfg_timeout_enable && (r_rsp_timeout_timer >= cfg_rsp_timeout_cnt)) && (r_rsp_timeout_timer != {16 {1'sb0}});
	always @(*) begin
		if (_sv2v_0)
			;
		w_protocol_violation = 1'b0;
		if (cfg_protocol_enable) begin
			if (rsp_valid && (r_trans_state == 2'b00))
				w_protocol_violation = 1'b1;
			if (cmd_valid && (r_trans_state == 2'b01))
				w_protocol_violation = 1'b1;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_current_latency = 1'sb0;
		w_latency_threshold_exceeded = 1'b0;
		if (w_has_active_trans && r_trans_table[w_active_idx][280]) begin
			w_current_latency = r_timestamp - r_trans_table[w_active_idx][115-:32];
			w_latency_threshold_exceeded = (cfg_perf_enable && cfg_latency_enable) && (w_current_latency > cfg_latency_threshold);
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			r_throughput_counter <= 1'sb0;
			r_throughput_timer <= 1'sb0;
		end
		else begin
			r_throughput_timer <= r_throughput_timer + 1'b1;
			if (w_rsp_handshake)
				r_throughput_counter <= r_throughput_counter + 1'b1;
			if (r_throughput_timer[15:0] == 16'hffff)
				r_throughput_counter <= 1'sb0;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		w_generate_error_event = 1'b0;
		w_generate_timeout_event = 1'b0;
		w_generate_perf_event = 1'b0;
		w_generate_debug_event = 1'b0;
		w_generate_completion_event = 1'b0;
		w_error_event_code = 4'h0;
		w_timeout_event_code = 4'h0;
		if (cfg_error_enable) begin
			if (w_protocol_violation) begin
				w_generate_error_event = 1'b1;
				w_error_event_code = 4'h1;
			end
			else if ((rsp_pslverr && w_rsp_handshake) && cfg_slverr_enable) begin
				w_generate_error_event = 1'b1;
				w_error_event_code = 4'h0;
			end
		end
		if (cfg_timeout_enable) begin
			if (w_cmd_timeout) begin
				w_generate_timeout_event = 1'b1;
				w_timeout_event_code = 4'h0;
			end
			else if (w_rsp_timeout) begin
				w_generate_timeout_event = 1'b1;
				w_timeout_event_code = 4'h1;
			end
		end
		if (cfg_perf_enable && w_latency_threshold_exceeded)
			w_generate_perf_event = 1'b1;
		if (cfg_debug_enable) begin
			if (cfg_trans_debug_enable && w_state_change)
				w_generate_debug_event = 1'b1;
		end
		if (w_rsp_handshake && !rsp_pslverr)
			w_generate_completion_event = 1'b1;
	end
	gaxi_fifo_sync #(
		.REGISTERED(1),
		.DATA_WIDTH(48),
		.DEPTH(MONITOR_FIFO_DEPTH),
		.ALMOST_WR_MARGIN(1),
		.ALMOST_RD_MARGIN(1)
	) monitor_fifo(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(w_fifo_wr_valid),
		.wr_ready(w_fifo_wr_ready),
		.wr_data(w_fifo_wr_data),
		.rd_ready(w_fifo_rd_ready),
		.count(),
		.rd_valid(w_fifo_rd_valid),
		.rd_data(w_fifo_rd_data)
	);
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr_valid = 1'b0;
		w_fifo_wr_data = 1'sb0;
		if (w_generate_error_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[47-:4] = monitor_common_pkg_PktTypeError;
			w_fifo_wr_data[43-:4] = w_error_event_code;
			w_fifo_wr_data[39-:32] = cmd_paddr;
			w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
		end
		else if (w_generate_timeout_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[47-:4] = monitor_common_pkg_PktTypeTimeout;
			w_fifo_wr_data[43-:4] = w_timeout_event_code;
			w_fifo_wr_data[39-:32] = (w_has_active_trans ? r_trans_table[w_active_idx][270:239] : cmd_paddr);
			w_fifo_wr_data[7-:8] = {r_cmd_timeout_timer[7:0]};
		end
		else if (w_generate_perf_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[47-:4] = monitor_common_pkg_PktTypePerf;
			w_fifo_wr_data[43-:4] = (cmd_pwrite ? 4'h1 : 4'h0);
			w_fifo_wr_data[39-:32] = w_current_latency;
			w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
		end
		else if (w_generate_debug_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[47-:4] = monitor_common_pkg_PktTypeDebug;
			w_fifo_wr_data[43-:4] = 4'h1;
			w_fifo_wr_data[39-:32] = {28'h0000000, r_trans_state, w_next_trans_state};
			w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
		end
		else if (w_generate_completion_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[47-:4] = monitor_common_pkg_PktTypeCompletion;
			w_fifo_wr_data[43-:4] = 4'h0;
			w_fifo_wr_data[39-:32] = cmd_paddr;
			w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
		end
	end
	always @(posedge aclk)
		if (!aresetn)
			;
		else begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
				if ((((r_trans_table[i][280] && ((r_trans_table[i][273-:3] == 3'h3) || (r_trans_table[i][273-:3] == 3'h4))) && !r_trans_table[i][275]) && w_fifo_wr_valid) && w_fifo_wr_ready)
					r_trans_table[i][275] <= 1'b1;
		end
	wire w_monbus_pkt_valid;
	wire w_monbus_pkt_ready;
	wire [63:0] w_monbus_pkt_data;
	assign w_monbus_pkt_valid = w_fifo_rd_valid;
	assign w_fifo_rd_ready = w_monbus_pkt_ready;
	assign w_monbus_pkt_data[63:60] = w_fifo_rd_data[47-:4];
	assign w_monbus_pkt_data[59:57] = 3'b010;
	assign w_monbus_pkt_data[56:53] = w_fifo_rd_data[43-:4];
	assign w_monbus_pkt_data[52:47] = 6'h00;
	assign w_monbus_pkt_data[46:43] = UNIT_ID[3:0];
	assign w_monbus_pkt_data[42:35] = AGENT_ID[7:0];
	assign w_monbus_pkt_data[34:3] = w_fifo_rd_data[39-:32];
	assign w_monbus_pkt_data[2:0] = w_fifo_rd_data[2:0];
	gaxi_skid_buffer #(
		.DATA_WIDTH(64),
		.DEPTH(2)
	) monbus_skid_buffer(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(w_monbus_pkt_valid),
		.wr_ready(w_monbus_pkt_ready),
		.wr_data(w_monbus_pkt_data),
		.rd_valid(monbus_valid),
		.rd_ready(monbus_ready),
		.rd_data(monbus_packet),
		.count(),
		.rd_count()
	);
	initial _sv2v_0 = 0;
endmodule
