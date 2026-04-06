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
module descriptor_engine (
	clk,
	rst_n,
	apb_valid,
	apb_ready,
	apb_addr,
	channel_idle,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_error,
	descriptor_eos,
	descriptor_eol,
	descriptor_eod,
	descriptor_type,
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
	r_resp,
	r_last,
	r_id,
	cfg_prefetch_enable,
	cfg_fifo_threshold,
	cfg_addr0_base,
	cfg_addr0_limit,
	cfg_addr1_base,
	cfg_addr1_limit,
	cfg_channel_reset,
	descriptor_engine_idle,
	mon_valid,
	mon_ready,
	mon_packet
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 32;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] FIFO_DEPTH = 8;
	parameter signed [31:0] DESC_ADDR_FIFO_DEPTH = 2;
	parameter signed [31:0] TIMEOUT_CYCLES = 1000;
	parameter [7:0] MON_AGENT_ID = 8'h10;
	parameter [3:0] MON_UNIT_ID = 4'h1;
	parameter [5:0] MON_CHANNEL_ID = 6'h00;
	input wire clk;
	input wire rst_n;
	input wire apb_valid;
	output wire apb_ready;
	input wire [ADDR_WIDTH - 1:0] apb_addr;
	input wire channel_idle;
	output wire descriptor_valid;
	input wire descriptor_ready;
	output wire [255:0] descriptor_packet;
	output wire descriptor_error;
	output wire descriptor_eos;
	output wire descriptor_eol;
	output wire descriptor_eod;
	output wire [1:0] descriptor_type;
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
	input wire [255:0] r_data;
	input wire [1:0] r_resp;
	input wire r_last;
	input wire [AXI_ID_WIDTH - 1:0] r_id;
	input wire cfg_prefetch_enable;
	input wire [3:0] cfg_fifo_threshold;
	input wire [ADDR_WIDTH - 1:0] cfg_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_addr1_limit;
	input wire cfg_channel_reset;
	output wire descriptor_engine_idle;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
	initial if (AXI_ID_WIDTH < CHAN_WIDTH) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/stream/rtl/fub/descriptor_engine.sv:137:13 - descriptor_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
		$finish(1);
	end
	reg [2:0] r_current_state;
	reg [2:0] w_next_state;
	reg r_channel_reset_active;
	wire w_safe_to_reset;
	wire w_fifos_empty;
	wire w_no_active_operations;
	wire w_apb_skid_valid_in;
	wire w_apb_skid_ready_in;
	wire w_apb_skid_valid_out;
	wire w_apb_skid_ready_out;
	wire [ADDR_WIDTH - 1:0] w_apb_skid_dout;
	reg w_desc_addr_fifo_wr_valid;
	wire w_desc_addr_fifo_wr_ready;
	wire w_desc_addr_fifo_rd_valid;
	wire w_desc_addr_fifo_rd_ready;
	reg [ADDR_WIDTH - 1:0] w_desc_addr_fifo_wr_data;
	wire [ADDR_WIDTH - 1:0] w_desc_addr_fifo_rd_data;
	wire w_desc_addr_fifo_empty;
	wire w_desc_fifo_wr_valid;
	wire w_desc_fifo_wr_ready;
	wire w_desc_fifo_rd_valid;
	wire w_desc_fifo_rd_ready;
	reg [260:0] w_desc_fifo_wr_data;
	wire [260:0] w_desc_fifo_rd_data;
	reg r_apb_operation_active;
	reg r_axi_read_active;
	reg [ADDR_WIDTH - 1:0] r_axi_read_addr;
	reg [1:0] r_axi_read_resp;
	reg [255:0] r_descriptor_data;
	reg [ADDR_WIDTH - 1:0] r_saved_next_addr;
	wire w_chain_condition;
	wire w_next_addr_valid;
	wire w_should_chain;
	reg w_desc_eos;
	reg w_desc_eol;
	reg w_desc_eod;
	reg w_desc_last;
	reg w_desc_valid;
	reg [1:0] w_desc_type;
	reg [31:0] w_next_addr;
	wire w_addr_range_valid;
	wire w_our_axi_response;
	wire w_axi_response_ok;
	reg r_descriptor_error;
	reg r_apb_ip;
	reg r_channel_idle_prev;
	reg r_mon_valid;
	reg [63:0] r_mon_packet;
	always @(posedge clk)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	assign w_fifos_empty = (!w_apb_skid_valid_out && !w_desc_addr_fifo_rd_valid) && !w_desc_fifo_rd_valid;
	assign w_no_active_operations = !r_apb_operation_active && !r_axi_read_active;
	assign w_safe_to_reset = (w_fifos_empty && w_no_active_operations) && (r_current_state == 3'b000);
	assign descriptor_engine_idle = ((r_current_state == 3'b000) && !r_channel_reset_active) && w_fifos_empty;
	wire w_apb_addr_valid;
	assign w_apb_addr_valid = apb_addr != {ADDR_WIDTH {1'sb0}};
	assign w_apb_skid_valid_in = (((apb_valid && !r_channel_reset_active) && w_desc_addr_fifo_empty) && channel_idle) && !r_apb_ip;
	assign apb_ready = (((w_apb_skid_ready_in && !r_channel_reset_active) && w_desc_addr_fifo_empty) && channel_idle) && !r_apb_ip;
	gaxi_skid_buffer #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(2)
	) i_apb_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_apb_skid_valid_in),
		.wr_ready(w_apb_skid_ready_in),
		.wr_data(apb_addr),
		.rd_valid(w_apb_skid_valid_out),
		.rd_ready(w_apb_skid_ready_out),
		.rd_data(w_apb_skid_dout),
		.count(),
		.rd_count()
	);
	assign w_apb_skid_ready_out = ((r_current_state == 3'b000) && w_desc_addr_fifo_wr_ready) && !r_channel_reset_active;
	gaxi_fifo_sync #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(DESC_ADDR_FIFO_DEPTH)
	) i_desc_addr_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_desc_addr_fifo_wr_valid),
		.wr_ready(w_desc_addr_fifo_wr_ready),
		.wr_data(w_desc_addr_fifo_wr_data),
		.rd_valid(w_desc_addr_fifo_rd_valid),
		.rd_ready(w_desc_addr_fifo_rd_ready),
		.rd_data(w_desc_addr_fifo_rd_data),
		.count()
	);
	assign w_desc_addr_fifo_empty = !w_desc_addr_fifo_rd_valid;
	assign w_desc_addr_fifo_rd_ready = (r_current_state == 3'b000) && !r_channel_reset_active;
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_addr_fifo_wr_valid = 1'b0;
		w_desc_addr_fifo_wr_data = 1'sb0;
		if (w_apb_skid_valid_out && w_apb_skid_ready_out) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = w_apb_skid_dout;
		end
		else if (w_should_chain && (r_current_state == 3'b011)) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
		end
	end
	wire [ADDR_WIDTH - 1:0] w_next_addr_extended;
	assign w_next_addr_extended = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
	assign w_next_addr_valid = ((w_next_addr_extended >= cfg_addr0_base) && (w_next_addr_extended <= cfg_addr0_limit)) || ((w_next_addr_extended >= cfg_addr1_base) && (w_next_addr_extended <= cfg_addr1_limit));
	assign w_chain_condition = ((w_next_addr != {32 {1'sb0}}) && !w_desc_last) && w_desc_valid;
	assign w_should_chain = ((w_chain_condition && w_next_addr_valid) && !r_descriptor_error) && w_desc_fifo_wr_ready;
	assign w_desc_fifo_wr_valid = (r_current_state == 3'b011) && !r_channel_reset_active;
	assign w_desc_fifo_rd_ready = descriptor_ready && !r_channel_reset_active;
	gaxi_fifo_sync #(
		.DATA_WIDTH(261),
		.DEPTH(FIFO_DEPTH)
	) i_descriptor_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_desc_fifo_wr_valid),
		.wr_ready(w_desc_fifo_wr_ready),
		.wr_data(w_desc_fifo_wr_data),
		.rd_valid(w_desc_fifo_rd_valid),
		.rd_ready(w_desc_fifo_rd_ready),
		.rd_data(w_desc_fifo_rd_data),
		.count()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_eos = 1'b0;
		w_desc_eol = 1'b0;
		w_desc_eod = 1'b0;
		w_desc_last = 1'b0;
		w_desc_type = 2'b00;
		w_next_addr = 32'h00000000;
		w_next_addr = r_descriptor_data[191:160];
		w_desc_last = r_descriptor_data[194];
		w_desc_valid = r_descriptor_data[192];
		w_desc_eos = 1'b0;
		w_desc_eol = 1'b0;
		w_desc_eod = 1'b0;
		w_desc_type = 2'b00;
	end
	assign w_addr_range_valid = ((r_axi_read_addr >= cfg_addr0_base) && (r_axi_read_addr <= cfg_addr0_limit)) || ((r_axi_read_addr >= cfg_addr1_base) && (r_axi_read_addr <= cfg_addr1_limit));
	assign w_our_axi_response = r_valid && (r_id[CHAN_WIDTH - 1:0] == CHANNEL_ID[CHAN_WIDTH - 1:0]);
	assign w_axi_response_ok = r_resp == 2'b00;
	assign r_ready = (r_current_state == 3'b010) && w_our_axi_response;
	always @(posedge clk)
		if (!rst_n)
			r_current_state <= 3'b000;
		else
			r_current_state <= w_next_state;
	reg w_pkt_error;
	reg w_pkt_last;
	reg w_pkt_gen_irq;
	reg w_pkt_valid;
	reg [31:0] w_pkt_next_descriptor_ptr;
	reg [31:0] w_pkt_length;
	reg [63:0] w_pkt_dst_addr;
	reg [63:0] w_pkt_src_addr;
	always @(*) begin
		if (_sv2v_0)
			;
		w_pkt_error = r_data[195];
		w_pkt_last = r_data[194];
		w_pkt_gen_irq = r_data[193];
		w_pkt_valid = r_data[192];
		w_pkt_next_descriptor_ptr = r_data[191:160];
		w_pkt_length = r_data[159:128];
		w_pkt_dst_addr = r_data[127:64];
		w_pkt_src_addr = r_data[63:0];
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		case (r_current_state)
			3'b000:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready)
					w_next_state = 3'b001;
			3'b001:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (ar_ready)
					w_next_state = 3'b010;
			3'b010:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_our_axi_response && r_valid) begin
					if (w_axi_response_ok)
						w_next_state = 3'b011;
					else
						w_next_state = 3'b100;
				end
			3'b011:
				if (w_desc_fifo_wr_ready)
					w_next_state = 3'b000;
			3'b100: w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk)
		if (!rst_n) begin
			r_apb_operation_active <= 1'b0;
			r_axi_read_active <= 1'b0;
			r_axi_read_addr <= 64'h0000000000000000;
			r_axi_read_resp <= 2'b00;
			r_descriptor_data <= 1'sb0;
			r_saved_next_addr <= 64'h0000000000000000;
			r_descriptor_error <= 1'b0;
		end
		else begin
			case (r_current_state)
				3'b000: begin
					if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready) begin
						r_apb_operation_active <= 1'b1;
						r_axi_read_addr <= w_desc_addr_fifo_rd_data;
					end
					r_descriptor_error <= 1'b0;
				end
				3'b001:
					if (ar_ready)
						r_axi_read_active <= 1'b1;
				3'b010:
					if (w_our_axi_response && r_valid) begin
						r_descriptor_data <= r_data;
						r_axi_read_resp <= r_resp;
						r_saved_next_addr <= {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
						if (!r_data[192])
							r_descriptor_error <= 1'b1;
					end
				3'b011:
					if (w_desc_fifo_wr_ready) begin
						r_apb_operation_active <= 1'b0;
						r_axi_read_active <= 1'b0;
					end
				3'b100: begin
					r_descriptor_error <= 1'b1;
					r_apb_operation_active <= 1'b0;
					r_axi_read_active <= 1'b0;
				end
				default:
					;
			endcase
			// APB address-0 error detection (merged from separate always block)
			if (apb_valid && !w_apb_addr_valid)
				r_descriptor_error <= 1'b1;
			if (r_channel_reset_active) begin
				r_apb_operation_active <= 1'b0;
				r_axi_read_active <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_fifo_wr_data = 1'sb0;
		if (r_current_state == 3'b011) begin
			w_desc_fifo_wr_data[260-:256] = r_descriptor_data;
			w_desc_fifo_wr_data[4] = w_desc_eos;
			w_desc_fifo_wr_data[3] = w_desc_eol;
			w_desc_fifo_wr_data[2] = w_desc_eod;
			w_desc_fifo_wr_data[1-:2] = w_desc_type;
		end
	end
	assign ar_valid = (r_current_state == 3'b001) && !r_axi_read_active;
	assign ar_addr = r_axi_read_addr;
	assign ar_len = 8'h00;
	assign ar_size = 3'b110;
	assign ar_burst = 2'b01;
	assign ar_id = {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, CHANNEL_ID[CHAN_WIDTH - 1:0]};
	assign ar_lock = 1'b0;
	assign ar_cache = 4'b0010;
	assign ar_prot = 3'b000;
	assign ar_qos = 4'h0;
	assign ar_region = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [63:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [2:0] protocol;
		input reg [3:0] event_code;
		input reg [5:0] channel_id;
		input reg [3:0] unit_id;
		input reg [7:0] agent_id;
		input reg [34:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
	endfunction
	always @(posedge clk)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
			case (r_current_state)
				3'b011: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, 4'h0, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, r_axi_read_addr[34:0]);
				end
				3'b100: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 3'b100, 4'h6, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {16'h0000, r_axi_read_resp, 17'h00000});
				end
				default:
					;
			endcase
		end
	wire w_channel_idle_falling = r_channel_idle_prev && !channel_idle;
	always @(posedge clk)
		if (!rst_n) begin
			r_apb_ip <= 1'b0;
			r_channel_idle_prev <= 1'b1;
		end
		else begin
			r_channel_idle_prev <= channel_idle;
			if (w_apb_skid_valid_in && w_apb_skid_ready_in)
				r_apb_ip <= 1'b1;
			else if (w_channel_idle_falling && r_apb_ip)
				r_apb_ip <= 1'b0;
		end
	assign descriptor_valid = w_desc_fifo_rd_valid && !r_descriptor_error;
	assign descriptor_packet = w_desc_fifo_rd_data[260-:256];
	assign descriptor_error = r_descriptor_error;
	assign descriptor_eos = w_desc_fifo_rd_data[4];
	assign descriptor_eol = w_desc_fifo_rd_data[3];
	assign descriptor_eod = w_desc_fifo_rd_data[2];
	assign descriptor_type = w_desc_fifo_rd_data[1-:2];
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	initial _sv2v_0 = 0;
endmodule
