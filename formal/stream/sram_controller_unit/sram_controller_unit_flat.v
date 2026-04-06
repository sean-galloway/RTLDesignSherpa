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
module stream_alloc_ctrl (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_size,
	wr_ready,
	rd_valid,
	rd_ready,
	space_free,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] DEPTH = 512;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 1;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(D);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	input wire [7:0] wr_size;
	output wire wr_ready;
	input wire rd_valid;
	output wire rd_ready;
	output wire [AW:0] space_free;
	output wire wr_full;
	output wire wr_almost_full;
	output wire rd_empty;
	output wire rd_almost_empty;
	reg [AW:0] r_wr_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire [AW:0] w_count;
	wire w_write;
	wire w_read;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	function automatic [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65;
		input reg [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65 = inp;
	endfunction
	always @(posedge axi_aclk)
		if (!axi_aresetn)
			r_wr_ptr_bin <= 1'sb0;
		else if (w_write && !r_wr_full)
			r_wr_ptr_bin <= r_wr_ptr_bin + sv2v_cast_2BB65(wr_size);
	assign w_wr_ptr_bin_next = r_wr_ptr_bin + (w_write && !r_wr_full ? sv2v_cast_2BB65(wr_size) : {(AW >= 0 ? AW + 1 : 1 - AW) {1'sb0}});
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
		.count(w_count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_ready = !r_rd_empty;
	function automatic signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65_signed;
		input reg signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65_signed = inp;
	endfunction
	assign space_free = sv2v_cast_2BB65_signed(D) - w_count;
	assign wr_full = r_wr_full;
	assign wr_almost_full = r_wr_almost_full;
	assign rd_empty = r_rd_empty;
	assign rd_almost_empty = r_rd_almost_empty;
endmodule
module stream_drain_ctrl (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	rd_valid,
	rd_size,
	rd_ready,
	data_available,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] DEPTH = 512;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 1;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(D);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire rd_valid;
	input wire [7:0] rd_size;
	output wire rd_ready;
	output wire [AW:0] data_available;
	output wire wr_full;
	output wire wr_almost_full;
	output wire rd_empty;
	output wire rd_almost_empty;
	wire [AW:0] r_wr_ptr_bin;
	reg [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire [AW:0] w_count;
	wire [AW:0] w_available_data;
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
	function automatic [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65;
		input reg [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65 = inp;
	endfunction
	always @(posedge axi_aclk)
		if (!axi_aresetn)
			r_rd_ptr_bin <= 1'sb0;
		else if (w_read && !r_rd_empty)
			r_rd_ptr_bin <= r_rd_ptr_bin + sv2v_cast_2BB65(rd_size);
	assign w_rd_ptr_bin_next = r_rd_ptr_bin + (w_read && !r_rd_empty ? sv2v_cast_2BB65(rd_size) : {(AW >= 0 ? AW + 1 : 1 - AW) {1'sb0}});
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
		.count(w_count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_ready = !r_rd_empty;
	assign data_available = w_count;
	assign wr_full = r_wr_full;
	assign wr_almost_full = r_wr_almost_full;
	assign rd_empty = r_rd_empty;
	assign rd_almost_empty = r_rd_almost_empty;
endmodule
module stream_latency_bridge (
	clk,
	rst_n,
	s_valid,
	s_ready,
	s_data,
	m_valid,
	m_ready,
	m_data,
	occupancy,
	dbg_r_pending,
	dbg_r_out_valid
);
	parameter signed [31:0] DATA_WIDTH = 64;
	parameter signed [31:0] SKID_DEPTH = 4;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire s_valid;
	output wire s_ready;
	input wire [DW - 1:0] s_data;
	output wire m_valid;
	input wire m_ready;
	output wire [DW - 1:0] m_data;
	output wire [2:0] occupancy;
	output wire dbg_r_pending;
	output wire dbg_r_out_valid;
	reg r_drain_ip;
	wire skid_wr_valid;
	wire skid_wr_ready;
	wire [DW - 1:0] skid_wr_data;
	wire [$clog2(SKID_DEPTH):0] skid_count;
	wire w_draining_now = m_valid && m_ready;
	wire w_write_stalled = skid_wr_valid && !skid_wr_ready;
	wire [2:0] pending_count = skid_count + {2'b00, w_write_stalled};
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	wire w_room_available = pending_count < sv2v_cast_3_signed(SKID_DEPTH);
	assign s_ready = w_room_available || w_draining_now;
	wire w_drain_fifo = s_valid && s_ready;
	always @(posedge clk)
		if (!rst_n)
			r_drain_ip <= 1'b0;
		else
			r_drain_ip <= w_drain_fifo;
	assign skid_wr_valid = r_drain_ip;
	assign skid_wr_data = s_data;
	gaxi_fifo_sync #(
		.MEM_STYLE(32'sd0),
		.REGISTERED(0),
		.DATA_WIDTH(DW),
		.DEPTH(SKID_DEPTH)
	) u_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(skid_wr_valid),
		.wr_ready(skid_wr_ready),
		.wr_data(skid_wr_data),
		.rd_valid(m_valid),
		.rd_ready(m_ready),
		.rd_data(m_data),
		.count(skid_count)
	);
	assign occupancy = skid_count;
	assign dbg_r_pending = r_drain_ip;
	assign dbg_r_out_valid = m_valid;
endmodule
module sram_controller_unit (
	clk,
	rst_n,
	axi_rd_alloc_req,
	axi_rd_alloc_size,
	axi_rd_alloc_space_free,
	axi_rd_sram_valid,
	axi_rd_sram_ready,
	axi_rd_sram_data,
	axi_wr_drain_data_avail,
	axi_wr_drain_req,
	axi_wr_drain_size,
	axi_wr_sram_valid,
	axi_wr_sram_ready,
	axi_wr_sram_data,
	dbg_bridge_pending,
	dbg_bridge_out_valid
);
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire axi_rd_alloc_req;
	input wire [7:0] axi_rd_alloc_size;
	output reg [SCW - 1:0] axi_rd_alloc_space_free;
	input wire axi_rd_sram_valid;
	output wire axi_rd_sram_ready;
	input wire [DW - 1:0] axi_rd_sram_data;
	output wire [SCW - 1:0] axi_wr_drain_data_avail;
	input wire axi_wr_drain_req;
	input wire [7:0] axi_wr_drain_size;
	output wire axi_wr_sram_valid;
	input wire axi_wr_sram_ready;
	output wire [DW - 1:0] axi_wr_sram_data;
	output wire dbg_bridge_pending;
	output wire dbg_bridge_out_valid;
	localparam signed [31:0] ADDR_WIDTH = $clog2(SD);
	wire [ADDR_WIDTH:0] alloc_space_free;
	wire [ADDR_WIDTH:0] drain_data_available;
	wire fifo_rd_valid_internal;
	wire fifo_rd_ready_internal;
	wire [DW - 1:0] fifo_rd_data_internal;
	wire [ADDR_WIDTH:0] fifo_count;
	wire fifo_empty;
	wire fifo_full;
	wire [2:0] bridge_occupancy;
	stream_alloc_ctrl #(
		.DEPTH(SD),
		.REGISTERED(1)
	) u_alloc_ctrl(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_alloc_req),
		.wr_size(axi_rd_alloc_size),
		.wr_ready(),
		.rd_valid(axi_wr_sram_valid && axi_wr_sram_ready),
		.rd_ready(),
		.space_free(alloc_space_free),
		.wr_full(),
		.wr_almost_full(),
		.rd_empty(),
		.rd_almost_empty()
	);
	stream_drain_ctrl #(
		.DEPTH(SD),
		.REGISTERED(1)
	) u_drain_ctrl(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_sram_valid && axi_rd_sram_ready),
		.wr_ready(),
		.rd_valid(axi_wr_drain_req),
		.rd_size(axi_wr_drain_size),
		.rd_ready(),
		.data_available(drain_data_available),
		.wr_full(),
		.wr_almost_full(),
		.rd_empty(),
		.rd_almost_empty()
	);
	gaxi_fifo_sync #(
		.MEM_STYLE(32'sd0),
		.REGISTERED(1),
		.DATA_WIDTH(DW),
		.DEPTH(SD)
	) u_channel_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_sram_valid),
		.wr_ready(axi_rd_sram_ready),
		.wr_data(axi_rd_sram_data),
		.rd_valid(fifo_rd_valid_internal),
		.rd_ready(fifo_rd_ready_internal),
		.rd_data(fifo_rd_data_internal),
		.count(fifo_count)
	);
	stream_latency_bridge #(.DATA_WIDTH(DW)) u_latency_bridge(
		.clk(clk),
		.rst_n(rst_n),
		.s_data(fifo_rd_data_internal),
		.s_valid(fifo_rd_valid_internal),
		.s_ready(fifo_rd_ready_internal),
		.m_data(axi_wr_sram_data),
		.m_valid(axi_wr_sram_valid),
		.m_ready(axi_wr_sram_ready),
		.occupancy(bridge_occupancy),
		.dbg_r_pending(dbg_bridge_pending),
		.dbg_r_out_valid(dbg_bridge_out_valid)
	);
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	assign axi_wr_drain_data_avail = drain_data_available + sv2v_cast_14961(bridge_occupancy);
	function automatic signed [SCW - 1:0] sv2v_cast_14961_signed;
		input reg signed [SCW - 1:0] inp;
		sv2v_cast_14961_signed = inp;
	endfunction
	always @(posedge clk)
		if (!rst_n)
			axi_rd_alloc_space_free <= sv2v_cast_14961_signed(SD);
		else
			axi_rd_alloc_space_free <= alloc_space_free;
endmodule
