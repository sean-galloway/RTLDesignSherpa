module axi_split_combi (
	aclk,
	aresetn,
	current_addr,
	current_len,
	ax_size,
	alignment_mask,
	is_idle_state,
	transaction_valid,
	split_required,
	split_len,
	next_boundary_addr,
	remaining_len_after_split,
	new_split_needed
);
	parameter signed [31:0] AW = 32;
	parameter signed [31:0] DW = 32;
	input wire aclk;
	input wire aresetn;
	input wire [AW - 1:0] current_addr;
	input wire [7:0] current_len;
	input wire [2:0] ax_size;
	input wire [11:0] alignment_mask;
	input wire is_idle_state;
	input wire transaction_valid;
	output wire split_required;
	output wire [7:0] split_len;
	output wire [AW - 1:0] next_boundary_addr;
	output wire [7:0] remaining_len_after_split;
	output wire new_split_needed;
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] LOG2_BYTES_PER_BEAT = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] EXPECTED_AX_SIZE = LOG2_BYTES_PER_BEAT;
	function automatic signed [AW - 1:0] sv2v_cast_DE851_signed;
		input reg signed [AW - 1:0] inp;
		sv2v_cast_DE851_signed = inp;
	endfunction
	localparam [AW - 1:0] ADDR_ALIGN_MASK = sv2v_cast_DE851_signed(BYTES_PER_BEAT - 1);
	wire [AW - 1:0] total_bytes;
	wire [AW - 1:0] transaction_end_addr;
	wire [AW - 1:0] bytes_to_boundary;
	wire [AW - 1:0] beats_to_boundary;
	function automatic [AW - 1:0] sv2v_cast_DE851;
		input reg [AW - 1:0] inp;
		sv2v_cast_DE851 = inp;
	endfunction
	assign total_bytes = (sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1)) << ax_size;
	assign transaction_end_addr = (current_addr + total_bytes) - sv2v_cast_DE851_signed(1);
	assign next_boundary_addr = (current_addr | sv2v_cast_DE851(alignment_mask)) + sv2v_cast_DE851_signed(1);
	assign bytes_to_boundary = next_boundary_addr - current_addr;
	assign beats_to_boundary = bytes_to_boundary >> ax_size;
	wire crosses_boundary;
	wire has_beats_before_boundary;
	wire beats_fit_before_boundary;
	assign crosses_boundary = transaction_end_addr >= next_boundary_addr;
	assign has_beats_before_boundary = beats_to_boundary > 0;
	assign beats_fit_before_boundary = beats_to_boundary <= (sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1));
	assign split_required = (crosses_boundary && has_beats_before_boundary) && beats_fit_before_boundary;
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign split_len = (split_required ? sv2v_cast_8(beats_to_boundary - sv2v_cast_DE851_signed(1)) : current_len);
	wire [AW - 1:0] split_beats_actual;
	wire [AW - 1:0] original_beats_total;
	wire [AW - 1:0] remaining_beats_actual;
	assign original_beats_total = sv2v_cast_DE851(current_len) + sv2v_cast_DE851_signed(1);
	assign split_beats_actual = (split_required ? beats_to_boundary : original_beats_total);
	assign remaining_beats_actual = (split_required ? original_beats_total - split_beats_actual : sv2v_cast_DE851_signed(0));
	assign remaining_len_after_split = (split_required ? (remaining_beats_actual > 0 ? sv2v_cast_8(remaining_beats_actual - sv2v_cast_DE851_signed(1)) : 8'sd0) : 8'sd0);
	assign new_split_needed = (split_required && is_idle_state) && transaction_valid;
	always @(posedge aclk)
		if ((aresetn && transaction_valid) && is_idle_state)
			;
	always @(posedge aclk)
		if (aresetn && transaction_valid) begin
			if (split_required)
				;
		end
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
	parameter signed [31:0] DEPTH = 8;
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
			always @(posedge rd_clk or negedge rd_rst_n)
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
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			reg [DATA_WIDTH - 1:0] r_rd_data;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_rd_data <= 1'sb0;
				else
					r_rd_data <= mem[r_rd_addr];
			assign rd_data = r_rd_data;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
	endgenerate
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
endmodule
module axi_master_rd_splitter (
	aclk,
	aresetn,
	alignment_mask,
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
	m_axi_rready,
	block_ready,
	fub_arid,
	fub_araddr,
	fub_arlen,
	fub_arsize,
	fub_arburst,
	fub_arlock,
	fub_arcache,
	fub_arprot,
	fub_arqos,
	fub_arregion,
	fub_aruser,
	fub_arvalid,
	fub_arready,
	fub_rid,
	fub_rdata,
	fub_rresp,
	fub_rlast,
	fub_ruser,
	fub_rvalid,
	fub_rready,
	fub_split_addr,
	fub_split_id,
	fub_split_cnt,
	fub_split_valid,
	o_split_fifo_overflow,
	fub_split_ready
);
	reg _sv2v_0;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] SPLIT_FIFO_DEPTH = 4;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [11:0] alignment_mask;
	output reg [IW - 1:0] m_axi_arid;
	output reg [AW - 1:0] m_axi_araddr;
	output reg [7:0] m_axi_arlen;
	output reg [2:0] m_axi_arsize;
	output reg [1:0] m_axi_arburst;
	output reg m_axi_arlock;
	output reg [3:0] m_axi_arcache;
	output reg [2:0] m_axi_arprot;
	output reg [3:0] m_axi_arqos;
	output reg [3:0] m_axi_arregion;
	output reg [UW - 1:0] m_axi_aruser;
	output reg m_axi_arvalid;
	input wire m_axi_arready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire [UW - 1:0] m_axi_ruser;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	input wire block_ready;
	input wire [IW - 1:0] fub_arid;
	input wire [AW - 1:0] fub_araddr;
	input wire [7:0] fub_arlen;
	input wire [2:0] fub_arsize;
	input wire [1:0] fub_arburst;
	input wire fub_arlock;
	input wire [3:0] fub_arcache;
	input wire [2:0] fub_arprot;
	input wire [3:0] fub_arqos;
	input wire [3:0] fub_arregion;
	input wire [UW - 1:0] fub_aruser;
	input wire fub_arvalid;
	output reg fub_arready;
	output wire [IW - 1:0] fub_rid;
	output wire [DW - 1:0] fub_rdata;
	output wire [1:0] fub_rresp;
	output wire fub_rlast;
	output wire [UW - 1:0] fub_ruser;
	output wire fub_rvalid;
	input wire fub_rready;
	output wire [AW - 1:0] fub_split_addr;
	output wire [IW - 1:0] fub_split_id;
	output wire [7:0] fub_split_cnt;
	output wire fub_split_valid;
	output wire o_split_fifo_overflow;
	input wire fub_split_ready;
	reg r_split_fifo_overflow;
	assign o_split_fifo_overflow = r_split_fifo_overflow;
	reg [1:0] r_split_state;
	reg [IW - 1:0] r_orig_arid;
	reg [AW - 1:0] r_orig_araddr;
	reg [7:0] r_orig_arlen;
	reg [2:0] r_orig_arsize;
	reg [1:0] r_orig_arburst;
	reg r_orig_arlock;
	reg [3:0] r_orig_arcache;
	reg [2:0] r_orig_arprot;
	reg [3:0] r_orig_arqos;
	reg [3:0] r_orig_arregion;
	reg [UW - 1:0] r_orig_aruser;
	reg [AW - 1:0] r_current_addr;
	reg [7:0] r_current_len;
	reg [7:0] r_split_count;
	reg [AW - 1:0] w_current_addr;
	reg [7:0] w_current_len;
	reg [2:0] w_current_size;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r_split_state == 2'b01) begin
			w_current_addr = fub_araddr;
			w_current_len = fub_arlen;
			w_current_size = fub_arsize;
		end
		else begin
			w_current_addr = r_current_addr;
			w_current_len = r_current_len;
			w_current_size = r_orig_arsize;
		end
	end
	wire w_split_required;
	wire [7:0] w_split_len;
	wire [AW - 1:0] w_next_boundary_addr;
	wire [7:0] w_remaining_len_after_split;
	wire w_new_split_needed;
	axi_split_combi #(
		.AW(AW),
		.DW(DW)
	) inst_axi_split_combi(
		.aclk(aclk),
		.aresetn(aresetn),
		.current_addr(w_current_addr),
		.current_len(w_current_len),
		.ax_size(w_current_size),
		.alignment_mask(alignment_mask),
		.is_idle_state(r_split_state == 2'b01),
		.transaction_valid(fub_arvalid),
		.split_required(w_split_required),
		.split_len(w_split_len),
		.next_boundary_addr(w_next_boundary_addr),
		.remaining_len_after_split(w_remaining_len_after_split),
		.new_split_needed(w_new_split_needed)
	);
	wire w_is_final_split;
	assign w_is_final_split = (r_split_state == 2'b10) && !w_split_required;
	reg [8:0] r_rbeats_remaining;
	reg r_rbeats_active;
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_rbeats_remaining <= 9'd0;
			r_rbeats_active <= 1'b0;
			r_split_state <= 2'b01;
			r_current_addr <= 1'sb0;
			r_current_len <= 1'sb0;
			r_split_count <= 8'd0;
			r_orig_arid <= 1'sb0;
			r_orig_araddr <= 1'sb0;
			r_orig_arlen <= 1'sb0;
			r_orig_arsize <= 1'sb0;
			r_orig_arburst <= 1'sb0;
			r_orig_arlock <= 1'sb0;
			r_orig_arcache <= 1'sb0;
			r_orig_arprot <= 1'sb0;
			r_orig_arqos <= 1'sb0;
			r_orig_arregion <= 1'sb0;
			r_orig_aruser <= 1'sb0;
		end
		else begin
			if ((r_rbeats_active && fub_rvalid) && fub_rready) begin
				r_rbeats_remaining <= r_rbeats_remaining - 9'd1;
				if (r_rbeats_remaining == 9'd1)
					r_rbeats_active <= 1'b0;
			end
			case (r_split_state)
				2'b01:
					if (((fub_arvalid && m_axi_arready) && !block_ready) && !r_rbeats_active) begin
						r_rbeats_remaining <= sv2v_cast_9(fub_arlen) + 9'd1;
						r_rbeats_active <= 1'b1;
						r_orig_arid <= fub_arid;
						r_orig_araddr <= fub_araddr;
						r_orig_arlen <= fub_arlen;
						r_orig_arsize <= fub_arsize;
						r_orig_arburst <= fub_arburst;
						r_orig_arlock <= fub_arlock;
						r_orig_arcache <= fub_arcache;
						r_orig_arprot <= fub_arprot;
						r_orig_arqos <= fub_arqos;
						r_orig_arregion <= fub_arregion;
						r_orig_aruser <= fub_aruser;
						if (w_new_split_needed) begin
							r_split_state <= 2'b10;
							r_current_addr <= w_next_boundary_addr;
							r_current_len <= w_remaining_len_after_split;
							r_split_count <= 8'd2;
						end
					end
				2'b10:
					if (m_axi_arvalid && m_axi_arready) begin
						if (w_split_required) begin
							r_current_addr <= w_next_boundary_addr;
							r_current_len <= w_remaining_len_after_split;
							r_split_count <= r_split_count + 8'd1;
						end
						else begin
							r_split_state <= 2'b01;
							r_split_count <= 8'd0;
						end
					end
				default: r_split_state <= 2'b01;
			endcase
		end
	always @(*) begin
		if (_sv2v_0)
			;
		m_axi_araddr = w_current_addr;
		m_axi_arlen = (w_split_required ? w_split_len : w_current_len);
		if (r_split_state == 2'b01) begin
			m_axi_arid = fub_arid;
			m_axi_arsize = fub_arsize;
			m_axi_arburst = fub_arburst;
			m_axi_arlock = fub_arlock;
			m_axi_arcache = fub_arcache;
			m_axi_arprot = fub_arprot;
			m_axi_arqos = fub_arqos;
			m_axi_arregion = fub_arregion;
			m_axi_aruser = fub_aruser;
		end
		else begin
			m_axi_arid = r_orig_arid;
			m_axi_arsize = r_orig_arsize;
			m_axi_arburst = r_orig_arburst;
			m_axi_arlock = r_orig_arlock;
			m_axi_arcache = r_orig_arcache;
			m_axi_arprot = r_orig_arprot;
			m_axi_arqos = r_orig_arqos;
			m_axi_arregion = r_orig_arregion;
			m_axi_aruser = r_orig_aruser;
		end
		case (r_split_state)
			2'b01: m_axi_arvalid = (fub_arvalid && !block_ready) && !r_rbeats_active;
			2'b10: m_axi_arvalid = 1'b1;
			default: m_axi_arvalid = 1'b0;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		case (r_split_state)
			2'b01:
				if (w_new_split_needed)
					fub_arready = 1'b0;
				else
					fub_arready = (m_axi_arready && !block_ready) && !r_rbeats_active;
			2'b10: fub_arready = (w_is_final_split && m_axi_arready) && !block_ready;
			default: fub_arready = 1'b0;
		endcase
	end
	assign fub_rid = m_axi_rid;
	assign fub_rdata = m_axi_rdata;
	assign fub_rresp = m_axi_rresp;
	assign fub_ruser = m_axi_ruser;
	assign fub_rvalid = m_axi_rvalid;
	assign fub_rlast = (r_rbeats_active ? r_rbeats_remaining == 9'd1 : m_axi_rlast);
	assign m_axi_rready = fub_rready;
	reg [(AW + IW) + 7:0] split_fifo_din;
	wire w_split_fifo_valid;
	wire w_split_fifo_ready;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_split_fifo_overflow <= 1'b0;
		else if (w_split_fifo_valid && !w_split_fifo_ready)
			r_split_fifo_overflow <= 1'b1;
	assign w_split_fifo_valid = fub_arvalid && fub_arready;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r_split_state == 2'b01)
			split_fifo_din = {fub_araddr, fub_arid, (w_new_split_needed ? 8'd2 : 8'd1)};
		else
			split_fifo_din = {r_orig_araddr, r_orig_arid, r_split_count};
	end
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH((AW + IW) + 8),
		.DEPTH(SPLIT_FIFO_DEPTH)
	) inst_split_info_fifo(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(w_split_fifo_valid),
		.wr_data(split_fifo_din),
		.rd_ready(fub_split_ready),
		.rd_valid(fub_split_valid),
		.rd_data({fub_split_addr, fub_split_id, fub_split_cnt}),
		.wr_ready(w_split_fifo_ready),
		.count()
	);
	always @(posedge aclk)
		if (aresetn) begin
			if (((r_split_state == 2'b01) && fub_arvalid) && w_new_split_needed)
				;
			if ((r_split_state == 2'b10) && !w_is_final_split)
				;
			if (r_split_state == 2'b10)
				;
			if (w_split_fifo_valid)
				;
		end
	initial _sv2v_0 = 0;
endmodule
