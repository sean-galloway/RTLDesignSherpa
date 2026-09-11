module counter_bin_load (
	clk,
	rst_n,
	enable,
	add_enable,
	add_value,
	load,
	load_value,
	counter_bin_curr,
	counter_bin_next
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 5;
	parameter signed [31:0] MAX = 10;
	input wire clk;
	input wire rst_n;
	input wire enable;
	input wire add_enable;
	input wire [WIDTH - 1:0] add_value;
	input wire load;
	input wire [WIDTH - 1:0] load_value;
	output reg [WIDTH - 1:0] counter_bin_curr;
	output reg [WIDTH - 1:0] counter_bin_next;
	localparam signed [31:0] WRAP_BOUNDARY = 2 * MAX;
	wire [WIDTH - 2:0] w_max_val;
	function automatic signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] sv2v_cast_00F62_signed;
		input reg signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] inp;
		sv2v_cast_00F62_signed = inp;
	endfunction
	assign w_max_val = sv2v_cast_00F62_signed(MAX - 1);
	reg [WIDTH:0] w_sum_ext;
	function automatic signed [((WIDTH + 0) >= 0 ? WIDTH + 1 : 1 - (WIDTH + 0)) - 1:0] sv2v_cast_5A5B2_signed;
		input reg signed [((WIDTH + 0) >= 0 ? WIDTH + 1 : 1 - (WIDTH + 0)) - 1:0] inp;
		sv2v_cast_5A5B2_signed = inp;
	endfunction
	function automatic signed [WIDTH - 1:0] sv2v_cast_6B8D6_signed;
		input reg signed [WIDTH - 1:0] inp;
		sv2v_cast_6B8D6_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		counter_bin_next = counter_bin_curr;
		w_sum_ext = 1'sb0;
		if (load)
			counter_bin_next = load_value;
		else if (add_enable) begin
			w_sum_ext = {1'b0, counter_bin_curr} + {1'b0, add_value};
			if (w_sum_ext >= sv2v_cast_5A5B2_signed(WRAP_BOUNDARY))
				counter_bin_next = w_sum_ext[WIDTH - 1:0] - sv2v_cast_6B8D6_signed(WRAP_BOUNDARY);
			else
				counter_bin_next = w_sum_ext[WIDTH - 1:0];
		end
		else if (enable) begin
			if (counter_bin_curr[WIDTH - 2:0] == w_max_val)
				counter_bin_next = {~counter_bin_curr[WIDTH - 1], {WIDTH - 1 {1'b0}}};
			else
				counter_bin_next = counter_bin_curr + 1;
		end
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
module gaxi_drop_fifo_sync (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_ready,
	count,
	rd_valid,
	rd_data,
	drop_valid,
	drop_ready,
	drop_count,
	drop_all
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
	output reg [DW - 1:0] rd_data;
	input wire drop_valid;
	output wire drop_ready;
	input wire [AW:0] drop_count;
	input wire drop_all;
	reg [1:0] r_drop_state;
	reg [1:0] w_drop_state_next;
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
	wire w_drop_active;
	wire w_use_drop_ptr;
	reg [DW - 1:0] w_rd_data;
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_drop_state <= 2'b00;
		else
			r_drop_state <= w_drop_state_next;
	always @(*) begin
		if (_sv2v_0)
			;
		w_drop_state_next = r_drop_state;
		case (r_drop_state)
			2'b00:
				if (drop_valid)
					w_drop_state_next = 2'b01;
			2'b01: w_drop_state_next = 2'b10;
			2'b10: w_drop_state_next = 2'b11;
			2'b11:
				if (!drop_valid)
					w_drop_state_next = 2'b00;
			default: w_drop_state_next = 2'b00;
		endcase
	end
	assign w_drop_active = (r_drop_state == 2'b01) || (r_drop_state == 2'b10);
	assign w_use_drop_ptr = r_drop_state == 2'b01;
	assign drop_ready = r_drop_state == 2'b11;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk)
		if ((((axi_aresetn && (r_drop_state == 2'b00)) && drop_valid) && !drop_all) && (sv2v_cast_32(drop_count) > sv2v_cast_32(count)))
			$display("Error [%0t] /tmp/claude-1000/defork_gaxi_drop_fifo_sync/gaxi_drop_fifo_sync.sv:270:13 - gaxi_drop_fifo_sync.<unnamed_block>.<unnamed_block>\n msg: ", $time, "gaxi_drop_fifo_sync: drop_count=%0d exceeds occupancy count=%0d -- read pointer will overrun and count will wrap", drop_count, count);
	wire w_write;
	wire w_wr_load;
	assign w_write = wr_valid && wr_ready;
	assign w_wr_load = w_use_drop_ptr && drop_all;
	localparam signed [31:0] sv2v_uu_write_pointer_inst_WIDTH = AW + 1;
	localparam [sv2v_uu_write_pointer_inst_WIDTH - 1:0] sv2v_uu_write_pointer_inst_ext_add_value_0 = 1'sb0;
	counter_bin_load #(
		.WIDTH(AW + 1),
		.MAX(D)
	) write_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_write && !r_wr_full),
		.add_enable(1'b0),
		.add_value(sv2v_uu_write_pointer_inst_ext_add_value_0),
		.load(w_wr_load),
		.load_value(r_wr_ptr_bin),
		.counter_bin_curr(r_wr_ptr_bin),
		.counter_bin_next(w_wr_ptr_bin_next)
	);
	wire w_read;
	wire w_rd_add_enable;
	wire w_rd_load;
	assign w_read = rd_valid && rd_ready;
	assign w_rd_add_enable = w_use_drop_ptr && !drop_all;
	assign w_rd_load = w_use_drop_ptr && drop_all;
	counter_bin_load #(
		.WIDTH(AW + 1),
		.MAX(D)
	) read_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_read && !r_rd_empty),
		.add_enable(w_rd_add_enable),
		.add_value(drop_count),
		.load(w_rd_load),
		.load_value(r_wr_ptr_bin),
		.counter_bin_curr(r_rd_ptr_bin),
		.counter_bin_next(w_rd_ptr_bin_next)
	);
	wire [AW:0] w_rd_ptr_selected;
	assign w_rd_ptr_selected = w_rd_ptr_bin_next;
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
		.wdom_rd_ptr_bin(w_rd_ptr_selected),
		.rd_ptr_bin(w_rd_ptr_selected),
		.rdom_wr_ptr_bin(w_wr_ptr_bin_next),
		.count(count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full && !w_drop_active;
	assign rd_valid = !r_rd_empty && !w_drop_active;
	assign r_wr_addr = r_wr_ptr_bin[AW - 1:0];
	assign r_rd_addr = r_rd_ptr_bin[AW - 1:0];
	generate
		if (MEM_STYLE == 32'sd1) begin : gen_srl
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			always @(*) begin
				if (_sv2v_0)
					;
				w_rd_data = mem[r_rd_addr];
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
			wire [DW:1] sv2v_tmp_7B1E8;
			assign sv2v_tmp_7B1E8 = r_rd_data;
			always @(*) w_rd_data = sv2v_tmp_7B1E8;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			always @(*) begin
				if (_sv2v_0)
					;
				w_rd_data = mem[r_rd_addr];
			end
		end
		if (REGISTERED != 0) begin : gen_flop_mode
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					rd_data <= 'b0;
				else
					rd_data <= w_rd_data;
		end
		else begin : gen_mux_mode
			wire [DW:1] sv2v_tmp_2F913;
			assign sv2v_tmp_2F913 = w_rd_data;
			always @(*) rd_data = sv2v_tmp_2F913;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
