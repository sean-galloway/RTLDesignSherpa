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
module scoria_rd_cmd_cam (
	aclk,
	aresetn,
	ins_valid_i,
	ins_ready_o,
	ins_bank_i,
	ins_row_i,
	ins_col_i,
	ins_id_i,
	ins_qos_i,
	ins_ticket_i,
	sched_lu_valid_i,
	sched_lu_bank_i,
	sched_lu_row_i,
	sched_lu_hit_o,
	sched_lu_slot_o,
	sched_lu_col_o,
	sched_lu_id_o,
	sched_lu_age_o,
	sch_valid_o,
	sch_bank_o,
	sch_row_o,
	sch_col_o,
	sch_older_o,
	age_thresh_i,
	sch_age_exceed_o,
	sch_qos_o,
	sch_head_rel_o,
	oldest_valid_o,
	oldest_bank_o,
	oldest_row_o,
	oldest_col_o,
	oldest_id_o,
	oldest_slot_o,
	issue_valid_i,
	issue_ready_o,
	issue_slot_i,
	iss_valid_o,
	iss_ready_i,
	iss_ticket_o,
	busy_o
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_ENTRIES = 8;
	parameter signed [31:0] N_SCHED_LU = 4;
	parameter signed [31:0] NUM_BANKS = 8;
	parameter signed [31:0] ROW_WIDTH = 14;
	parameter signed [31:0] COL_WIDTH = 10;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AGE_WIDTH = 16;
	parameter signed [31:0] RD_RET_DEPTH = 32;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] BKW = $clog2(NUM_BANKS);
	parameter signed [31:0] PTRW = $clog2(NUM_ENTRIES);
	parameter signed [31:0] TW = $clog2(RD_RET_DEPTH);
	input wire aclk;
	input wire aresetn;
	input wire ins_valid_i;
	output wire ins_ready_o;
	input wire [BKW - 1:0] ins_bank_i;
	input wire [ROW_WIDTH - 1:0] ins_row_i;
	input wire [COL_WIDTH - 1:0] ins_col_i;
	input wire [IW - 1:0] ins_id_i;
	input wire [3:0] ins_qos_i;
	input wire [TW - 1:0] ins_ticket_i;
	input wire [N_SCHED_LU - 1:0] sched_lu_valid_i;
	input wire [(N_SCHED_LU * BKW) - 1:0] sched_lu_bank_i;
	input wire [(N_SCHED_LU * ROW_WIDTH) - 1:0] sched_lu_row_i;
	output reg [N_SCHED_LU - 1:0] sched_lu_hit_o;
	output reg [(N_SCHED_LU * PTRW) - 1:0] sched_lu_slot_o;
	output reg [(N_SCHED_LU * COL_WIDTH) - 1:0] sched_lu_col_o;
	output reg [(N_SCHED_LU * IW) - 1:0] sched_lu_id_o;
	output reg [(N_SCHED_LU * AGE_WIDTH) - 1:0] sched_lu_age_o;
	output reg [NUM_ENTRIES - 1:0] sch_valid_o;
	output reg [(NUM_ENTRIES * BKW) - 1:0] sch_bank_o;
	output reg [(NUM_ENTRIES * ROW_WIDTH) - 1:0] sch_row_o;
	output reg [(NUM_ENTRIES * COL_WIDTH) - 1:0] sch_col_o;
	output reg [(NUM_ENTRIES * NUM_ENTRIES) - 1:0] sch_older_o;
	input wire [7:0] age_thresh_i;
	output reg [NUM_ENTRIES - 1:0] sch_age_exceed_o;
	output reg [(NUM_ENTRIES * 4) - 1:0] sch_qos_o;
	output reg [AGE_WIDTH - 1:0] sch_head_rel_o;
	output wire oldest_valid_o;
	output wire [BKW - 1:0] oldest_bank_o;
	output wire [ROW_WIDTH - 1:0] oldest_row_o;
	output wire [COL_WIDTH - 1:0] oldest_col_o;
	output wire [IW - 1:0] oldest_id_o;
	output wire [PTRW - 1:0] oldest_slot_o;
	input wire issue_valid_i;
	output wire issue_ready_o;
	input wire [PTRW - 1:0] issue_slot_i;
	output wire iss_valid_o;
	input wire iss_ready_i;
	output wire [TW - 1:0] iss_ticket_o;
	output reg busy_o;
	reg r_valid [0:NUM_ENTRIES - 1];
	reg [BKW - 1:0] r_bank [0:NUM_ENTRIES - 1];
	reg [ROW_WIDTH - 1:0] r_row [0:NUM_ENTRIES - 1];
	reg [COL_WIDTH - 1:0] r_col [0:NUM_ENTRIES - 1];
	reg [IW - 1:0] r_id [0:NUM_ENTRIES - 1];
	reg [3:0] r_qos [0:NUM_ENTRIES - 1];
	reg [TW - 1:0] r_ticket [0:NUM_ENTRIES - 1];
	reg [AGE_WIDTH - 1:0] r_age [0:NUM_ENTRIES - 1];
	reg [AGE_WIDTH - 1:0] r_age_ctr;
	reg [NUM_ENTRIES - 1:0] r_older [0:NUM_ENTRIES - 1];
	reg [AGE_WIDTH - 1:0] w_rel [0:NUM_ENTRIES - 1];
	reg [NUM_ENTRIES - 1:0] r_age_exceed;
	always @(*) begin : sv2v_autoblock_1
		reg signed [31:0] i;
		if (_sv2v_0)
			;
		for (i = 0; i < NUM_ENTRIES; i = i + 1)
			w_rel[i] = r_age_ctr - r_age[i];
	end
	reg w_have_free;
	reg [PTRW - 1:0] w_free_slot;
	function automatic signed [PTRW - 1:0] sv2v_cast_E6D00_signed;
		input reg signed [PTRW - 1:0] inp;
		sv2v_cast_E6D00_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_have_free = 1'b0;
		w_free_slot = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = NUM_ENTRIES - 1; i >= 0; i = i - 1)
				if (!r_valid[i]) begin
					w_have_free = 1'b1;
					w_free_slot = sv2v_cast_E6D00_signed(i);
				end
		end
	end
	wire w_ins_fire;
	assign ins_ready_o = w_have_free;
	assign w_ins_fire = ins_valid_i && ins_ready_o;
	wire w_issue_fire;
	assign issue_ready_o = iss_ready_i;
	assign w_issue_fire = issue_valid_i && issue_ready_o;
	assign iss_valid_o = issue_valid_i;
	assign iss_ticket_o = r_ticket[issue_slot_i];
	reg w_old_found;
	reg [PTRW - 1:0] w_old_slot;
	reg [AGE_WIDTH - 1:0] w_old_best;
	always @(*) begin
		if (_sv2v_0)
			;
		w_old_found = 1'b0;
		w_old_slot = 1'sb0;
		w_old_best = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				if (r_valid[i] && (!w_old_found || (w_rel[i] > w_old_best))) begin
					w_old_found = 1'b1;
					w_old_best = w_rel[i];
					w_old_slot = sv2v_cast_E6D00_signed(i);
				end
		end
	end
	assign oldest_valid_o = w_old_found;
	assign oldest_slot_o = w_old_slot;
	assign oldest_bank_o = r_bank[w_old_slot];
	assign oldest_row_o = r_row[w_old_slot];
	assign oldest_col_o = r_col[w_old_slot];
	assign oldest_id_o = r_id[w_old_slot];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg signed [31:0] j;
			for (j = 0; j < N_SCHED_LU; j = j + 1)
				begin : sv2v_autoblock_5
					reg found;
					reg [PTRW - 1:0] slot;
					reg [AGE_WIDTH - 1:0] best;
					reg [BKW - 1:0] qbank;
					reg [ROW_WIDTH - 1:0] qrow;
					found = 1'b0;
					slot = 1'sb0;
					best = 1'sb0;
					qbank = sched_lu_bank_i[j * BKW+:BKW];
					qrow = sched_lu_row_i[j * ROW_WIDTH+:ROW_WIDTH];
					begin : sv2v_autoblock_6
						reg signed [31:0] i;
						for (i = 0; i < NUM_ENTRIES; i = i + 1)
							if ((r_valid[i] && (r_bank[i] == qbank)) && (r_row[i] == qrow)) begin
								if (!found || (w_rel[i] > best)) begin
									found = 1'b1;
									best = w_rel[i];
									slot = sv2v_cast_E6D00_signed(i);
								end
							end
					end
					sched_lu_hit_o[j] = sched_lu_valid_i[j] && found;
					sched_lu_slot_o[j * PTRW+:PTRW] = slot;
					sched_lu_col_o[j * COL_WIDTH+:COL_WIDTH] = r_col[slot];
					sched_lu_id_o[j * IW+:IW] = r_id[slot];
					sched_lu_age_o[j * AGE_WIDTH+:AGE_WIDTH] = best;
				end
		end
	end
	reg w_sho_found;
	reg [PTRW - 1:0] w_sho_slot;
	always @(*) begin : sv2v_autoblock_7
		reg [NUM_ENTRIES - 1:0] w_sho_is;
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				begin : sv2v_autoblock_9
					reg ge_all;
					ge_all = 1'b1;
					begin : sv2v_autoblock_10
						reg signed [31:0] j;
						for (j = 0; j < NUM_ENTRIES; j = j + 1)
							if (((j != i) && r_valid[j]) && !r_older[i][j])
								ge_all = 1'b0;
					end
					w_sho_is[i] = r_valid[i] && ge_all;
				end
		end
		w_sho_found = |w_sho_is;
		w_sho_slot = 1'sb0;
		begin : sv2v_autoblock_11
			reg signed [31:0] i;
			for (i = NUM_ENTRIES - 1; i >= 0; i = i - 1)
				if (w_sho_is[i])
					w_sho_slot = sv2v_cast_E6D00_signed(i);
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_12
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				begin
					sch_valid_o[i] = r_valid[i];
					sch_bank_o[i * BKW+:BKW] = r_bank[i];
					sch_row_o[i * ROW_WIDTH+:ROW_WIDTH] = r_row[i];
					sch_col_o[i * COL_WIDTH+:COL_WIDTH] = r_col[i];
					sch_older_o[i * NUM_ENTRIES+:NUM_ENTRIES] = r_older[i];
					sch_qos_o[i * 4+:4] = r_qos[i];
					sch_age_exceed_o[i] = r_valid[i] && r_age_exceed[i];
				end
		end
		sch_head_rel_o = (w_sho_found ? w_rel[w_sho_slot] : {AGE_WIDTH {1'sb0}});
	end
	function automatic [AGE_WIDTH - 1:0] sv2v_cast_20586;
		input reg [AGE_WIDTH - 1:0] inp;
		sv2v_cast_20586 = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_age_exceed <= 1'sb0;
		else begin
			begin : sv2v_autoblock_13
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					r_age_exceed[i] <= (r_valid[i] && (age_thresh_i != 8'd0)) && (w_rel[i] >= sv2v_cast_20586({age_thresh_i, 4'h0}));
			end
			if (w_ins_fire)
				r_age_exceed[w_free_slot] <= 1'b0;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		busy_o = 1'b0;
		begin : sv2v_autoblock_14
			reg signed [31:0] i;
			for (i = 0; i < NUM_ENTRIES; i = i + 1)
				if (r_valid[i])
					busy_o = 1'b1;
		end
	end
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_age_ctr <= 1'sb0;
			begin : sv2v_autoblock_15
				reg signed [31:0] i;
				for (i = 0; i < NUM_ENTRIES; i = i + 1)
					begin
						r_valid[i] <= 1'b0;
						r_older[i] <= 1'sb0;
					end
			end
		end
		else begin
			r_age_ctr <= r_age_ctr + 1'b1;
			if (w_ins_fire) begin
				r_valid[w_free_slot] <= 1'b1;
				r_bank[w_free_slot] <= ins_bank_i;
				r_row[w_free_slot] <= ins_row_i;
				r_col[w_free_slot] <= ins_col_i;
				r_id[w_free_slot] <= ins_id_i;
				r_qos[w_free_slot] <= ins_qos_i;
				r_ticket[w_free_slot] <= ins_ticket_i;
				r_age[w_free_slot] <= r_age_ctr;
				begin : sv2v_autoblock_16
					reg signed [31:0] j;
					for (j = 0; j < NUM_ENTRIES; j = j + 1)
						begin
							r_older[w_free_slot][j] <= 1'b0;
							if (j != sv2v_cast_32_signed(w_free_slot))
								r_older[j][w_free_slot] <= 1'b1;
						end
				end
			end
			if (w_issue_fire)
				r_valid[issue_slot_i] <= 1'b0;
		end
	always @(posedge aclk)
		if (aresetn)
			;
	initial _sv2v_0 = 0;
endmodule
