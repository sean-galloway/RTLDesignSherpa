module cmdrsp_router (
	clk,
	rst_n,
	s_cmd_valid,
	s_cmd_ready,
	s_cmd_pwrite,
	s_cmd_paddr,
	s_cmd_pwdata,
	s_rsp_valid,
	s_rsp_ready,
	s_rsp_prdata,
	s_rsp_pslverr,
	m0_cmd_valid,
	m0_cmd_ready,
	m0_cmd_pwrite,
	m0_cmd_paddr,
	m0_cmd_pwdata,
	m0_rsp_valid,
	m0_rsp_ready,
	m0_rsp_prdata,
	m0_rsp_pslverr,
	m1_cmd_valid,
	m1_cmd_ready,
	m1_cmd_pwrite,
	m1_cmd_paddr,
	m1_cmd_pwdata,
	m1_rsp_valid,
	m1_rsp_ready,
	m1_rsp_prdata,
	m1_rsp_pslverr,
	perf_cfg_enable,
	perf_cfg_mode,
	perf_cfg_clear,
	perf_fifo_data_low,
	perf_fifo_data_high,
	perf_fifo_empty,
	perf_fifo_full,
	perf_fifo_count,
	perf_fifo_rd
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 12;
	parameter signed [31:0] DATA_WIDTH = 32;
	input wire clk;
	input wire rst_n;
	input wire s_cmd_valid;
	output wire s_cmd_ready;
	input wire s_cmd_pwrite;
	input wire [ADDR_WIDTH - 1:0] s_cmd_paddr;
	input wire [DATA_WIDTH - 1:0] s_cmd_pwdata;
	output wire s_rsp_valid;
	input wire s_rsp_ready;
	output wire [DATA_WIDTH - 1:0] s_rsp_prdata;
	output wire s_rsp_pslverr;
	output wire m0_cmd_valid;
	input wire m0_cmd_ready;
	output wire m0_cmd_pwrite;
	output wire [ADDR_WIDTH - 1:0] m0_cmd_paddr;
	output wire [DATA_WIDTH - 1:0] m0_cmd_pwdata;
	input wire m0_rsp_valid;
	output wire m0_rsp_ready;
	input wire [DATA_WIDTH - 1:0] m0_rsp_prdata;
	input wire m0_rsp_pslverr;
	output wire m1_cmd_valid;
	input wire m1_cmd_ready;
	output wire m1_cmd_pwrite;
	output wire [ADDR_WIDTH - 1:0] m1_cmd_paddr;
	output wire [DATA_WIDTH - 1:0] m1_cmd_pwdata;
	input wire m1_rsp_valid;
	output wire m1_rsp_ready;
	input wire [DATA_WIDTH - 1:0] m1_rsp_prdata;
	input wire m1_rsp_pslverr;
	output wire perf_cfg_enable;
	output wire perf_cfg_mode;
	output wire perf_cfg_clear;
	input wire [31:0] perf_fifo_data_low;
	input wire [31:0] perf_fifo_data_high;
	input wire perf_fifo_empty;
	input wire perf_fifo_full;
	input wire [15:0] perf_fifo_count;
	output wire perf_fifo_rd;
	reg addr_hit_m0;
	reg addr_hit_perf;
	reg addr_hit_m1;
	always @(*) begin
		if (_sv2v_0)
			;
		addr_hit_m0 = s_cmd_paddr[ADDR_WIDTH - 1:6] == {((ADDR_WIDTH - 1) >= 6 ? ADDR_WIDTH - 6 : 8 - ADDR_WIDTH) * 1 {1'sb0}};
		addr_hit_perf = (s_cmd_paddr[ADDR_WIDTH - 1:8] == {((ADDR_WIDTH - 1) >= 8 ? ADDR_WIDTH - 8 : 10 - ADDR_WIDTH) * 1 {1'sb0}}) && (s_cmd_paddr[7:6] != 2'b00);
		addr_hit_m1 = !addr_hit_m0 && !addr_hit_perf;
	end
	reg r_sel_m0;
	reg r_sel_perf;
	reg r_sel_m1;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_sel_m0 <= 1'b0;
			r_sel_perf <= 1'b0;
			r_sel_m1 <= 1'b0;
		end
		else begin
			if (s_cmd_valid && s_cmd_ready) begin
				r_sel_m0 <= addr_hit_m0;
				r_sel_perf <= addr_hit_perf;
				r_sel_m1 <= addr_hit_m1;
			end
			if (s_rsp_valid && s_rsp_ready) begin
				r_sel_m0 <= 1'b0;
				r_sel_perf <= 1'b0;
				r_sel_m1 <= 1'b0;
			end
		end
	localparam [7:0] PERF_CONFIG_ADDR = 8'h40;
	localparam [7:0] PERF_DATA_LOW_ADDR = 8'h44;
	localparam [7:0] PERF_DATA_HIGH_ADDR = 8'h48;
	localparam [7:0] PERF_STATUS_ADDR = 8'h4c;
	reg [2:0] r_perf_config;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_perf_config <= 3'b000;
		else if ((((s_cmd_valid && s_cmd_ready) && addr_hit_perf) && s_cmd_pwrite) && (s_cmd_paddr[7:0] == PERF_CONFIG_ADDR))
			r_perf_config <= s_cmd_pwdata[2:0];
		else if (r_perf_config[2])
			r_perf_config[2] <= 1'b0;
	assign perf_cfg_enable = r_perf_config[0];
	assign perf_cfg_mode = r_perf_config[1];
	assign perf_cfg_clear = r_perf_config[2];
	assign perf_fifo_rd = (((s_cmd_valid && s_cmd_ready) && addr_hit_perf) && !s_cmd_pwrite) && (s_cmd_paddr[7:0] == PERF_DATA_LOW_ADDR);
	reg [DATA_WIDTH - 1:0] perf_rsp_data;
	reg perf_rsp_valid;
	wire perf_rsp_ready_internal;
	always @(*) begin
		if (_sv2v_0)
			;
		perf_rsp_data = 32'h00000000;
		case (s_cmd_paddr[7:0])
			PERF_CONFIG_ADDR: perf_rsp_data = {29'h00000000, r_perf_config};
			PERF_DATA_LOW_ADDR: perf_rsp_data = perf_fifo_data_low;
			PERF_DATA_HIGH_ADDR: perf_rsp_data = perf_fifo_data_high;
			PERF_STATUS_ADDR: perf_rsp_data = {perf_fifo_count, 14'h0000, perf_fifo_full, perf_fifo_empty};
			default: perf_rsp_data = 32'hdeadbeef;
		endcase
	end
	assign perf_rsp_ready_internal = 1'b1;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			perf_rsp_valid <= 1'b0;
		else if ((s_cmd_valid && s_cmd_ready) && addr_hit_perf)
			perf_rsp_valid <= 1'b1;
		else if (perf_rsp_valid && s_rsp_ready)
			perf_rsp_valid <= 1'b0;
	assign m0_cmd_valid = s_cmd_valid && addr_hit_m0;
	assign m0_cmd_pwrite = s_cmd_pwrite;
	assign m0_cmd_paddr = s_cmd_paddr;
	assign m0_cmd_pwdata = s_cmd_pwdata;
	assign m1_cmd_valid = s_cmd_valid && addr_hit_m1;
	assign m1_cmd_pwrite = s_cmd_pwrite;
	assign m1_cmd_paddr = s_cmd_paddr;
	assign m1_cmd_pwdata = s_cmd_pwdata;
	assign s_cmd_ready = (addr_hit_m0 ? m0_cmd_ready : (addr_hit_perf ? perf_rsp_ready_internal : m1_cmd_ready));
	assign s_rsp_valid = (r_sel_m0 ? m0_rsp_valid : (r_sel_perf ? perf_rsp_valid : m1_rsp_valid));
	assign s_rsp_prdata = (r_sel_m0 ? m0_rsp_prdata : (r_sel_perf ? perf_rsp_data : m1_rsp_prdata));
	assign s_rsp_pslverr = (r_sel_m0 ? m0_rsp_pslverr : (r_sel_perf ? 1'b0 : m1_rsp_pslverr));
	assign m0_rsp_ready = r_sel_m0 && s_rsp_ready;
	assign m1_rsp_ready = r_sel_m1 && s_rsp_ready;
	initial _sv2v_0 = 0;
endmodule
