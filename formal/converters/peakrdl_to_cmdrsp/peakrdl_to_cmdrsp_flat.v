module reset_sync (
	clk,
	rst_n,
	sync_rst_n
);
	reg _sv2v_0;
	parameter signed [31:0] N = 3;
	parameter [0:0] KEEP_ATTRS = 1'b1;
	parameter [0:0] IN_ACTIVE_LOW = 1'b1;
	parameter [0:0] OUT_ACTIVE_LOW = 1'b1;
	parameter [0:0] ASYNC_ASSERT = 1'b1;
	input wire clk;
	input wire rst_n;
	output reg sync_rst_n;
	generate
		if (N < 2) begin : g_illegal
			initial $display("Error [%0t] /mnt/data/github/RTLDesignSherpa/rtl/cdc/reset_sync.sv:248:17 - reset_sync.g_illegal.<unnamed_block>\n msg: ", $time, "reset_sync: N must be >= 2 (got %0d)", N);
		end
	endgenerate
	wire rst_in_h = (IN_ACTIVE_LOW ? ~rst_n : rst_n);
	generate
		if (ASYNC_ASSERT) begin : g_async_assert
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
		else begin : g_sync_only
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module peakrdl_to_cmdrsp (
	aclk,
	aresetn,
	cmd_valid,
	cmd_ready,
	cmd_pwrite,
	cmd_paddr,
	cmd_pwdata,
	cmd_pstrb,
	rsp_valid,
	rsp_ready,
	rsp_prdata,
	rsp_pslverr,
	regblk_req,
	regblk_req_is_wr,
	regblk_addr,
	regblk_wr_data,
	regblk_wr_biten,
	regblk_req_stall_wr,
	regblk_req_stall_rd,
	regblk_rd_ack,
	regblk_rd_err,
	regblk_rd_data,
	regblk_wr_ack,
	regblk_wr_err
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 12;
	parameter signed [31:0] DATA_WIDTH = 32;
	input wire aclk;
	input wire aresetn;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_pwrite;
	input wire [ADDR_WIDTH - 1:0] cmd_paddr;
	input wire [DATA_WIDTH - 1:0] cmd_pwdata;
	input wire [(DATA_WIDTH / 8) - 1:0] cmd_pstrb;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [DATA_WIDTH - 1:0] rsp_prdata;
	output wire rsp_pslverr;
	output wire regblk_req;
	output wire regblk_req_is_wr;
	output wire [ADDR_WIDTH - 1:0] regblk_addr;
	output wire [DATA_WIDTH - 1:0] regblk_wr_data;
	output wire [DATA_WIDTH - 1:0] regblk_wr_biten;
	input wire regblk_req_stall_wr;
	input wire regblk_req_stall_rd;
	input wire regblk_rd_ack;
	input wire regblk_rd_err;
	input wire [DATA_WIDTH - 1:0] regblk_rd_data;
	input wire regblk_wr_ack;
	input wire regblk_wr_err;
	wire w_aresetn;
	reset_sync #(
		.N(3),
		.KEEP_ATTRS(1'b1),
		.IN_ACTIVE_LOW(1'b1),
		.OUT_ACTIVE_LOW(1'b1),
		.ASYNC_ASSERT(1'b1)
	) u_reset_sync(
		.clk(aclk),
		.rst_n(aresetn),
		.sync_rst_n(w_aresetn)
	);
	localparam signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	reg [1:0] cmd_state;
	reg [1:0] cmd_state_next;
	reg r_cmd_pwrite;
	reg [ADDR_WIDTH - 1:0] r_cmd_paddr;
	reg [DATA_WIDTH - 1:0] r_cmd_pwdata;
	reg [DATA_WIDTH - 1:0] r_cmd_wr_biten;
	reg rsp_state;
	reg rsp_state_next;
	reg [DATA_WIDTH - 1:0] r_rsp_prdata;
	reg r_rsp_pslverr;
	function automatic [DATA_WIDTH - 1:0] strb_to_biten;
		input reg [STRB_WIDTH - 1:0] strb;
		reg [DATA_WIDTH - 1:0] biten;
		begin
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 0; i < STRB_WIDTH; i = i + 1)
					biten[i * 8+:8] = {8 {strb[i]}};
			end
			strb_to_biten = biten;
		end
	endfunction
	always @(posedge aclk or negedge w_aresetn)
		if (!w_aresetn)
			cmd_state <= 2'b00;
		else
			cmd_state <= cmd_state_next;
	always @(*) begin
		if (_sv2v_0)
			;
		cmd_state_next = cmd_state;
		case (cmd_state)
			2'b00:
				if (cmd_valid) begin
					if (cmd_pwrite && !regblk_req_stall_wr)
						cmd_state_next = 2'b01;
					else if (!cmd_pwrite && !regblk_req_stall_rd)
						cmd_state_next = 2'b01;
					else
						cmd_state_next = 2'b10;
				end
			2'b01:
				if (regblk_wr_ack || regblk_rd_ack)
					cmd_state_next = 2'b00;
			2'b10:
				if (r_cmd_pwrite && !regblk_req_stall_wr)
					cmd_state_next = 2'b01;
				else if (!r_cmd_pwrite && !regblk_req_stall_rd)
					cmd_state_next = 2'b01;
			default: cmd_state_next = 2'b00;
		endcase
	end
	assign cmd_ready = cmd_state == 2'b00;
	always @(posedge aclk or negedge w_aresetn)
		if (!w_aresetn) begin
			r_cmd_pwrite <= 1'sb0;
			r_cmd_paddr <= 1'sb0;
			r_cmd_pwdata <= 1'sb0;
			r_cmd_wr_biten <= 1'sb0;
		end
		else if (cmd_valid && cmd_ready) begin
			r_cmd_pwrite <= cmd_pwrite;
			r_cmd_paddr <= cmd_paddr;
			r_cmd_pwdata <= cmd_pwdata;
			r_cmd_wr_biten <= strb_to_biten(cmd_pstrb);
		end
	assign regblk_req = (cmd_state == 2'b01) || ((cmd_state == 2'b00) && cmd_valid);
	assign regblk_req_is_wr = (cmd_state == 2'b00 ? cmd_pwrite : r_cmd_pwrite);
	assign regblk_addr = (cmd_state == 2'b00 ? cmd_paddr : r_cmd_paddr);
	assign regblk_wr_data = (cmd_state == 2'b00 ? cmd_pwdata : r_cmd_pwdata);
	assign regblk_wr_biten = (cmd_state == 2'b00 ? strb_to_biten(cmd_pstrb) : r_cmd_wr_biten);
	always @(posedge aclk or negedge w_aresetn)
		if (!w_aresetn)
			rsp_state <= 1'b0;
		else
			rsp_state <= rsp_state_next;
	always @(*) begin
		if (_sv2v_0)
			;
		rsp_state_next = rsp_state;
		case (rsp_state)
			1'b0:
				if (regblk_wr_ack || regblk_rd_ack)
					rsp_state_next = 1'b1;
			1'b1:
				if (rsp_ready)
					rsp_state_next = 1'b0;
			default: rsp_state_next = 1'b0;
		endcase
	end
	always @(posedge aclk or negedge w_aresetn)
		if (!w_aresetn) begin
			r_rsp_prdata <= 1'sb0;
			r_rsp_pslverr <= 1'sb0;
		end
		else if (rsp_state == 1'b0) begin
			if (regblk_rd_ack) begin
				r_rsp_prdata <= regblk_rd_data;
				r_rsp_pslverr <= regblk_rd_err;
			end
			else if (regblk_wr_ack) begin
				r_rsp_prdata <= 1'sb0;
				r_rsp_pslverr <= regblk_wr_err;
			end
		end
	assign rsp_valid = rsp_state == 1'b1;
	assign rsp_prdata = r_rsp_prdata;
	assign rsp_pslverr = r_rsp_pslverr;
	initial _sv2v_0 = 0;
endmodule
