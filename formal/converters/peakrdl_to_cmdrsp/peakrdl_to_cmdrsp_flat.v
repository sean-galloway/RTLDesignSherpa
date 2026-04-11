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
	always @(posedge aclk)
		if (!aresetn)
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
	always @(posedge aclk)
		if (!aresetn) begin
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
	always @(posedge aclk)
		if (!aresetn)
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
	always @(posedge aclk)
		if (!aresetn) begin
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
