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
	always @(posedge aclk or negedge aresetn)
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
	always @(posedge aclk or negedge aresetn)
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
	always @(posedge aclk or negedge aresetn)
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
	always @(posedge aclk or negedge aresetn)
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
module rtc_regs (
	clk,
	rst,
	s_cpuif_req,
	s_cpuif_req_is_wr,
	s_cpuif_addr,
	s_cpuif_wr_data,
	s_cpuif_wr_biten,
	s_cpuif_req_stall_wr,
	s_cpuif_req_stall_rd,
	s_cpuif_rd_ack,
	s_cpuif_rd_err,
	s_cpuif_rd_data,
	s_cpuif_wr_ack,
	s_cpuif_wr_err,
	hwif_in,
	hwif_out
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	input wire s_cpuif_req;
	input wire s_cpuif_req_is_wr;
	input wire [5:0] s_cpuif_addr;
	input wire [31:0] s_cpuif_wr_data;
	input wire [31:0] s_cpuif_wr_biten;
	output wire s_cpuif_req_stall_wr;
	output wire s_cpuif_req_stall_rd;
	output wire s_cpuif_rd_ack;
	output wire s_cpuif_rd_err;
	output wire [31:0] s_cpuif_rd_data;
	output wire s_cpuif_wr_ack;
	output wire s_cpuif_wr_err;
	input wire [58:0] hwif_in;
	output wire [82:0] hwif_out;
	wire cpuif_req;
	wire cpuif_req_is_wr;
	wire [5:0] cpuif_addr;
	wire [31:0] cpuif_wr_data;
	wire [31:0] cpuif_wr_biten;
	wire cpuif_req_stall_wr;
	wire cpuif_req_stall_rd;
	wire cpuif_rd_ack;
	wire cpuif_rd_err;
	wire [31:0] cpuif_rd_data;
	wire cpuif_wr_ack;
	wire cpuif_wr_err;
	assign cpuif_req = s_cpuif_req;
	assign cpuif_req_is_wr = s_cpuif_req_is_wr;
	assign cpuif_addr = s_cpuif_addr;
	assign cpuif_wr_data = s_cpuif_wr_data;
	assign cpuif_wr_biten = s_cpuif_wr_biten;
	assign s_cpuif_req_stall_wr = cpuif_req_stall_wr;
	assign s_cpuif_req_stall_rd = cpuif_req_stall_rd;
	assign s_cpuif_rd_ack = cpuif_rd_ack;
	assign s_cpuif_rd_err = cpuif_rd_err;
	assign s_cpuif_rd_data = cpuif_rd_data;
	assign s_cpuif_wr_ack = cpuif_wr_ack;
	assign s_cpuif_wr_err = cpuif_wr_err;
	wire cpuif_req_masked;
	assign cpuif_req_stall_rd = 1'sb0;
	assign cpuif_req_stall_wr = 1'sb0;
	assign cpuif_req_masked = (cpuif_req & !(!cpuif_req_is_wr & cpuif_req_stall_rd)) & !(cpuif_req_is_wr & cpuif_req_stall_wr);
	reg [12:0] decoded_reg_strb;
	wire decoded_req;
	wire decoded_req_is_wr;
	wire [31:0] decoded_wr_data;
	wire [31:0] decoded_wr_biten;
	always @(*) begin
		if (_sv2v_0)
			;
		decoded_reg_strb[12] = cpuif_req_masked & (cpuif_addr == 6'h00);
		decoded_reg_strb[11] = cpuif_req_masked & (cpuif_addr == 6'h04);
		decoded_reg_strb[10] = cpuif_req_masked & (cpuif_addr == 6'h08);
		decoded_reg_strb[9] = cpuif_req_masked & (cpuif_addr == 6'h0c);
		decoded_reg_strb[8] = cpuif_req_masked & (cpuif_addr == 6'h10);
		decoded_reg_strb[7] = cpuif_req_masked & (cpuif_addr == 6'h14);
		decoded_reg_strb[6] = cpuif_req_masked & (cpuif_addr == 6'h18);
		decoded_reg_strb[5] = cpuif_req_masked & (cpuif_addr == 6'h1c);
		decoded_reg_strb[4] = cpuif_req_masked & (cpuif_addr == 6'h20);
		decoded_reg_strb[3] = cpuif_req_masked & (cpuif_addr == 6'h24);
		decoded_reg_strb[2] = cpuif_req_masked & (cpuif_addr == 6'h28);
		decoded_reg_strb[1] = cpuif_req_masked & (cpuif_addr == 6'h2c);
		decoded_reg_strb[0] = cpuif_req_masked & (cpuif_addr == 6'h30);
	end
	assign decoded_req = cpuif_req_masked;
	assign decoded_req_is_wr = cpuif_req_is_wr;
	assign decoded_wr_data = cpuif_wr_data;
	assign decoded_wr_biten = cpuif_wr_biten;
	reg [108:0] field_combo;
	reg [85:0] field_storage;
	always @(*) begin : sv2v_autoblock_1
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[85];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[12] && decoded_req_is_wr) begin
			next_c = (field_storage[85] & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
			load_next_c = 1'sb1;
		end
		field_combo[108] = next_c;
		field_combo[107] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[85] <= 1'h0;
		else if (field_combo[107])
			field_storage[85] <= field_combo[108];
	assign hwif_out[82] = field_storage[85];
	always @(*) begin : sv2v_autoblock_2
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[84];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[12] && decoded_req_is_wr) begin
			next_c = (field_storage[84] & ~decoded_wr_biten[1:1]) | (decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
			load_next_c = 1'sb1;
		end
		field_combo[106] = next_c;
		field_combo[105] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[84] <= 1'h0;
		else if (field_combo[105])
			field_storage[84] <= field_combo[106];
	assign hwif_out[81] = field_storage[84];
	always @(*) begin : sv2v_autoblock_3
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[83];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[12] && decoded_req_is_wr) begin
			next_c = (field_storage[83] & ~decoded_wr_biten[2:2]) | (decoded_wr_data[2:2] & decoded_wr_biten[2:2]);
			load_next_c = 1'sb1;
		end
		field_combo[104] = next_c;
		field_combo[103] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[83] <= 1'h0;
		else if (field_combo[103])
			field_storage[83] <= field_combo[104];
	assign hwif_out[80] = field_storage[83];
	always @(*) begin : sv2v_autoblock_4
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[82];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[12] && decoded_req_is_wr) begin
			next_c = (field_storage[82] & ~decoded_wr_biten[3:3]) | (decoded_wr_data[3:3] & decoded_wr_biten[3:3]);
			load_next_c = 1'sb1;
		end
		field_combo[102] = next_c;
		field_combo[101] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[82] <= 1'h0;
		else if (field_combo[101])
			field_storage[82] <= field_combo[102];
	assign hwif_out[79] = field_storage[82];
	always @(*) begin : sv2v_autoblock_5
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[81];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[12] && decoded_req_is_wr) begin
			next_c = (field_storage[81] & ~decoded_wr_biten[4:4]) | (decoded_wr_data[4:4] & decoded_wr_biten[4:4]);
			load_next_c = 1'sb1;
		end
		field_combo[100] = next_c;
		field_combo[99] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[81] <= 1'h0;
		else if (field_combo[99])
			field_storage[81] <= field_combo[100];
	assign hwif_out[78] = field_storage[81];
	always @(*) begin : sv2v_autoblock_6
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[80];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[11] && decoded_req_is_wr) begin
			next_c = (field_storage[80] & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
			load_next_c = 1'sb1;
		end
		field_combo[98] = next_c;
		field_combo[97] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[80] <= 1'h0;
		else if (field_combo[97])
			field_storage[80] <= field_combo[98];
	assign hwif_out[77] = field_storage[80];
	always @(*) begin : sv2v_autoblock_7
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[79];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[11] && decoded_req_is_wr) begin
			next_c = (field_storage[79] & ~decoded_wr_biten[1:1]) | (decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
			load_next_c = 1'sb1;
		end
		field_combo[96] = next_c;
		field_combo[95] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[79] <= 1'h0;
		else if (field_combo[95])
			field_storage[79] <= field_combo[96];
	assign hwif_out[76] = field_storage[79];
	always @(*) begin : sv2v_autoblock_8
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[78];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[11] && decoded_req_is_wr) begin
			next_c = (field_storage[78] & ~decoded_wr_biten[2:2]) | (decoded_wr_data[2:2] & decoded_wr_biten[2:2]);
			load_next_c = 1'sb1;
		end
		field_combo[94] = next_c;
		field_combo[93] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[78] <= 1'h0;
		else if (field_combo[93])
			field_storage[78] <= field_combo[94];
	assign hwif_out[75] = field_storage[78];
	always @(*) begin : sv2v_autoblock_9
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[77];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[10] && decoded_req_is_wr) begin
			next_c = field_storage[77] & ~(decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
			load_next_c = 1'sb1;
		end
		else begin
			next_c = hwif_in[58];
			load_next_c = 1'sb1;
		end
		field_combo[92] = next_c;
		field_combo[91] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[77] <= 1'h0;
		else if (field_combo[91])
			field_storage[77] <= field_combo[92];
	always @(*) begin : sv2v_autoblock_10
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[76];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[10] && decoded_req_is_wr) begin
			next_c = field_storage[76] & ~(decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
			load_next_c = 1'sb1;
		end
		else begin
			next_c = hwif_in[57];
			load_next_c = 1'sb1;
		end
		field_combo[90] = next_c;
		field_combo[89] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[76] <= 1'h0;
		else if (field_combo[89])
			field_storage[76] <= field_combo[90];
	always @(*) begin : sv2v_autoblock_11
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[75];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[10] && decoded_req_is_wr) begin
			next_c = field_storage[75] & ~(decoded_wr_data[4:4] & decoded_wr_biten[4:4]);
			load_next_c = 1'sb1;
		end
		else begin
			next_c = hwif_in[54];
			load_next_c = 1'sb1;
		end
		field_combo[88] = next_c;
		field_combo[87] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[75] <= 1'h0;
		else if (field_combo[87])
			field_storage[75] <= field_combo[88];
	always @(*) begin : sv2v_autoblock_12
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[74-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[9] && decoded_req_is_wr) begin
			next_c = (field_storage[74-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[45]) begin
			next_c = hwif_in[53-:8];
			load_next_c = 1'sb1;
		end
		field_combo[86-:8] = next_c;
		field_combo[78] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[74-:8] <= 8'h00;
		else if (field_combo[78])
			field_storage[74-:8] <= field_combo[86-:8];
	assign hwif_out[74-:8] = field_storage[74-:8];
	always @(*) begin : sv2v_autoblock_13
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[66-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[8] && decoded_req_is_wr) begin
			next_c = (field_storage[66-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[36]) begin
			next_c = hwif_in[44-:8];
			load_next_c = 1'sb1;
		end
		field_combo[77-:8] = next_c;
		field_combo[69] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[66-:8] <= 8'h00;
		else if (field_combo[69])
			field_storage[66-:8] <= field_combo[77-:8];
	assign hwif_out[66-:8] = field_storage[66-:8];
	always @(*) begin : sv2v_autoblock_14
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[58-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[7] && decoded_req_is_wr) begin
			next_c = (field_storage[58-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[27]) begin
			next_c = hwif_in[35-:8];
			load_next_c = 1'sb1;
		end
		field_combo[68-:8] = next_c;
		field_combo[60] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[58-:8] <= 8'h00;
		else if (field_combo[60])
			field_storage[58-:8] <= field_combo[68-:8];
	assign hwif_out[58-:8] = field_storage[58-:8];
	always @(*) begin : sv2v_autoblock_15
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[50-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[6] && decoded_req_is_wr) begin
			next_c = (field_storage[50-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[18]) begin
			next_c = hwif_in[26-:8];
			load_next_c = 1'sb1;
		end
		field_combo[59-:8] = next_c;
		field_combo[51] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[50-:8] <= 8'h01;
		else if (field_combo[51])
			field_storage[50-:8] <= field_combo[59-:8];
	assign hwif_out[50-:8] = field_storage[50-:8];
	always @(*) begin : sv2v_autoblock_16
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[42-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[5] && decoded_req_is_wr) begin
			next_c = (field_storage[42-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[9]) begin
			next_c = hwif_in[17-:8];
			load_next_c = 1'sb1;
		end
		field_combo[50-:8] = next_c;
		field_combo[42] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[42-:8] <= 8'h01;
		else if (field_combo[42])
			field_storage[42-:8] <= field_combo[50-:8];
	assign hwif_out[42-:8] = field_storage[42-:8];
	always @(*) begin : sv2v_autoblock_17
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[34-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[4] && decoded_req_is_wr) begin
			next_c = (field_storage[34-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		else if (hwif_in[0]) begin
			next_c = hwif_in[8-:8];
			load_next_c = 1'sb1;
		end
		field_combo[41-:8] = next_c;
		field_combo[33] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[34-:8] <= 8'h00;
		else if (field_combo[33])
			field_storage[34-:8] <= field_combo[41-:8];
	assign hwif_out[34-:8] = field_storage[34-:8];
	always @(*) begin : sv2v_autoblock_18
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[26-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[3] && decoded_req_is_wr) begin
			next_c = (field_storage[26-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		field_combo[32-:8] = next_c;
		field_combo[24] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[26-:8] <= 8'h00;
		else if (field_combo[24])
			field_storage[26-:8] <= field_combo[32-:8];
	assign hwif_out[26-:8] = field_storage[26-:8];
	always @(*) begin : sv2v_autoblock_19
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[18-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[2] && decoded_req_is_wr) begin
			next_c = (field_storage[18-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		field_combo[23-:8] = next_c;
		field_combo[15] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[18-:8] <= 8'h00;
		else if (field_combo[15])
			field_storage[18-:8] <= field_combo[23-:8];
	assign hwif_out[18-:8] = field_storage[18-:8];
	always @(*) begin : sv2v_autoblock_20
		reg [7:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[10-:8];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[1] && decoded_req_is_wr) begin
			next_c = (field_storage[10-:8] & ~decoded_wr_biten[7:0]) | (decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
			load_next_c = 1'sb1;
		end
		field_combo[14-:8] = next_c;
		field_combo[6] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[10-:8] <= 8'h00;
		else if (field_combo[6])
			field_storage[10-:8] <= field_combo[14-:8];
	assign hwif_out[10-:8] = field_storage[10-:8];
	always @(*) begin : sv2v_autoblock_21
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[2];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[0] && decoded_req_is_wr) begin
			next_c = (field_storage[2] & ~decoded_wr_biten[0:0]) | (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
			load_next_c = 1'sb1;
		end
		field_combo[5] = next_c;
		field_combo[4] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[2] <= 1'h0;
		else if (field_combo[4])
			field_storage[2] <= field_combo[5];
	assign hwif_out[2] = field_storage[2];
	always @(*) begin : sv2v_autoblock_22
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[1];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[0] && decoded_req_is_wr) begin
			next_c = (field_storage[1] & ~decoded_wr_biten[1:1]) | (decoded_wr_data[1:1] & decoded_wr_biten[1:1]);
			load_next_c = 1'sb1;
		end
		field_combo[3] = next_c;
		field_combo[2] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[1] <= 1'h0;
		else if (field_combo[2])
			field_storage[1] <= field_combo[3];
	assign hwif_out[1] = field_storage[1];
	always @(*) begin : sv2v_autoblock_23
		reg [0:0] next_c;
		reg load_next_c;
		if (_sv2v_0)
			;
		next_c = field_storage[0];
		load_next_c = 1'sb0;
		if (decoded_reg_strb[0] && decoded_req_is_wr) begin
			next_c = (field_storage[0] & ~decoded_wr_biten[2:2]) | (decoded_wr_data[2:2] & decoded_wr_biten[2:2]);
			load_next_c = 1'sb1;
		end
		field_combo[1] = next_c;
		field_combo[0] = load_next_c;
	end
	always @(posedge clk)
		if (rst)
			field_storage[0] <= 1'h0;
		else if (field_combo[0])
			field_storage[0] <= field_combo[1];
	assign hwif_out[0] = field_storage[0];
	assign cpuif_wr_ack = decoded_req & decoded_req_is_wr;
	assign cpuif_wr_err = 1'sb0;
	reg readback_err;
	reg readback_done;
	reg [31:0] readback_data;
	wire [31:0] readback_array [0:12];
	assign readback_array[0][0:0] = (decoded_reg_strb[12] && !decoded_req_is_wr ? field_storage[85] : 1'b0);
	assign readback_array[0][1:1] = (decoded_reg_strb[12] && !decoded_req_is_wr ? field_storage[84] : 1'b0);
	assign readback_array[0][2:2] = (decoded_reg_strb[12] && !decoded_req_is_wr ? field_storage[83] : 1'b0);
	assign readback_array[0][3:3] = (decoded_reg_strb[12] && !decoded_req_is_wr ? field_storage[82] : 1'b0);
	assign readback_array[0][4:4] = (decoded_reg_strb[12] && !decoded_req_is_wr ? field_storage[81] : 1'b0);
	assign readback_array[0][31:5] = (decoded_reg_strb[12] && !decoded_req_is_wr ? 27'h0000000 : {27 {1'sb0}});
	assign readback_array[1][0:0] = (decoded_reg_strb[11] && !decoded_req_is_wr ? field_storage[80] : 1'b0);
	assign readback_array[1][1:1] = (decoded_reg_strb[11] && !decoded_req_is_wr ? field_storage[79] : 1'b0);
	assign readback_array[1][2:2] = (decoded_reg_strb[11] && !decoded_req_is_wr ? field_storage[78] : 1'b0);
	assign readback_array[1][31:3] = (decoded_reg_strb[11] && !decoded_req_is_wr ? 29'h00000000 : {29 {1'sb0}});
	assign readback_array[2][0:0] = (decoded_reg_strb[10] && !decoded_req_is_wr ? field_storage[77] : 1'b0);
	assign readback_array[2][1:1] = (decoded_reg_strb[10] && !decoded_req_is_wr ? field_storage[76] : 1'b0);
	assign readback_array[2][2:2] = (decoded_reg_strb[10] && !decoded_req_is_wr ? hwif_in[56] : 1'b0);
	assign readback_array[2][3:3] = (decoded_reg_strb[10] && !decoded_req_is_wr ? hwif_in[55] : 1'b0);
	assign readback_array[2][4:4] = (decoded_reg_strb[10] && !decoded_req_is_wr ? field_storage[75] : 1'b0);
	assign readback_array[2][31:5] = (decoded_reg_strb[10] && !decoded_req_is_wr ? 27'h0000000 : {27 {1'sb0}});
	assign readback_array[3][7:0] = (decoded_reg_strb[9] && !decoded_req_is_wr ? field_storage[74-:8] : {8 {1'sb0}});
	assign readback_array[3][31:8] = (decoded_reg_strb[9] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[4][7:0] = (decoded_reg_strb[8] && !decoded_req_is_wr ? field_storage[66-:8] : {8 {1'sb0}});
	assign readback_array[4][31:8] = (decoded_reg_strb[8] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[5][7:0] = (decoded_reg_strb[7] && !decoded_req_is_wr ? field_storage[58-:8] : {8 {1'sb0}});
	assign readback_array[5][31:8] = (decoded_reg_strb[7] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[6][7:0] = (decoded_reg_strb[6] && !decoded_req_is_wr ? field_storage[50-:8] : {8 {1'sb0}});
	assign readback_array[6][31:8] = (decoded_reg_strb[6] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[7][7:0] = (decoded_reg_strb[5] && !decoded_req_is_wr ? field_storage[42-:8] : {8 {1'sb0}});
	assign readback_array[7][31:8] = (decoded_reg_strb[5] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[8][7:0] = (decoded_reg_strb[4] && !decoded_req_is_wr ? field_storage[34-:8] : {8 {1'sb0}});
	assign readback_array[8][31:8] = (decoded_reg_strb[4] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[9][7:0] = (decoded_reg_strb[3] && !decoded_req_is_wr ? field_storage[26-:8] : {8 {1'sb0}});
	assign readback_array[9][31:8] = (decoded_reg_strb[3] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[10][7:0] = (decoded_reg_strb[2] && !decoded_req_is_wr ? field_storage[18-:8] : {8 {1'sb0}});
	assign readback_array[10][31:8] = (decoded_reg_strb[2] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[11][7:0] = (decoded_reg_strb[1] && !decoded_req_is_wr ? field_storage[10-:8] : {8 {1'sb0}});
	assign readback_array[11][31:8] = (decoded_reg_strb[1] && !decoded_req_is_wr ? 24'h000000 : {24 {1'sb0}});
	assign readback_array[12][0:0] = (decoded_reg_strb[0] && !decoded_req_is_wr ? field_storage[2] : 1'b0);
	assign readback_array[12][1:1] = (decoded_reg_strb[0] && !decoded_req_is_wr ? field_storage[1] : 1'b0);
	assign readback_array[12][2:2] = (decoded_reg_strb[0] && !decoded_req_is_wr ? field_storage[0] : 1'b0);
	assign readback_array[12][31:3] = (decoded_reg_strb[0] && !decoded_req_is_wr ? 29'h00000000 : {29 {1'sb0}});
	always @(*) begin : sv2v_autoblock_24
		reg [31:0] readback_data_var;
		if (_sv2v_0)
			;
		readback_done = decoded_req & ~decoded_req_is_wr;
		readback_err = 1'sb0;
		readback_data_var = 1'sb0;
		begin : sv2v_autoblock_25
			reg signed [31:0] i;
			for (i = 0; i < 13; i = i + 1)
				readback_data_var = readback_data_var | readback_array[i];
		end
		readback_data = readback_data_var;
	end
	assign cpuif_rd_ack = readback_done;
	assign cpuif_rd_data = readback_data;
	assign cpuif_rd_err = readback_err;
	initial _sv2v_0 = 0;
endmodule
module rtc_config_regs (
	clk,
	rst_n,
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
	cfg_rtc_enable,
	cfg_hour_mode_12,
	cfg_bcd_mode,
	cfg_clock_select,
	cfg_time_set_mode,
	cfg_valid,
	cfg_alarm_enable,
	cfg_alarm_int_enable,
	cfg_second_int_enable,
	time_seconds_out,
	time_minutes_out,
	time_hours_out,
	time_day_out,
	time_month_out,
	time_year_out,
	time_set_commit,
	time_commit_busy,
	time_seconds_in,
	time_minutes_in,
	time_hours_in,
	time_day_in,
	time_month_in,
	time_year_in,
	alarm_seconds,
	alarm_minutes,
	alarm_hours,
	alarm_sec_match_en,
	alarm_min_match_en,
	alarm_hour_match_en,
	status_alarm_flag,
	status_second_tick,
	status_time_valid,
	status_pm_indicator,
	status_commit_timeout,
	clear_alarm_flag,
	clear_second_tick,
	clear_commit_timeout
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_pwrite;
	input wire [11:0] cmd_paddr;
	input wire [31:0] cmd_pwdata;
	input wire [3:0] cmd_pstrb;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [31:0] rsp_prdata;
	output wire rsp_pslverr;
	output wire cfg_rtc_enable;
	output wire cfg_hour_mode_12;
	output wire cfg_bcd_mode;
	output wire cfg_clock_select;
	output wire cfg_time_set_mode;
	output wire cfg_valid;
	output wire cfg_alarm_enable;
	output wire cfg_alarm_int_enable;
	output wire cfg_second_int_enable;
	output wire [7:0] time_seconds_out;
	output wire [7:0] time_minutes_out;
	output wire [7:0] time_hours_out;
	output wire [7:0] time_day_out;
	output wire [7:0] time_month_out;
	output wire [7:0] time_year_out;
	output wire time_set_commit;
	input wire time_commit_busy;
	input wire [7:0] time_seconds_in;
	input wire [7:0] time_minutes_in;
	input wire [7:0] time_hours_in;
	input wire [7:0] time_day_in;
	input wire [7:0] time_month_in;
	input wire [7:0] time_year_in;
	output wire [7:0] alarm_seconds;
	output wire [7:0] alarm_minutes;
	output wire [7:0] alarm_hours;
	output wire alarm_sec_match_en;
	output wire alarm_min_match_en;
	output wire alarm_hour_match_en;
	input wire status_alarm_flag;
	input wire status_second_tick;
	input wire status_time_valid;
	input wire status_pm_indicator;
	input wire status_commit_timeout;
	output wire clear_alarm_flag;
	output wire clear_second_tick;
	output wire clear_commit_timeout;
	localparam [11:0] ADDR_RTC_CONFIG = 12'h000;
	localparam [11:0] ADDR_RTC_CONTROL = 12'h004;
	localparam [11:0] ADDR_RTC_STATUS = 12'h008;
	localparam [11:0] ADDR_RTC_SECONDS = 12'h00c;
	localparam [11:0] ADDR_RTC_MINUTES = 12'h010;
	localparam [11:0] ADDR_RTC_HOURS = 12'h014;
	localparam [11:0] ADDR_RTC_DAY = 12'h018;
	localparam [11:0] ADDR_RTC_MONTH = 12'h01c;
	localparam [11:0] ADDR_RTC_YEAR = 12'h020;
	localparam [11:0] ADDR_RTC_ALARM_SEC = 12'h024;
	localparam [11:0] ADDR_RTC_ALARM_MIN = 12'h028;
	localparam [11:0] ADDR_RTC_ALARM_HOUR = 12'h02c;
	localparam [11:0] ADDR_RTC_ALARM_MASK = 12'h030;
	wire adapter_req;
	wire adapter_req_is_wr;
	wire [11:0] adapter_addr;
	wire [31:0] adapter_wr_data;
	wire [31:0] adapter_wr_biten;
	wire adapter_req_stall_wr;
	wire adapter_req_stall_rd;
	wire adapter_rd_ack;
	wire adapter_rd_err;
	wire [31:0] adapter_rd_data;
	wire adapter_wr_ack;
	wire adapter_wr_err;
	wire regblk_req;
	wire regblk_req_is_wr;
	wire [5:0] regblk_addr;
	wire [31:0] regblk_wr_data;
	wire [31:0] regblk_wr_biten;
	wire regblk_req_stall_wr;
	wire regblk_req_stall_rd;
	wire regblk_rd_ack;
	wire regblk_rd_err;
	wire [31:0] regblk_rd_data;
	wire regblk_wr_ack;
	wire regblk_wr_err;
	reg w_addr_mapped;
	wire w_drop;
	wire w_drop_ack;
	reg r_time_set_mode_d;
	wire w_mirror_en;
	wire w_seconds_rd_req;
	reg r_seconds_rd_d;
	wire w_seconds_latch;
	wire w_stage_hold;
	wire w_snapshot_load;
	wire w_staged_pm;
	reg [7:0] r_shd_d1_minutes;
	reg [7:0] r_shd_d1_hours;
	reg [7:0] r_shd_d1_day;
	reg [7:0] r_shd_d1_month;
	reg [7:0] r_shd_d1_year;
	reg r_shd_d1_pm;
	reg r_shd_d1_valid;
	reg r_snap_pm;
	reg r_snap_time_valid;
	wire w_config_sw_wr;
	reg r_cfg_valid;
	wire w_status_sw_wr;
	wire w_status_wr_event;
	reg r_status_sw_wr_d;
	wire [58:0] hwif_in;
	wire [82:0] hwif_out;
	peakrdl_to_cmdrsp #(
		.ADDR_WIDTH(12),
		.DATA_WIDTH(32)
	) u_adapter(
		.aclk(clk),
		.aresetn(rst_n),
		.cmd_valid(cmd_valid),
		.cmd_ready(cmd_ready),
		.cmd_pwrite(cmd_pwrite),
		.cmd_paddr(cmd_paddr),
		.cmd_pwdata(cmd_pwdata),
		.cmd_pstrb(cmd_pstrb),
		.rsp_valid(rsp_valid),
		.rsp_ready(rsp_ready),
		.rsp_prdata(rsp_prdata),
		.rsp_pslverr(rsp_pslverr),
		.regblk_req(adapter_req),
		.regblk_req_is_wr(adapter_req_is_wr),
		.regblk_addr(adapter_addr),
		.regblk_wr_data(adapter_wr_data),
		.regblk_wr_biten(adapter_wr_biten),
		.regblk_req_stall_wr(adapter_req_stall_wr),
		.regblk_req_stall_rd(adapter_req_stall_rd),
		.regblk_rd_ack(adapter_rd_ack),
		.regblk_rd_err(adapter_rd_err),
		.regblk_rd_data(adapter_rd_data),
		.regblk_wr_ack(adapter_wr_ack),
		.regblk_wr_err(adapter_wr_err)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		case (adapter_addr)
			ADDR_RTC_CONFIG, ADDR_RTC_CONTROL, ADDR_RTC_STATUS, ADDR_RTC_SECONDS, ADDR_RTC_MINUTES, ADDR_RTC_HOURS, ADDR_RTC_DAY, ADDR_RTC_MONTH, ADDR_RTC_YEAR, ADDR_RTC_ALARM_SEC, ADDR_RTC_ALARM_MIN, ADDR_RTC_ALARM_HOUR, ADDR_RTC_ALARM_MASK: w_addr_mapped = 1'b1;
			default: w_addr_mapped = 1'b0;
		endcase
	end
	assign w_drop = !w_addr_mapped;
	assign w_drop_ack = adapter_req && w_drop;
	assign regblk_req = adapter_req && !w_drop;
	assign regblk_req_is_wr = adapter_req_is_wr;
	assign regblk_addr = adapter_addr[5:0];
	assign regblk_wr_data = adapter_wr_data;
	assign regblk_wr_biten = adapter_wr_biten;
	assign adapter_req_stall_wr = regblk_req_stall_wr;
	assign adapter_req_stall_rd = regblk_req_stall_rd;
	assign adapter_rd_ack = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
	assign adapter_rd_err = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
	assign adapter_rd_data = (w_drop_ack ? 32'h00000000 : regblk_rd_data);
	assign adapter_wr_ack = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
	assign adapter_wr_err = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_time_set_mode_d <= 1'b0;
		else
			r_time_set_mode_d <= cfg_time_set_mode;
	assign time_set_commit = r_time_set_mode_d && !cfg_time_set_mode;
	assign w_seconds_rd_req = (regblk_req && !regblk_req_is_wr) && (regblk_addr == ADDR_RTC_SECONDS[5:0]);
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_seconds_rd_d <= 1'b0;
		else
			r_seconds_rd_d <= w_seconds_rd_req;
	assign w_seconds_latch = w_seconds_rd_req && !r_seconds_rd_d;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_shd_d1_minutes <= 8'h00;
			r_shd_d1_hours <= 8'h00;
			r_shd_d1_day <= 8'h01;
			r_shd_d1_month <= 8'h01;
			r_shd_d1_year <= 8'h00;
			r_shd_d1_pm <= 1'b0;
			r_shd_d1_valid <= 1'b0;
		end
		else begin
			r_shd_d1_minutes <= time_minutes_in;
			r_shd_d1_hours <= time_hours_in;
			r_shd_d1_day <= time_day_in;
			r_shd_d1_month <= time_month_in;
			r_shd_d1_year <= time_year_in;
			r_shd_d1_pm <= status_pm_indicator;
			r_shd_d1_valid <= status_time_valid;
		end
	assign w_stage_hold = (cfg_time_set_mode || time_set_commit) || time_commit_busy;
	assign w_mirror_en = !w_stage_hold;
	assign w_snapshot_load = w_seconds_latch && !w_stage_hold;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_snap_pm <= 1'b0;
			r_snap_time_valid <= 1'b0;
		end
		else if (w_snapshot_load) begin
			r_snap_pm <= r_shd_d1_pm;
			r_snap_time_valid <= r_shd_d1_valid;
		end
	assign w_staged_pm = cfg_hour_mode_12 && hwif_out[58];
	assign w_config_sw_wr = (regblk_req && regblk_req_is_wr) && (regblk_addr == ADDR_RTC_CONFIG[5:0]);
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_cfg_valid <= 1'b0;
		else if (w_config_sw_wr)
			r_cfg_valid <= 1'b1;
	assign cfg_valid = r_cfg_valid;
	assign w_status_sw_wr = (regblk_req && regblk_req_is_wr) && (regblk_addr == ADDR_RTC_STATUS[5:0]);
	assign w_status_wr_event = w_status_sw_wr && !r_status_sw_wr_d;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_status_sw_wr_d <= 1'b0;
		else
			r_status_sw_wr_d <= w_status_sw_wr;
	assign clear_alarm_flag = (w_status_wr_event && regblk_wr_data[0]) && regblk_wr_biten[0];
	assign clear_second_tick = (w_status_wr_event && regblk_wr_data[1]) && regblk_wr_biten[1];
	assign clear_commit_timeout = (w_status_wr_event && regblk_wr_data[4]) && regblk_wr_biten[4];
	assign hwif_in[53-:8] = time_seconds_in;
	assign hwif_in[44-:8] = r_shd_d1_minutes;
	assign hwif_in[35-:8] = r_shd_d1_hours;
	assign hwif_in[26-:8] = r_shd_d1_day;
	assign hwif_in[17-:8] = r_shd_d1_month;
	assign hwif_in[8-:8] = r_shd_d1_year;
	assign hwif_in[45] = w_mirror_en;
	assign hwif_in[36] = w_snapshot_load;
	assign hwif_in[27] = w_snapshot_load;
	assign hwif_in[18] = w_snapshot_load;
	assign hwif_in[9] = w_snapshot_load;
	assign hwif_in[0] = w_snapshot_load;
	assign hwif_in[58] = status_alarm_flag;
	assign hwif_in[57] = status_second_tick;
	assign hwif_in[54] = status_commit_timeout;
	assign hwif_in[56] = (w_stage_hold ? 1'b0 : r_snap_time_valid);
	assign hwif_in[55] = (w_stage_hold ? w_staged_pm : r_snap_pm);
	rtc_regs u_rtc_regs(
		.clk(clk),
		.rst(!rst_n),
		.s_cpuif_req(regblk_req),
		.s_cpuif_req_is_wr(regblk_req_is_wr),
		.s_cpuif_addr(regblk_addr),
		.s_cpuif_wr_data(regblk_wr_data),
		.s_cpuif_wr_biten(regblk_wr_biten),
		.s_cpuif_req_stall_wr(regblk_req_stall_wr),
		.s_cpuif_req_stall_rd(regblk_req_stall_rd),
		.s_cpuif_rd_ack(regblk_rd_ack),
		.s_cpuif_rd_err(regblk_rd_err),
		.s_cpuif_rd_data(regblk_rd_data),
		.s_cpuif_wr_ack(regblk_wr_ack),
		.s_cpuif_wr_err(regblk_wr_err),
		.hwif_in(hwif_in),
		.hwif_out(hwif_out)
	);
	assign cfg_rtc_enable = hwif_out[82];
	assign cfg_hour_mode_12 = hwif_out[81];
	assign cfg_bcd_mode = hwif_out[80];
	assign cfg_clock_select = hwif_out[79];
	assign cfg_time_set_mode = hwif_out[78];
	assign cfg_alarm_enable = hwif_out[77];
	assign cfg_alarm_int_enable = hwif_out[76];
	assign cfg_second_int_enable = hwif_out[75];
	assign time_seconds_out = hwif_out[74-:8];
	assign time_minutes_out = hwif_out[66-:8];
	assign time_hours_out = hwif_out[58-:8];
	assign time_day_out = hwif_out[50-:8];
	assign time_month_out = hwif_out[42-:8];
	assign time_year_out = hwif_out[34-:8];
	assign alarm_seconds = hwif_out[26-:8];
	assign alarm_minutes = hwif_out[18-:8];
	assign alarm_hours = hwif_out[10-:8];
	assign alarm_sec_match_en = hwif_out[2];
	assign alarm_min_match_en = hwif_out[1];
	assign alarm_hour_match_en = hwif_out[0];
	initial _sv2v_0 = 0;
endmodule
