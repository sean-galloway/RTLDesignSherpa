module apbtodescr (
	clk,
	rst_n,
	apb_cmd_valid,
	apb_cmd_ready,
	apb_cmd_addr,
	apb_cmd_wdata,
	apb_cmd_write,
	apb_rsp_valid,
	apb_rsp_ready,
	apb_rsp_rdata,
	apb_rsp_error,
	desc_apb_valid,
	desc_apb_ready,
	desc_apb_addr,
	apb_descriptor_kickoff_hit
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] NUM_CHANNELS = 8;
	input wire clk;
	input wire rst_n;
	input wire apb_cmd_valid;
	output wire apb_cmd_ready;
	input wire [ADDR_WIDTH - 1:0] apb_cmd_addr;
	input wire [DATA_WIDTH - 1:0] apb_cmd_wdata;
	input wire apb_cmd_write;
	output wire apb_rsp_valid;
	input wire apb_rsp_ready;
	output wire [DATA_WIDTH - 1:0] apb_rsp_rdata;
	output wire apb_rsp_error;
	output reg [NUM_CHANNELS - 1:0] desc_apb_valid;
	input wire [NUM_CHANNELS - 1:0] desc_apb_ready;
	output reg [(NUM_CHANNELS * 64) - 1:0] desc_apb_addr;
	output wire apb_descriptor_kickoff_hit;
	wire [2:0] channel_id;
	wire addr_in_range;
	reg [2:0] r_state;
	reg [2:0] w_next_state;
	reg [2:0] r_channel_id;
	reg [DATA_WIDTH - 1:0] r_wdata_low;
	reg [DATA_WIDTH - 1:0] r_wdata_high;
	reg r_error;
	wire r_is_high_write;
	assign channel_id = apb_cmd_addr[5:3];
	assign r_is_high_write = apb_cmd_addr[2];
	assign addr_in_range = {20'h00000, apb_cmd_addr[11:0]} < (NUM_CHANNELS * 8);
	always @(posedge clk)
		if (!rst_n)
			r_state <= 3'b000;
		else
			r_state <= w_next_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_state;
		case (r_state)
			3'b000:
				if (apb_cmd_valid && !apb_cmd_write)
					w_next_state = 3'b001;
				else if (apb_cmd_valid && apb_cmd_write) begin
					if (!r_is_high_write)
						w_next_state = 3'b001;
					else
						w_next_state = 3'b001;
				end
			3'b001:
				if (apb_rsp_ready) begin
					if (r_error)
						w_next_state = 3'b000;
					else
						w_next_state = 3'b010;
				end
			3'b010:
				if (apb_cmd_valid && !apb_cmd_write)
					w_next_state = 3'b100;
				else if (apb_cmd_valid && apb_cmd_write) begin
					if (r_is_high_write && (channel_id == r_channel_id))
						w_next_state = 3'b011;
					else
						w_next_state = 3'b100;
				end
			3'b011:
				if (r_error)
					w_next_state = 3'b100;
				else if (desc_apb_ready[r_channel_id])
					w_next_state = 3'b100;
			3'b100:
				if (apb_rsp_ready)
					w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk)
		if (!rst_n) begin
			r_channel_id <= 3'h0;
			r_wdata_low <= 1'sb0;
			r_wdata_high <= 1'sb0;
			r_error <= 1'b0;
		end
		else begin
			if ((r_state == 3'b000) && apb_cmd_valid) begin
				if (!apb_cmd_write)
					r_error <= 1'b1;
				else if (!addr_in_range)
					r_error <= 1'b1;
				else if (r_is_high_write)
					r_error <= 1'b1;
				else begin
					r_channel_id <= channel_id;
					r_wdata_low <= apb_cmd_wdata;
					r_error <= 1'b0;
				end
			end
			if ((r_state == 3'b010) && apb_cmd_valid) begin
				if (!apb_cmd_write)
					r_error <= 1'b1;
				else if (!r_is_high_write)
					r_error <= 1'b1;
				else if (channel_id != r_channel_id)
					r_error <= 1'b1;
				else begin
					r_wdata_high <= apb_cmd_wdata;
					r_error <= 1'b0;
				end
			end
		end
	assign apb_cmd_ready = (r_state == 3'b000) || (r_state == 3'b010);
	assign apb_rsp_valid = (r_state == 3'b001) || (r_state == 3'b100);
	assign apb_rsp_rdata = 1'sb0;
	assign apb_rsp_error = r_error;
	always @(*) begin
		if (_sv2v_0)
			;
		desc_apb_valid = 1'sb0;
		if ((r_state == 3'b011) && !r_error)
			desc_apb_valid[r_channel_id] = 1'b1;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				desc_apb_addr[ch * 64+:64] = {r_wdata_high, r_wdata_low};
		end
	end
	assign apb_descriptor_kickoff_hit = ((r_state == 3'b011) || (r_state == 3'b100)) && !r_error;
	initial _sv2v_0 = 0;
endmodule
