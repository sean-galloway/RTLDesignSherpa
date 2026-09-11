module cdc_4_phase_handshake (
	clk_src,
	rst_src_n,
	src_valid,
	src_ready,
	src_data,
	src_timeout,
	clk_dst,
	rst_dst_n,
	dst_valid,
	dst_ready,
	dst_data
);
	parameter signed [31:0] DATA_WIDTH = 8;
	parameter signed [31:0] SYNC_STAGES = 3;
	parameter signed [31:0] TIMEOUT_CYCLES = 0;
	parameter [0:0] FAST_PATH = 1'b0;
	input wire clk_src;
	input wire rst_src_n;
	input wire src_valid;
	output reg src_ready;
	input wire [DATA_WIDTH - 1:0] src_data;
	output reg src_timeout;
	input wire clk_dst;
	input wire rst_dst_n;
	output reg dst_valid;
	input wire dst_ready;
	output wire [DATA_WIDTH - 1:0] dst_data;
	reg r_req_src;
	reg r_ack_dst;
	reg [DATA_WIDTH - 1:0] r_src_data_hold;
	(* ASYNC_REG = "TRUE" *) reg [DATA_WIDTH - 1:0] r_dst_data;
	(* ASYNC_REG = "TRUE" *) reg [SYNC_STAGES - 1:0] r_req_sync;
	(* ASYNC_REG = "TRUE" *) reg [SYNC_STAGES - 1:0] r_ack_sync;
	wire w_req_sync;
	wire w_ack_sync;
	reg [1:0] r_src_state;
	reg [1:0] r_dst_state;
	localparam signed [31:0] TIMEOUT_CW = (TIMEOUT_CYCLES > 1 ? $clog2(TIMEOUT_CYCLES + 1) : 1);
	always @(posedge clk_src or negedge rst_src_n)
		if (!rst_src_n)
			r_ack_sync <= 1'sb0;
		else
			r_ack_sync <= {r_ack_sync[SYNC_STAGES - 2:0], r_ack_dst};
	assign w_ack_sync = r_ack_sync[SYNC_STAGES - 1];
	always @(posedge clk_src or negedge rst_src_n)
		if (!rst_src_n) begin
			r_src_state <= 2'd0;
			r_req_src <= 1'b0;
			src_ready <= 1'b0;
			r_src_data_hold <= 1'sb0;
		end
		else
			(* full_case, parallel_case *)
			case (r_src_state)
				2'd0: begin
					src_ready <= 1'b1;
					r_req_src <= 1'b0;
					if (src_valid) begin
						r_src_data_hold <= src_data;
						r_req_src <= 1'b1;
						src_ready <= 1'b0;
						r_src_state <= 2'd1;
					end
				end
				2'd1: begin
					src_ready <= 1'b0;
					if (w_ack_sync) begin
						r_req_src <= 1'b0;
						r_src_state <= 2'd2;
					end
				end
				2'd2: begin
					src_ready <= 1'b0;
					r_req_src <= 1'b0;
					if (!w_ack_sync) begin
						src_ready <= 1'b1;
						r_src_state <= 2'd0;
					end
				end
				default: begin
					r_src_state <= 2'd0;
					src_ready <= 1'b1;
					r_req_src <= 1'b0;
				end
			endcase
	generate
		if (TIMEOUT_CYCLES > 0) begin : g_timeout
			reg [TIMEOUT_CW - 1:0] r_timeout_cnt;
			always @(posedge clk_src or negedge rst_src_n)
				if (!rst_src_n) begin
					r_timeout_cnt <= 1'sb0;
					src_timeout <= 1'b0;
				end
				else if (r_src_state == 2'd0) begin
					r_timeout_cnt <= 1'sb0;
					src_timeout <= 1'b0;
				end
				else if (r_timeout_cnt == TIMEOUT_CYCLES[TIMEOUT_CW - 1:0])
					src_timeout <= 1'b1;
				else
					r_timeout_cnt <= r_timeout_cnt + 1'b1;
		end
		else begin : g_no_timeout
			wire [1:1] sv2v_tmp_D5E08;
			assign sv2v_tmp_D5E08 = 1'b0;
			always @(*) src_timeout = sv2v_tmp_D5E08;
		end
	endgenerate
	always @(posedge clk_dst or negedge rst_dst_n)
		if (!rst_dst_n)
			r_req_sync <= 1'sb0;
		else
			r_req_sync <= {r_req_sync[SYNC_STAGES - 2:0], r_req_src};
	assign w_req_sync = r_req_sync[SYNC_STAGES - 1];
	always @(posedge clk_dst or negedge rst_dst_n)
		if (!rst_dst_n) begin
			r_dst_state <= 2'd0;
			r_ack_dst <= 1'b0;
			dst_valid <= 1'b0;
			r_dst_data <= 1'sb0;
		end
		else
			(* full_case, parallel_case *)
			case (r_dst_state)
				2'd0: begin
					r_ack_dst <= 1'b0;
					if (w_req_sync) begin
						r_dst_data <= r_src_data_hold;
						if (FAST_PATH && dst_ready) begin
							dst_valid <= 1'b1;
							r_ack_dst <= 1'b1;
							r_dst_state <= 2'd2;
						end
						else begin
							dst_valid <= 1'b1;
							r_dst_state <= 2'd1;
						end
					end
					else
						dst_valid <= 1'b0;
				end
				2'd1: begin
					dst_valid <= 1'b1;
					if (dst_ready) begin
						r_ack_dst <= 1'b1;
						dst_valid <= 1'b0;
						r_dst_state <= 2'd2;
					end
					else if (!w_req_sync) begin
						dst_valid <= 1'b0;
						r_dst_state <= 2'd0;
					end
				end
				2'd2: begin
					dst_valid <= 1'b0;
					if (!w_req_sync) begin
						r_ack_dst <= 1'b0;
						r_dst_state <= 2'd0;
					end
				end
				default: begin
					r_dst_state <= 2'd0;
					r_ack_dst <= 1'b0;
					dst_valid <= 1'b0;
				end
			endcase
	assign dst_data = r_dst_data;
endmodule
