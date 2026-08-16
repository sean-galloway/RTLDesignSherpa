module axi_monitor_timeout (
	aclk,
	aresetn,
	trans_table,
	timer_tick,
	cfg_addr_cnt,
	cfg_data_cnt,
	cfg_resp_cnt,
	cfg_timeout_enable,
	timeout_detected
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter [0:0] IS_READ = 1;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire timer_tick;
	input wire [15:0] cfg_addr_cnt;
	input wire [15:0] cfg_data_cnt;
	input wire [15:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	localparam signed [31:0] TIMER_W = 16;
	reg [15:0] r_addr_timer [0:MAX_TRANSACTIONS - 1];
	reg [15:0] r_data_timer [0:MAX_TRANSACTIONS - 1];
	reg [15:0] r_resp_timer [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_timeout_detected;
	assign timeout_detected = (cfg_timeout_enable ? r_timeout_detected : {MAX_TRANSACTIONS {1'b0}});
	reg [MAX_TRANSACTIONS - 1:0] w_addr_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_data_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_resp_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_slot_retired;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				begin
					w_addr_pending[idx] = (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h1)) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 283];
					w_data_pending[idx] = ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h1) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h2))) && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 283]) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 281];
					w_resp_pending[idx] = (((!IS_READ && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284]) && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h2)) && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 281]) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 280];
					w_slot_retired[idx] = (!trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h0);
				end
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_addr_timer[idx] <= 1'sb0;
						r_data_timer[idx] <= 1'sb0;
						r_resp_timer[idx] <= 1'sb0;
					end
			end
			r_timeout_detected <= 1'sb0;
		end
		else if (!cfg_timeout_enable) begin
			r_timeout_detected <= 1'sb0;
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_addr_timer[idx] <= 1'sb0;
						r_data_timer[idx] <= 1'sb0;
						r_resp_timer[idx] <= 1'sb0;
					end
			end
		end
		else begin : sv2v_autoblock_4
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				begin
					if (w_slot_retired[idx])
						r_timeout_detected[idx] <= 1'b0;
					if (!w_addr_pending[idx])
						r_addr_timer[idx] <= 1'sb0;
					if (!w_data_pending[idx])
						r_data_timer[idx] <= 1'sb0;
					if (!w_resp_pending[idx])
						r_resp_timer[idx] <= 1'sb0;
					if ((cfg_timeout_enable && timer_tick) && !r_timeout_detected[idx]) begin
						if (w_addr_pending[idx]) begin
							if (r_addr_timer[idx] >= cfg_addr_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_addr_timer[idx] <= r_addr_timer[idx] + 1'b1;
						end
						if (w_data_pending[idx]) begin
							if (r_data_timer[idx] >= cfg_data_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_data_timer[idx] <= r_data_timer[idx] + 1'b1;
						end
						if (w_resp_pending[idx]) begin
							if (r_resp_timer[idx] >= cfg_resp_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_resp_timer[idx] <= r_resp_timer[idx] + 1'b1;
						end
					end
				end
		end
	initial _sv2v_0 = 0;
endmodule
