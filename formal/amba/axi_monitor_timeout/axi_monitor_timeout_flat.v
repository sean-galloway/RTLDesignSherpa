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
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter [0:0] IS_READ = 1;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 281) - 1:0] trans_table;
	input wire timer_tick;
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	reg [280:0] r_trans_table_local [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_timeout_detected;
	assign timeout_detected = r_timeout_detected;
	localparam [3:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 4'h0;
	localparam [3:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 4'h1;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 4'h2;
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_1
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_local[idx] <= 1'sb0;
			end
			r_timeout_detected <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_trans_table_local[idx] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 281+:281];
						if (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4)) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h0))
							r_timeout_detected[idx] <= 1'b0;
					end
			end
			if (timer_tick) begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table_local[idx][280] && !r_timeout_detected[idx]) begin
						if ((r_trans_table_local[idx][273-:3] == 3'h1) && !r_trans_table_local[idx][279]) begin
							r_trans_table_local[idx][211-:32] <= r_trans_table_local[idx][211-:32] + 1'b1;
							if (r_trans_table_local[idx][211-:32] >= {12'h000, cfg_addr_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_CMD_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((((r_trans_table_local[idx][273-:3] == 3'h1) || (r_trans_table_local[idx][273-:3] == 3'h2)) && r_trans_table_local[idx][279]) && r_trans_table_local[idx][278]) && !r_trans_table_local[idx][277]) begin
							r_trans_table_local[idx][179-:32] <= r_trans_table_local[idx][179-:32] + 1'b1;
							if (r_trans_table_local[idx][179-:32] >= {12'h000, cfg_data_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_DATA_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((!IS_READ && (r_trans_table_local[idx][273-:3] == 3'h2)) && r_trans_table_local[idx][277]) && !r_trans_table_local[idx][276]) begin
							r_trans_table_local[idx][147-:32] <= r_trans_table_local[idx][147-:32] + 1'b1;
							if (r_trans_table_local[idx][147-:32] >= {12'h000, cfg_resp_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_RESP_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
					end
			end
		end
endmodule
