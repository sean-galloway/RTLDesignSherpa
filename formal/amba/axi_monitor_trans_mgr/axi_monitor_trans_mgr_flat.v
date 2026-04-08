module axi_monitor_trans_mgr (
	aclk,
	aresetn,
	cmd_valid,
	cmd_ready,
	cmd_id,
	cmd_addr,
	cmd_len,
	cmd_size,
	cmd_burst,
	data_valid,
	data_ready,
	data_id,
	data_last,
	data_resp,
	resp_valid,
	resp_ready,
	resp_id,
	resp_code,
	timestamp,
	i_event_reported_flags,
	trans_table,
	active_count,
	state_change
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire [IW - 1:0] cmd_id;
	input wire [AW - 1:0] cmd_addr;
	input wire [7:0] cmd_len;
	input wire [2:0] cmd_size;
	input wire [1:0] cmd_burst;
	input wire data_valid;
	input wire data_ready;
	input wire [IW - 1:0] data_id;
	input wire data_last;
	input wire [1:0] data_resp;
	input wire resp_valid;
	input wire resp_ready;
	input wire [IW - 1:0] resp_id;
	input wire [1:0] resp_code;
	input wire [31:0] timestamp;
	input wire [MAX_TRANSACTIONS - 1:0] i_event_reported_flags;
	output wire [(MAX_TRANSACTIONS * 281) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	reg [(MAX_TRANSACTIONS * 281) - 1:0] r_trans_table;
	reg [(MAX_TRANSACTIONS * 281) - 1:0] r_trans_table_prev;
	assign trans_table = r_trans_table;
	reg [7:0] r_active_count;
	assign active_count = r_active_count;
	reg [MAX_TRANSACTIONS - 1:0] r_state_change;
	assign state_change = r_state_change;
	localparam signed [31:0] ADDR_PAD_BITS = (AW > 32 ? 0 : 32 - AW);
	localparam [0:0] ADDR_NEEDS_TRUNC = AW > 32;
	reg signed [31:0] w_addr_trans_idx;
	reg signed [31:0] w_addr_free_idx;
	reg signed [31:0] w_data_trans_idx;
	reg signed [31:0] w_data_free_idx;
	reg signed [31:0] w_resp_trans_idx;
	reg signed [31:0] w_resp_free_idx;
	reg [5:0] w_addr_chan_idx;
	reg [MAX_TRANSACTIONS - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_trans_idx = -1;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((w_addr_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == cmd_id))
					w_addr_trans_idx = idx;
		end
		w_addr_free_idx = -1;
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((w_addr_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
					w_addr_free_idx = idx;
		end
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
		if (IS_READ) begin
			w_data_trans_idx = -1;
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((w_data_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == data_id))
						w_data_trans_idx = idx;
			end
		end
		else begin
			w_data_trans_idx = -1;
			begin : sv2v_autoblock_4
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((((w_data_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && ((r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h1) || (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h2))) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 279]) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 277])
						w_data_trans_idx = idx;
			end
		end
		w_data_free_idx = -1;
		begin : sv2v_autoblock_5
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((w_data_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
					w_data_free_idx = idx;
		end
		if (!IS_READ) begin
			w_resp_trans_idx = -1;
			begin : sv2v_autoblock_6
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((w_resp_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == resp_id))
						w_resp_trans_idx = idx;
			end
			w_resp_free_idx = -1;
			begin : sv2v_autoblock_7
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if ((w_resp_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
						w_resp_free_idx = idx;
			end
		end
		else begin
			w_resp_trans_idx = -1;
			w_resp_free_idx = -1;
		end
		begin : sv2v_autoblock_8
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
					case (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3])
						3'h3: w_can_cleanup[idx] = r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275];
						3'h4, 3'h5: w_can_cleanup[idx] = r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275];
						default: w_can_cleanup[idx] = 1'b0;
					endcase
				else
					w_can_cleanup[idx] = 1'b0;
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_9
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_prev[((MAX_TRANSACTIONS - 1) - idx) * 281+:281] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= r_trans_table;
			begin : sv2v_autoblock_10
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && r_trans_table_prev[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) begin
						if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] != r_trans_table_prev[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3])
							r_state_change[idx] <= 1'b1;
						else
							r_state_change[idx] <= 1'b0;
					end
					else
						r_state_change[idx] <= 1'b0;
			end
		end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_11
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] <= 1'b0;
			end
			r_active_count <= 1'sb0;
		end
		else begin
			if (cmd_valid) begin
				if ((w_addr_trans_idx < 0) && (w_addr_free_idx >= 0)) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 280] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 273-:3] <= 3'h1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 238-:8] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= cmd_id;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 270-:32] <= (ADDR_NEEDS_TRUNC ? cmd_addr[31:0] : {{ADDR_PAD_BITS {1'b0}}, cmd_addr});
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 230-:8] <= cmd_len;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 222-:3] <= cmd_size;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 219-:2] <= cmd_burst;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 279] <= (cmd_ready ? 1'b1 : 1'b0);
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 211-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 278] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 277] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 276] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 3-:4] <= 4'h0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 275] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 179-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 147-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 115-:32] <= timestamp;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 19-:8] <= (IS_AXI ? cmd_len + 8'h01 : 8'h01);
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 11-:8] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 217-:6] <= w_addr_chan_idx;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 274] <= 1'b0;
					r_active_count <= r_active_count + 1'b1;
				end
			end
			if (cmd_valid && cmd_ready) begin
				if (w_addr_trans_idx >= 0) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 279] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 211-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 115-:32] <= timestamp;
				end
			end
			begin : sv2v_autoblock_12
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && w_can_cleanup[idx]) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] <= 1'b0;
						r_active_count <= r_active_count - 1'b1;
					end
			end
			begin : sv2v_autoblock_13
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (i_event_reported_flags[idx] && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275])
						r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275] <= 1'b1;
			end
		end
	localparam [3:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 4'h2;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_DECERR = 4'h1;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 4'h0;
	always @(posedge aclk)
		if (!aresetn)
			;
		else if (data_valid && data_ready) begin
			if (IS_READ) begin
				if (w_data_trans_idx >= 0) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 278] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] <= r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 179-:32] <= 1'sb0;
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] != 3'h4)
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h2;
					if (data_last) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 277] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 83-:32] <= timestamp;
					end
					if (data_resp[1]) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h4;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 3-:4] <= (data_resp[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
					end
					else if (data_last) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h3;
						if (ENABLE_PERF_PACKETS)
							;
					end
				end
				else if (w_data_free_idx >= 0) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 280] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 273-:3] <= 3'h5;
					if (IS_AXI) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= data_id;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= {24'h000000, data_id} % 64;
					end
					else begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 19-:8] <= 8'h01;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= 6'h00;
					end
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 278] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 277] <= data_last;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 11-:8] <= 8'h01;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 83-:32] <= timestamp;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_DATA_ORPHAN;
					r_active_count <= r_active_count + 1'b1;
				end
			end
			else if (w_data_trans_idx >= 0) begin
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 278] <= 1'b1;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] <= r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1'b1;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 179-:32] <= 1'sb0;
				if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] != 3'h4)
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h2;
				if (data_last || ((r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1) == r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 19-:8])) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 277] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 83-:32] <= timestamp;
					if (ENABLE_PERF_PACKETS)
						;
				end
			end
			else if (!IS_AXI && (w_data_free_idx >= 0)) begin
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 280] <= 1'b1;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 273-:3] <= 3'h5;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 278] <= 1'b1;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 277] <= data_last;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 11-:8] <= 8'h01;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 19-:8] <= 8'h01;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 83-:32] <= timestamp;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_DATA_ORPHAN;
				r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= 6'h00;
				r_active_count <= r_active_count + 1'b1;
			end
		end
	localparam [3:0] monitor_amba4_pkg_EVT_PROTOCOL = 4'h4;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 4'h3;
	generate
		if (!IS_READ) begin : gen_resp_processor
			always @(posedge aclk)
				if (!aresetn)
					;
				else if (resp_valid && resp_ready) begin
					if (w_resp_trans_idx >= 0) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 276] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 51-:32] <= timestamp;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 147-:32] <= 1'sb0;
						if (resp_code[1]) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= (resp_code[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
						end
						else if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 277]) begin
							if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] != 3'h4) begin
								r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h3;
								if (ENABLE_PERF_PACKETS)
									;
							end
						end
						else if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 278]) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_PROTOCOL;
						end
						else begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_PROTOCOL;
						end
					end
					else if (w_resp_free_idx >= 0) begin
						if (IS_AXI) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 280] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 273-:3] <= 3'h5;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= resp_id;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 276] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 51-:32] <= timestamp;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_RESP_ORPHAN;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 217-:6] <= resp_id % 64;
						end
						else begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 280] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 273-:3] <= 3'h5;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 276] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 51-:32] <= timestamp;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_RESP_ORPHAN;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 217-:6] <= 6'h00;
						end
						r_active_count <= r_active_count + 1'b1;
					end
				end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
