module wb4_retry (
	clk,
	aresetn,
	cfg_max_retries,
	cfg_retry_delay,
	cmd_valid,
	cmd_ready,
	cmd_we,
	cmd_adr,
	cmd_dat,
	cmd_sel,
	rsp_valid,
	rsp_ready,
	rsp_status,
	rsp_dat,
	mst_cmd_valid,
	mst_cmd_ready,
	mst_cmd_we,
	mst_cmd_adr,
	mst_cmd_dat,
	mst_cmd_sel,
	mst_rsp_valid,
	mst_rsp_ready,
	mst_rsp_status,
	mst_rsp_dat,
	retry_count,
	active_count
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] INFLIGHT = 1;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = DW / 8;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	input wire clk;
	input wire aresetn;
	input wire [7:0] cfg_max_retries;
	input wire [15:0] cfg_retry_delay;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_we;
	input wire [AW - 1:0] cmd_adr;
	input wire [DW - 1:0] cmd_dat;
	input wire [SW - 1:0] cmd_sel;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [STW - 1:0] rsp_status;
	output wire [DW - 1:0] rsp_dat;
	output wire mst_cmd_valid;
	input wire mst_cmd_ready;
	output wire mst_cmd_we;
	output wire [AW - 1:0] mst_cmd_adr;
	output wire [DW - 1:0] mst_cmd_dat;
	output wire [SW - 1:0] mst_cmd_sel;
	input wire mst_rsp_valid;
	output wire mst_rsp_ready;
	input wire [STW - 1:0] mst_rsp_status;
	input wire [DW - 1:0] mst_rsp_dat;
	output reg [31:0] retry_count;
	output wire [7:0] active_count;
	localparam signed [31:0] N = INFLIGHT;
	localparam signed [31:0] IW = (N > 1 ? $clog2(N) : 1);
	localparam signed [31:0] CW = $clog2(N + 1);
	reg [1:0] r_state [0:N - 1];
	reg r_we [0:N - 1];
	reg [AW - 1:0] r_adr [0:N - 1];
	reg [DW - 1:0] r_dat [0:N - 1];
	reg [SW - 1:0] r_sel [0:N - 1];
	reg [7:0] r_retries [0:N - 1];
	reg [15:0] r_timer [0:N - 1];
	reg [STW - 1:0] r_status [0:N - 1];
	reg [DW - 1:0] r_dat_r [0:N - 1];
	reg [IW - 1:0] r_head;
	reg [IW - 1:0] r_tail;
	reg [CW - 1:0] r_count;
	wire w_full;
	wire w_empty;
	reg [IW - 1:0] r_log [0:N - 1];
	reg [IW - 1:0] r_log_head;
	reg [IW - 1:0] r_log_tail;
	reg [CW - 1:0] r_log_count;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [IW - 1:0] f_wrap;
		input reg [IW - 1:0] i;
		f_wrap = (sv2v_cast_32(i) == (N - 1) ? {IW {1'sb0}} : i + 1'b1);
	endfunction
	assign w_full = sv2v_cast_32(r_count) >= N;
	assign w_empty = r_count == {CW {1'sb0}};
	reg w_retry_valid;
	reg [IW - 1:0] w_retry_idx;
	function automatic [IW - 1:0] sv2v_cast_83959;
		input reg [IW - 1:0] inp;
		sv2v_cast_83959 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_retry_valid = 1'b0;
		w_retry_idx = r_head;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = N - 1; i >= 0; i = i - 1)
				begin : sv2v_autoblock_2
					reg [IW - 1:0] idx;
					idx = sv2v_cast_83959((sv2v_cast_32(r_head) + i) % N);
					if (((i < sv2v_cast_32(r_count)) && (r_state[idx] == 2'd2)) && (r_timer[idx] == {16 {1'sb0}})) begin
						w_retry_valid = 1'b1;
						w_retry_idx = idx;
					end
				end
		end
	end
	wire w_issue_new;
	wire w_issue_retry;
	wire w_mst_issue;
	assign mst_cmd_valid = w_retry_valid || (cmd_valid && !w_full);
	assign w_mst_issue = mst_cmd_valid && mst_cmd_ready;
	assign w_issue_retry = w_mst_issue && w_retry_valid;
	assign w_issue_new = w_mst_issue && !w_retry_valid;
	assign cmd_ready = (!w_retry_valid && !w_full) && mst_cmd_ready;
	assign mst_cmd_we = (w_retry_valid ? r_we[w_retry_idx] : cmd_we);
	assign mst_cmd_adr = (w_retry_valid ? r_adr[w_retry_idx] : cmd_adr);
	assign mst_cmd_dat = (w_retry_valid ? r_dat[w_retry_idx] : cmd_dat);
	assign mst_cmd_sel = (w_retry_valid ? r_sel[w_retry_idx] : cmd_sel);
	wire w_rsp_take;
	wire w_rsp_is_rty;
	wire w_rsp_retry;
	wire [IW - 1:0] w_rsp_idx;
	assign mst_rsp_ready = r_log_count != {CW {1'sb0}};
	assign w_rsp_take = mst_rsp_valid && mst_rsp_ready;
	assign w_rsp_idx = r_log[r_log_head];
	function automatic [1:0] sv2v_cast_1AA03;
		input reg [1:0] inp;
		sv2v_cast_1AA03 = inp;
	endfunction
	function automatic [STW - 1:0] sv2v_cast_C2FF6;
		input reg [STW - 1:0] inp;
		sv2v_cast_C2FF6 = inp;
	endfunction
	assign w_rsp_is_rty = mst_rsp_status == sv2v_cast_C2FF6(sv2v_cast_1AA03(2'b10));
	assign w_rsp_retry = (w_rsp_take && w_rsp_is_rty) && (r_retries[w_rsp_idx] < cfg_max_retries);
	wire w_rsp_pop;
	assign rsp_valid = !w_empty && (r_state[r_head] == 2'd3);
	assign rsp_status = r_status[r_head];
	assign rsp_dat = r_dat_r[r_head];
	assign w_rsp_pop = rsp_valid && rsp_ready;
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign active_count = sv2v_cast_8(r_count);
	function automatic [CW - 1:0] sv2v_cast_3D2D3;
		input reg [CW - 1:0] inp;
		sv2v_cast_3D2D3 = inp;
	endfunction
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			r_head <= 1'sb0;
			r_tail <= 1'sb0;
			r_count <= 1'sb0;
			r_log_head <= 1'sb0;
			r_log_tail <= 1'sb0;
			r_log_count <= 1'sb0;
			retry_count <= 1'sb0;
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					begin
						r_state[i] <= 2'd0;
						r_we[i] <= 1'b0;
						r_adr[i] <= 1'sb0;
						r_dat[i] <= 1'sb0;
						r_sel[i] <= 1'sb0;
						r_retries[i] <= 1'sb0;
						r_timer[i] <= 1'sb0;
						r_status[i] <= 1'sb0;
						r_dat_r[i] <= 1'sb0;
						r_log[i] <= 1'sb0;
					end
			end
		end
		else begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					if ((r_state[i] == 2'd2) && (r_timer[i] != {16 {1'sb0}}))
						r_timer[i] <= r_timer[i] - 1'b1;
			end
			if (w_issue_new) begin
				r_state[r_tail] <= 2'd1;
				r_we[r_tail] <= cmd_we;
				r_adr[r_tail] <= cmd_adr;
				r_dat[r_tail] <= cmd_dat;
				r_sel[r_tail] <= cmd_sel;
				r_retries[r_tail] <= 1'sb0;
				r_tail <= f_wrap(r_tail);
			end
			if (w_issue_retry)
				r_state[w_retry_idx] <= 2'd1;
			if (w_mst_issue) begin
				r_log[r_log_tail] <= (w_retry_valid ? w_retry_idx : r_tail);
				r_log_tail <= f_wrap(r_log_tail);
			end
			if (w_rsp_take) begin
				r_log_head <= f_wrap(r_log_head);
				if (w_rsp_retry) begin
					r_state[w_rsp_idx] <= 2'd2;
					r_retries[w_rsp_idx] <= r_retries[w_rsp_idx] + 1'b1;
					r_timer[w_rsp_idx] <= cfg_retry_delay;
					retry_count <= retry_count + 1'b1;
				end
				else begin
					r_state[w_rsp_idx] <= 2'd3;
					r_status[w_rsp_idx] <= mst_rsp_status;
					r_dat_r[w_rsp_idx] <= mst_rsp_dat;
				end
			end
			if (w_rsp_pop) begin
				r_state[r_head] <= 2'd0;
				r_head <= f_wrap(r_head);
			end
			r_count <= (r_count + sv2v_cast_3D2D3(w_issue_new)) - sv2v_cast_3D2D3(w_rsp_pop);
			r_log_count <= (r_log_count + sv2v_cast_3D2D3(w_mst_issue)) - sv2v_cast_3D2D3(w_rsp_take);
		end
	reg f_past_valid;
	initial f_past_valid = 1'b0;
	always @(posedge clk) f_past_valid <= 1'b1;
	always @(posedge clk)
		if ((f_past_valid && aresetn) && $past(aresetn)) begin
			assert (sv2v_cast_32(r_count) <= N) ;
			assert (sv2v_cast_32(r_log_count) <= N) ;
			assert (r_log_count <= r_count) ;
			assert (!(w_issue_retry && cmd_ready)) ;
			assert (!rsp_valid || (r_state[r_head] == 2'd3)) ;
		end
	initial _sv2v_0 = 0;
endmodule
