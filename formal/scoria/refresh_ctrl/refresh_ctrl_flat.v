module scoria_refresh_ctrl (
	mc_clk,
	mc_rst_n,
	t_refi_i,
	trefi_pb_i,
	refresh_burst_i,
	refpb_mode_i,
	enable_i,
	refi_reload_i,
	postpone_limit_i,
	pullin_limit_i,
	demand_i,
	elastic_en_i,
	pullin_idle_streak_i,
	postpone_demand_streak_i,
	tcr_en_i,
	trefi_derate_i,
	refresh_req_o,
	refresh_grant_i,
	grant_was_pb_i,
	pending_refreshes_o,
	refresh_drain_active_o,
	refresh_kind_o,
	refresh_bank_o,
	obs_refi_cnt_o,
	obs_drain_remaining_o,
	obs_bank_rotor_o,
	obs_grants_total_o,
	obs_pullin_credit_o,
	obs_postpone_events_o,
	obs_pullin_events_o
);
	parameter signed [31:0] NUM_BANKS = 8;
	parameter signed [31:0] BA_W = $clog2(NUM_BANKS);
	input wire mc_clk;
	input wire mc_rst_n;
	input wire [15:0] t_refi_i;
	input wire [15:0] trefi_pb_i;
	input wire [3:0] refresh_burst_i;
	input wire refpb_mode_i;
	input wire enable_i;
	input wire refi_reload_i;
	input wire [3:0] postpone_limit_i;
	input wire [3:0] pullin_limit_i;
	input wire demand_i;
	input wire elastic_en_i;
	input wire [7:0] pullin_idle_streak_i;
	input wire [6:0] postpone_demand_streak_i;
	input wire tcr_en_i;
	input wire [1:0] trefi_derate_i;
	output reg refresh_req_o;
	input wire refresh_grant_i;
	input wire grant_was_pb_i;
	output reg [3:0] pending_refreshes_o;
	output reg refresh_drain_active_o;
	output reg refresh_kind_o;
	output reg [BA_W - 1:0] refresh_bank_o;
	output reg [15:0] obs_refi_cnt_o;
	output reg [3:0] obs_drain_remaining_o;
	output reg [BA_W - 1:0] obs_bank_rotor_o;
	output reg [15:0] obs_grants_total_o;
	output reg [3:0] obs_pullin_credit_o;
	output reg [15:0] obs_postpone_events_o;
	output reg [15:0] obs_pullin_events_o;
	reg [15:0] r_refi_cnt;
	reg [3:0] r_pending;
	reg [6:0] r_demand_streak;
	reg [15:0] r_postpone_events;
	reg [15:0] r_pullin_events;
	localparam [3:0] MAX_PENDING = 4'd8;
	wire w_refi_expired;
	assign w_refi_expired = r_refi_cnt == 16'd0;
	wire [15:0] w_refi_eff;
	assign w_refi_eff = (!refpb_mode_i ? t_refi_i : (trefi_pb_i != 16'd0 ? trefi_pb_i : t_refi_i >> 3));
	wire [1:0] w_derate_shift;
	wire [15:0] w_refi_eff_derated;
	assign w_derate_shift = (!tcr_en_i ? 2'd0 : (trefi_derate_i > 2'd2 ? 2'd2 : trefi_derate_i));
	assign w_refi_eff_derated = w_refi_eff >> w_derate_shift;
	localparam [3:0] POSTPONE_MAX = MAX_PENDING - 4'd2;
	wire [3:0] w_post_eff;
	wire [3:0] w_pull_eff;
	assign w_post_eff = (postpone_limit_i > POSTPONE_MAX ? POSTPONE_MAX : postpone_limit_i);
	assign w_pull_eff = (pullin_limit_i > 4'd8 ? 4'd8 : pullin_limit_i);
	reg [3:0] r_pullin;
	wire w_grant_accept;
	wire w_grant_early;
	assign w_grant_accept = refresh_grant_i && (r_pending > 4'd0);
	assign w_grant_early = (refresh_grant_i && (r_pending == 4'd0)) && (r_pullin < 4'd8);
	reg [7:0] r_idle_cnt;
	wire w_idle;
	assign w_idle = r_idle_cnt >= (elastic_en_i ? pullin_idle_streak_i : 8'd16);
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n)
			r_idle_cnt <= 1'sb0;
		else if (demand_i)
			r_idle_cnt <= 1'sb0;
		else if (!w_idle)
			r_idle_cnt <= r_idle_cnt + 1'b1;
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n) begin
			r_refi_cnt <= 16'd0;
			r_pending <= 4'd0;
			r_pullin <= 4'd0;
			r_demand_streak <= 7'd0;
			r_postpone_events <= 16'd0;
			r_pullin_events <= 16'd0;
		end
		else begin
			if (!enable_i || refi_reload_i)
				r_refi_cnt <= w_refi_eff_derated;
			else if (w_refi_expired)
				r_refi_cnt <= w_refi_eff_derated;
			else
				r_refi_cnt <= r_refi_cnt - 16'd1;
			if (!demand_i)
				r_demand_streak <= 7'd0;
			else if (r_demand_streak != 7'd127)
				r_demand_streak <= r_demand_streak + 7'd1;
			begin : sv2v_autoblock_1
				reg [3:0] pend_n;
				reg [3:0] pull_n;
				reg pend_tick;
				pend_n = r_pending;
				pull_n = r_pullin;
				pend_tick = 1'b0;
				if (enable_i && w_refi_expired) begin
					if (pull_n > 4'd0)
						pull_n = pull_n - 4'd1;
					else if (pend_n < MAX_PENDING) begin
						pend_n = pend_n + 4'd1;
						pend_tick = 1'b1;
					end
				end
				if (refresh_grant_i) begin
					if (pend_n > 4'd0)
						pend_n = pend_n - 4'd1;
					else if (pull_n < 4'd8)
						pull_n = pull_n + 4'd1;
				end
				r_pending <= pend_n;
				r_pullin <= pull_n;
				if (((((pend_tick && elastic_en_i) && !w_idle) && (r_demand_streak >= postpone_demand_streak_i)) && (r_pending <= w_post_eff)) && (r_postpone_events != 16'hffff))
					r_postpone_events <= r_postpone_events + 16'd1;
				if (w_grant_early && (r_pullin_events != 16'hffff))
					r_pullin_events <= r_pullin_events + 16'd1;
			end
		end
	reg [3:0] r_burst_remaining;
	wire [3:0] w_drain_load;
	assign w_drain_load = (refresh_burst_i > r_pending ? r_pending : refresh_burst_i);
	wire w_drain_active;
	assign w_drain_active = ((r_burst_remaining > 4'd0) && (r_pending > 4'd0)) && refresh_req_o;
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n)
			r_burst_remaining <= 4'd0;
		else if (w_grant_accept && (r_burst_remaining > 4'd0))
			r_burst_remaining <= r_burst_remaining - 4'd1;
		else if ((r_burst_remaining == 4'd0) && (r_pending > 4'd0))
			r_burst_remaining <= (w_drain_load == 4'd0 ? 4'd1 : w_drain_load);
	reg [BA_W - 1:0] r_bank_rotor;
	reg [15:0] r_grants_total;
	function automatic signed [BA_W - 1:0] sv2v_cast_6B15A_signed;
		input reg signed [BA_W - 1:0] inp;
		sv2v_cast_6B15A_signed = inp;
	endfunction
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n) begin
			r_bank_rotor <= 1'sb0;
			r_grants_total <= 16'd0;
		end
		else if (w_grant_accept || w_grant_early) begin
			r_grants_total <= r_grants_total + 16'd1;
			if (grant_was_pb_i) begin
				if (r_bank_rotor == sv2v_cast_6B15A_signed(NUM_BANKS - 1))
					r_bank_rotor <= 1'sb0;
				else
					r_bank_rotor <= r_bank_rotor + sv2v_cast_6B15A_signed(1);
			end
		end
	wire w_req;
	assign w_req = enable_i && (w_idle ? (r_pending > 4'd0) || (r_pullin < w_pull_eff) : (elastic_en_i && (r_demand_streak < postpone_demand_streak_i) ? r_pending > 4'd0 : r_pending > w_post_eff));
	always @(posedge mc_clk or negedge mc_rst_n)
		if (!mc_rst_n) begin
			refresh_req_o <= 1'b0;
			pending_refreshes_o <= 4'd0;
			refresh_drain_active_o <= 1'b0;
			refresh_kind_o <= 1'b0;
			refresh_bank_o <= 1'sb0;
			obs_refi_cnt_o <= 16'd0;
			obs_drain_remaining_o <= 4'd0;
			obs_bank_rotor_o <= 1'sb0;
			obs_grants_total_o <= 16'd0;
			obs_pullin_credit_o <= 4'd0;
			obs_postpone_events_o <= 16'd0;
			obs_pullin_events_o <= 16'd0;
		end
		else begin
			refresh_req_o <= w_req;
			pending_refreshes_o <= r_pending;
			refresh_drain_active_o <= w_drain_active;
			refresh_kind_o <= refpb_mode_i;
			refresh_bank_o <= r_bank_rotor;
			obs_refi_cnt_o <= r_refi_cnt;
			obs_drain_remaining_o <= r_burst_remaining;
			obs_bank_rotor_o <= r_bank_rotor;
			obs_grants_total_o <= r_grants_total;
			obs_pullin_credit_o <= r_pullin;
			obs_postpone_events_o <= r_postpone_events;
			obs_pullin_events_o <= r_pullin_events;
		end
endmodule
