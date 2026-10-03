module scoria_bank_timer (
	clk,
	rst_n,
	t_rcd_i,
	t_rp_i,
	t_ras_i,
	t_rc_i,
	t_wr_i,
	t_rtp_i,
	set_act_i,
	set_rd_i,
	set_wr_i,
	set_pre_i,
	set_ap_i,
	row_i,
	safe_act_o,
	safe_rd_o,
	safe_wr_o,
	safe_pre_o,
	safe_act_la_o,
	safe_rdwr_la_o,
	safe_pre_la_o,
	row_valid_o,
	open_row_o,
	state_o,
	obs_rcd_nz_o,
	obs_preblk_nz_o,
	obs_ras_nz_o,
	obs_ap_pending_o
);
	reg _sv2v_0;
	parameter signed [31:0] ROW_WIDTH = 14;
	parameter signed [31:0] TW = 8;
	parameter signed [31:0] LA = 0;
	input wire clk;
	input wire rst_n;
	input wire [TW - 1:0] t_rcd_i;
	input wire [TW - 1:0] t_rp_i;
	input wire [TW - 1:0] t_ras_i;
	input wire [TW - 1:0] t_rc_i;
	input wire [TW - 1:0] t_wr_i;
	input wire [TW - 1:0] t_rtp_i;
	input wire set_act_i;
	input wire set_rd_i;
	input wire set_wr_i;
	input wire set_pre_i;
	input wire set_ap_i;
	input wire [ROW_WIDTH - 1:0] row_i;
	output wire safe_act_o;
	output wire safe_rd_o;
	output wire safe_wr_o;
	output wire safe_pre_o;
	output wire safe_act_la_o;
	output wire safe_rdwr_la_o;
	output wire safe_pre_la_o;
	output wire row_valid_o;
	output wire [ROW_WIDTH - 1:0] open_row_o;
	output reg [2:0] state_o;
	output wire obs_rcd_nz_o;
	output wire obs_preblk_nz_o;
	output wire obs_ras_nz_o;
	output wire obs_ap_pending_o;
	reg [TW - 1:0] r_rcd;
	reg [TW - 1:0] r_ras;
	reg [TW - 1:0] r_rc;
	reg [TW - 1:0] r_rp;
	reg [TW - 1:0] r_preblk;
	reg r_row_valid;
	reg [ROW_WIDTH - 1:0] r_open_row;
	reg r_ap_pending;
	wire w_ap_fire;
	assign w_ap_fire = (r_ap_pending && (r_preblk == {TW {1'sb0}})) && (r_ras == {TW {1'sb0}});
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_rcd <= 1'sb0;
			r_ras <= 1'sb0;
			r_rc <= 1'sb0;
			r_rp <= 1'sb0;
			r_preblk <= 1'sb0;
			r_row_valid <= 1'b0;
			r_open_row <= 1'sb0;
			r_ap_pending <= 1'b0;
		end
		else begin
			if (set_act_i)
				r_rcd <= t_rcd_i;
			else if (r_rcd != {TW {1'sb0}})
				r_rcd <= r_rcd - 1'b1;
			if (set_act_i)
				r_ras <= t_ras_i;
			else if (r_ras != {TW {1'sb0}})
				r_ras <= r_ras - 1'b1;
			if (set_act_i)
				r_rc <= t_rc_i;
			else if (r_rc != {TW {1'sb0}})
				r_rc <= r_rc - 1'b1;
			if (set_pre_i || w_ap_fire)
				r_rp <= t_rp_i;
			else if (r_rp != {TW {1'sb0}})
				r_rp <= r_rp - 1'b1;
			if (set_rd_i)
				r_preblk <= t_rtp_i;
			else if (set_wr_i)
				r_preblk <= t_wr_i;
			else if (r_preblk != {TW {1'sb0}})
				r_preblk <= r_preblk - 1'b1;
			if (set_act_i) begin
				r_row_valid <= 1'b1;
				r_open_row <= row_i;
				r_ap_pending <= 1'b0;
			end
			else if (set_pre_i) begin
				r_row_valid <= 1'b0;
				r_ap_pending <= 1'b0;
			end
			else if (w_ap_fire) begin
				r_row_valid <= 1'b0;
				r_ap_pending <= 1'b0;
			end
			else if (set_rd_i || set_wr_i)
				r_ap_pending <= set_ap_i;
		end
	assign safe_act_o = (!r_row_valid && (r_rp == {TW {1'sb0}})) && (r_rc == {TW {1'sb0}});
	assign safe_rd_o = (r_row_valid && (r_rcd == {TW {1'sb0}})) && !r_ap_pending;
	assign safe_wr_o = safe_rd_o;
	assign safe_pre_o = ((r_row_valid && (r_ras == {TW {1'sb0}})) && (r_preblk == {TW {1'sb0}})) && !r_ap_pending;
	function automatic signed [TW - 1:0] sv2v_cast_C1BC4_signed;
		input reg signed [TW - 1:0] inp;
		sv2v_cast_C1BC4_signed = inp;
	endfunction
	assign safe_act_la_o = (!r_row_valid && (r_rp <= sv2v_cast_C1BC4_signed(LA))) && (r_rc <= sv2v_cast_C1BC4_signed(LA));
	assign safe_rdwr_la_o = (r_row_valid && (r_rcd <= sv2v_cast_C1BC4_signed(LA))) && !r_ap_pending;
	assign safe_pre_la_o = ((r_row_valid && (r_ras <= sv2v_cast_C1BC4_signed(LA))) && (r_preblk <= sv2v_cast_C1BC4_signed(LA))) && !r_ap_pending;
	assign row_valid_o = r_row_valid;
	assign open_row_o = r_open_row;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r_row_valid)
			state_o = (r_rcd != {TW {1'sb0}} ? 3'h1 : 3'h2);
		else
			state_o = (r_rp != {TW {1'sb0}} ? 3'h5 : 3'h0);
	end
	assign obs_rcd_nz_o = r_rcd != {TW {1'sb0}};
	assign obs_preblk_nz_o = r_preblk != {TW {1'sb0}};
	assign obs_ras_nz_o = r_ras != {TW {1'sb0}};
	assign obs_ap_pending_o = r_ap_pending;
	initial _sv2v_0 = 0;
endmodule
