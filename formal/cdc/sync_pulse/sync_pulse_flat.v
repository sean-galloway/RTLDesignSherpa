module sync_pulse (
	i_src_clk,
	i_src_rst_n,
	i_pulse,
	i_dst_clk,
	i_dst_rst_n,
	o_pulse
);
	parameter signed [31:0] SYNC_STAGES = 3;
	input wire i_src_clk;
	input wire i_src_rst_n;
	input wire i_pulse;
	input wire i_dst_clk;
	input wire i_dst_rst_n;
	output wire o_pulse;
	initial if ((SYNC_STAGES < 2) || (SYNC_STAGES > 4))
		$display("Error [%0t] /tmp/claude-1000/defork_sync_pulse/sync_pulse.sv:153:13 - sync_pulse.<unnamed_block>.<unnamed_block>\n msg: ", $time, "sync_pulse: SYNC_STAGES=%0d out of range [2,4]", SYNC_STAGES);
	(* ASYNC_REG = "TRUE" *) reg r_src_toggle;
	always @(posedge i_src_clk or negedge i_src_rst_n)
		if (!i_src_rst_n)
			r_src_toggle <= 1'b0;
		else if (i_pulse)
			r_src_toggle <= ~r_src_toggle;
	(* ASYNC_REG = "TRUE" *) reg [SYNC_STAGES - 1:0] r_sync;
	always @(posedge i_dst_clk or negedge i_dst_rst_n)
		if (!i_dst_rst_n)
			r_sync <= 1'sb0;
		else
			r_sync <= {r_sync[SYNC_STAGES - 2:0], r_src_toggle};
	reg r_sync_prev;
	always @(posedge i_dst_clk or negedge i_dst_rst_n)
		if (!i_dst_rst_n)
			r_sync_prev <= 1'b0;
		else
			r_sync_prev <= r_sync[SYNC_STAGES - 1];
	assign o_pulse = r_sync[SYNC_STAGES - 1] ^ r_sync_prev;
endmodule
