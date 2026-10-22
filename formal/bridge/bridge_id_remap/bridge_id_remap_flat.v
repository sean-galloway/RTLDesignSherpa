module bridge_id_remap (
	aclk,
	aresetn,
	req_id,
	req_tgt,
	req_meta,
	req_push,
	req_slot,
	req_ok,
	full,
	rsp_slot,
	rsp_pop,
	rsp_id,
	rsp_meta,
	out_cnt
);
	reg _sv2v_0;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] NUM_TGT = 4;
	parameter signed [31:0] META_WIDTH = 1;
	localparam signed [31:0] SW = $clog2(DEPTH);
	input wire aclk;
	input wire aresetn;
	input wire [ID_WIDTH - 1:0] req_id;
	input wire [NUM_TGT - 1:0] req_tgt;
	input wire [META_WIDTH - 1:0] req_meta;
	input wire req_push;
	output wire [SW - 1:0] req_slot;
	output wire req_ok;
	output reg full;
	input wire [SW - 1:0] rsp_slot;
	input wire rsp_pop;
	output wire [ID_WIDTH - 1:0] rsp_id;
	output wire [META_WIDTH - 1:0] rsp_meta;
	output wire [SW:0] out_cnt;
	reg [ID_WIDTH - 1:0] r_id [0:DEPTH - 1];
	reg [NUM_TGT - 1:0] r_tgt [0:DEPTH - 1];
	reg [META_WIDTH - 1:0] r_meta [0:DEPTH - 1];
	reg [SW:0] r_cnt [0:DEPTH - 1];
	reg [DEPTH - 1:0] r_live;
	reg [DEPTH - 1:0] w_hit;
	reg [DEPTH - 1:0] w_bad;
	reg w_any_hit;
	reg [SW - 1:0] w_hit_slot;
	reg [SW - 1:0] w_free_slot;
	reg [DEPTH - 1:0] w_free_oh;
	function automatic signed [SW - 1:0] sv2v_cast_6C2E3_signed;
		input reg signed [SW - 1:0] inp;
		sv2v_cast_6C2E3_signed = inp;
	endfunction
	function automatic signed [DEPTH - 1:0] sv2v_cast_758CD_signed;
		input reg signed [DEPTH - 1:0] inp;
		sv2v_cast_758CD_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_hit_slot = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				begin
					w_hit[i] = r_live[i] && (r_id[i] == req_id);
					w_bad[i] = w_hit[i] && (!(|(r_tgt[i] & req_tgt)) || (r_meta[i] != req_meta));
					if (w_hit[i])
						w_hit_slot = w_hit_slot | sv2v_cast_6C2E3_signed(i);
				end
		end
		w_any_hit = |w_hit;
		w_free_slot = 1'sb0;
		w_free_oh = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = DEPTH - 1; i >= 0; i = i - 1)
				if (!r_live[i]) begin
					w_free_slot = sv2v_cast_6C2E3_signed(i);
					w_free_oh = sv2v_cast_758CD_signed(1) << i;
				end
		end
	end
	assign req_slot = (w_any_hit ? w_hit_slot : w_free_slot);
	assign req_ok = !(|w_bad);
	assign rsp_id = r_id[rsp_slot];
	assign rsp_meta = r_meta[rsp_slot];
	reg [SW:0] r_out_cnt;
	reg r_pop;
	reg [SW - 1:0] r_pop_slot;
	wire [1:0] w_net;
	reg [DEPTH - 1:0] w_inc;
	reg [DEPTH - 1:0] w_dec;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				begin
					w_inc[i] = req_push && (w_any_hit ? w_hit[i] : w_free_oh[i]);
					w_dec[i] = r_pop && (r_pop_slot == sv2v_cast_6C2E3_signed(i));
				end
		end
	end
	assign w_net = {req_push, r_pop};
	assign out_cnt = r_out_cnt;
	function automatic [((SW + 0) >= 0 ? SW + 1 : 1 - (SW + 0)) - 1:0] sv2v_cast_1DCD7;
		input reg [((SW + 0) >= 0 ? SW + 1 : 1 - (SW + 0)) - 1:0] inp;
		sv2v_cast_1DCD7 = inp;
	endfunction
	function automatic signed [((SW + 0) >= 0 ? SW + 1 : 1 - (SW + 0)) - 1:0] sv2v_cast_1DCD7_signed;
		input reg signed [((SW + 0) >= 0 ? SW + 1 : 1 - (SW + 0)) - 1:0] inp;
		sv2v_cast_1DCD7_signed = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					r_cnt[i] <= 1'sb0;
			end
			r_live <= 1'sb0;
			r_out_cnt <= 1'sb0;
			full <= 1'b0;
			r_pop <= 1'b0;
			r_pop_slot <= 1'sb0;
		end
		else begin
			r_pop <= rsp_pop;
			r_pop_slot <= rsp_slot;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					begin
						r_cnt[i] <= (r_cnt[i] + sv2v_cast_1DCD7(w_inc[i])) - sv2v_cast_1DCD7(w_dec[i]);
						r_live[i] <= (w_inc[i] || (r_cnt[i] > sv2v_cast_1DCD7_signed(1))) || ((r_cnt[i] == sv2v_cast_1DCD7_signed(1)) && !w_dec[i]);
					end
			end
			case (w_net)
				2'b10: r_out_cnt <= r_out_cnt + 1'b1;
				2'b01: r_out_cnt <= r_out_cnt - 1'b1;
				default: r_out_cnt <= r_out_cnt;
			endcase
			full <= ((r_out_cnt == sv2v_cast_1DCD7_signed(DEPTH)) && (w_net != 2'b01)) || ((r_out_cnt == sv2v_cast_1DCD7_signed(DEPTH - 1)) && (w_net == 2'b10));
		end
	always @(posedge aclk) begin : sv2v_autoblock_6
		reg signed [31:0] i;
		for (i = 0; i < DEPTH; i = i + 1)
			if (w_free_oh[i]) begin
				r_id[i] <= req_id;
				r_tgt[i] <= req_tgt;
				r_meta[i] <= req_meta;
			end
	end
	initial _sv2v_0 = 0;
endmodule
