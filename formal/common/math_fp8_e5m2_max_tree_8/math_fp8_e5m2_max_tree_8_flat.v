module math_fp8_e5m2_max_tree_8 (
	i_data,
	ow_max,
	ow_max_idx
);
	input wire [63:0] i_data;
	output wire [7:0] ow_max;
	output wire [7:0] ow_max_idx;
	function automatic [7:0] fp_max;
		input reg [7:0] a;
		input reg [7:0] b;
		reg a_sign;
		reg b_sign;
		reg [6:0] a_mag;
		reg [6:0] b_mag;
		reg a_is_nan;
		reg b_is_nan;
		reg a_greater;
		reg [0:1] _sv2v_jump;
		begin
			_sv2v_jump = 2'b00;
			a_sign = a[7];
			b_sign = b[7];
			a_mag = a[6:0];
			b_mag = b[6:0];
			a_is_nan = (a[6:2] == 5'h1f) & (a[1:0] != 2'h0);
			b_is_nan = (b[6:2] == 5'h1f) & (b[1:0] != 2'h0);
			if (a_is_nan) begin
				fp_max = b;
				_sv2v_jump = 2'b11;
			end
			if (_sv2v_jump == 2'b00) begin
				if (b_is_nan) begin
					fp_max = a;
					_sv2v_jump = 2'b11;
				end
				if (_sv2v_jump == 2'b00) begin
					if (a_sign != b_sign)
						a_greater = ~a_sign;
					else if (a_sign == 1'b0)
						a_greater = a_mag >= b_mag;
					else
						a_greater = a_mag <= b_mag;
					fp_max = (a_greater ? a : b);
					_sv2v_jump = 2'b11;
				end
			end
		end
	endfunction
	function automatic fp_gt;
		input reg [7:0] a;
		input reg [7:0] b;
		reg a_sign;
		reg b_sign;
		reg [6:0] a_mag;
		reg [6:0] b_mag;
		reg a_is_nan;
		reg b_is_nan;
		reg [0:1] _sv2v_jump;
		begin
			_sv2v_jump = 2'b00;
			a_sign = a[7];
			b_sign = b[7];
			a_mag = a[6:0];
			b_mag = b[6:0];
			a_is_nan = (a[6:2] == 5'h1f) & (a[1:0] != 2'h0);
			b_is_nan = (b[6:2] == 5'h1f) & (b[1:0] != 2'h0);
			if (a_is_nan | b_is_nan) begin
				fp_gt = 1'b0;
				_sv2v_jump = 2'b11;
			end
			if (_sv2v_jump == 2'b00) begin
				if (a_sign != b_sign) begin
					fp_gt = ~a_sign;
					_sv2v_jump = 2'b11;
				end
				else if (a_sign == 1'b0) begin
					fp_gt = a_mag > b_mag;
					_sv2v_jump = 2'b11;
				end
				else begin
					fp_gt = a_mag < b_mag;
					_sv2v_jump = 2'b11;
				end
			end
		end
	endfunction
	wire [7:0] w_level0 [0:3];
	assign w_level0[0] = fp_max(i_data[56+:8], i_data[48+:8]);
	assign w_level0[1] = fp_max(i_data[40+:8], i_data[32+:8]);
	assign w_level0[2] = fp_max(i_data[24+:8], i_data[16+:8]);
	assign w_level0[3] = fp_max(i_data[8+:8], i_data[0+:8]);
	wire [7:0] w_level1 [0:1];
	assign w_level1[0] = fp_max(w_level0[0], w_level0[1]);
	assign w_level1[1] = fp_max(w_level0[2], w_level0[3]);
	wire [7:0] w_level2 [0:0];
	assign w_level2[0] = fp_max(w_level1[0], w_level1[1]);
	assign ow_max = w_level2[0];
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < 8; _gv_gi_1 = _gv_gi_1 + 1) begin : gen_idx
			localparam gi = _gv_gi_1;
			assign ow_max_idx[gi] = i_data[(7 - gi) * 8+:8] == ow_max;
		end
	endgenerate
endmodule
