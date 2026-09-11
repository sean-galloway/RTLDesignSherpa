module math_fp16_min_tree_8 (
	i_data,
	ow_min,
	ow_min_idx
);
	input wire [127:0] i_data;
	output wire [15:0] ow_min;
	output wire [7:0] ow_min_idx;
	function automatic [15:0] fp_min;
		input reg [15:0] a;
		input reg [15:0] b;
		reg a_sign;
		reg b_sign;
		reg [14:0] a_mag;
		reg [14:0] b_mag;
		reg a_is_nan;
		reg b_is_nan;
		reg a_less;
		reg [0:1] _sv2v_jump;
		begin
			_sv2v_jump = 2'b00;
			a_sign = a[15];
			b_sign = b[15];
			a_mag = a[14:0];
			b_mag = b[14:0];
			a_is_nan = (a[14:10] == 5'h1f) & (a[9:0] != 10'h000);
			b_is_nan = (b[14:10] == 5'h1f) & (b[9:0] != 10'h000);
			if (a_is_nan) begin
				fp_min = b;
				_sv2v_jump = 2'b11;
			end
			if (_sv2v_jump == 2'b00) begin
				if (b_is_nan) begin
					fp_min = a;
					_sv2v_jump = 2'b11;
				end
				if (_sv2v_jump == 2'b00) begin
					if (a_sign != b_sign)
						a_less = a_sign;
					else if (a_sign == 1'b0)
						a_less = a_mag <= b_mag;
					else
						a_less = a_mag >= b_mag;
					fp_min = (a_less ? a : b);
					_sv2v_jump = 2'b11;
				end
			end
		end
	endfunction
	wire [15:0] w_level0 [0:3];
	assign w_level0[0] = fp_min(i_data[112+:16], i_data[96+:16]);
	assign w_level0[1] = fp_min(i_data[80+:16], i_data[64+:16]);
	assign w_level0[2] = fp_min(i_data[48+:16], i_data[32+:16]);
	assign w_level0[3] = fp_min(i_data[16+:16], i_data[0+:16]);
	wire [15:0] w_level1 [0:1];
	assign w_level1[0] = fp_min(w_level0[0], w_level0[1]);
	assign w_level1[1] = fp_min(w_level0[2], w_level0[3]);
	wire [15:0] w_level2 [0:0];
	assign w_level2[0] = fp_min(w_level1[0], w_level1[1]);
	assign ow_min = w_level2[0];
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < 8; _gv_gi_1 = _gv_gi_1 + 1) begin : gen_idx
			localparam gi = _gv_gi_1;
			assign ow_min_idx[gi] = i_data[(7 - gi) * 16+:16] == ow_min;
		end
	endgenerate
endmodule
