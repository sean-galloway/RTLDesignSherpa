module math_fp8_e5m2_clamp (
	i_x,
	i_min,
	i_max,
	ow_result
);
	input wire [7:0] i_x;
	input wire [7:0] i_min;
	input wire [7:0] i_max;
	output wire [7:0] ow_result;
	wire w_sign_x = i_x[7];
	wire [4:0] w_exp_x = i_x[6:2];
	wire [1:0] w_mant_x = i_x[1:0];
	wire w_sign_min = i_min[7];
	wire [4:0] w_exp_min = i_min[6:2];
	wire [1:0] w_mant_min = i_min[1:0];
	wire w_sign_max = i_max[7];
	wire [4:0] w_exp_max = i_max[6:2];
	wire [1:0] w_mant_max = i_max[1:0];
	wire w_x_is_nan = (w_exp_x == 5'h1f) & (w_mant_x != 2'h0);
	wire w_min_is_nan = (w_exp_min == 5'h1f) & (w_mant_min != 2'h0);
	wire w_max_is_nan = (w_exp_max == 5'h1f) & (w_mant_max != 2'h0);
	wire w_any_nan = (w_x_is_nan | w_min_is_nan) | w_max_is_nan;
	wire [6:0] w_mag_x = i_x[6:0];
	wire [6:0] w_mag_min = i_min[6:0];
	wire [6:0] w_mag_max = i_max[6:0];
	function automatic fp_less_than;
		input reg [7:0] a;
		input reg [7:0] b;
		reg a_sign;
		reg b_sign;
		reg [6:0] a_mag;
		reg [6:0] b_mag;
		begin
			a_sign = a[7];
			b_sign = b[7];
			a_mag = a[6:0];
			b_mag = b[6:0];
			if (a_sign != b_sign)
				fp_less_than = a_sign;
			else if (a_sign == 1'b0)
				fp_less_than = a_mag < b_mag;
			else
				fp_less_than = a_mag > b_mag;
		end
	endfunction
	wire w_x_lt_min = fp_less_than(i_x, i_min);
	wire w_x_gt_max = fp_less_than(i_max, i_x);
	assign ow_result = (w_any_nan ? i_x : (w_x_lt_min ? i_min : (w_x_gt_max ? i_max : i_x)));
endmodule
