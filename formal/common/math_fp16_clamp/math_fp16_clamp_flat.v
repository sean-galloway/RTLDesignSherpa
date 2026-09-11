module math_fp16_clamp (
	i_x,
	i_min,
	i_max,
	ow_result
);
	input wire [15:0] i_x;
	input wire [15:0] i_min;
	input wire [15:0] i_max;
	output wire [15:0] ow_result;
	wire w_sign_x = i_x[15];
	wire [4:0] w_exp_x = i_x[14:10];
	wire [9:0] w_mant_x = i_x[9:0];
	wire w_sign_min = i_min[15];
	wire [4:0] w_exp_min = i_min[14:10];
	wire [9:0] w_mant_min = i_min[9:0];
	wire w_sign_max = i_max[15];
	wire [4:0] w_exp_max = i_max[14:10];
	wire [9:0] w_mant_max = i_max[9:0];
	wire w_x_is_nan = (w_exp_x == 5'h1f) & (w_mant_x != 10'h000);
	wire w_min_is_nan = (w_exp_min == 5'h1f) & (w_mant_min != 10'h000);
	wire w_max_is_nan = (w_exp_max == 5'h1f) & (w_mant_max != 10'h000);
	wire w_any_nan = (w_x_is_nan | w_min_is_nan) | w_max_is_nan;
	wire [14:0] w_mag_x = i_x[14:0];
	wire [14:0] w_mag_min = i_min[14:0];
	wire [14:0] w_mag_max = i_max[14:0];
	function automatic fp_less_than;
		input reg [15:0] a;
		input reg [15:0] b;
		reg a_sign;
		reg b_sign;
		reg [14:0] a_mag;
		reg [14:0] b_mag;
		begin
			a_sign = a[15];
			b_sign = b[15];
			a_mag = a[14:0];
			b_mag = b[14:0];
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
