module math_fp8_e5m2_softmax_8 (
	i_clk,
	i_rst_n,
	i_valid,
	i_data,
	ow_valid,
	ow_result
);
	input wire i_clk;
	input wire i_rst_n;
	input wire i_valid;
	input wire [63:0] i_data;
	output wire ow_valid;
	output wire [63:0] ow_result;
	reg r_valid_d1;
	reg r_valid_d2;
	reg r_valid_d3;
	reg [7:0] r_data_d1 [0:7];
	reg [7:0] r_max;
	function automatic [7:0] fp_max;
		input reg [7:0] a;
		input reg [7:0] b;
		reg a_sign;
		reg b_sign;
		reg [4:0] a_exp;
		reg [4:0] b_exp;
		reg [1:0] a_mant;
		reg [1:0] b_mant;
		reg a_greater;
		begin
			a_sign = a[7];
			b_sign = b[7];
			a_exp = a[6:2];
			b_exp = b[6:2];
			a_mant = a[1:0];
			b_mant = b[1:0];
			if (a_sign != b_sign)
				a_greater = b_sign;
			else if (a_sign == 1'b0)
				a_greater = (a_exp > b_exp) | ((a_exp == b_exp) & (a_mant > b_mant));
			else
				a_greater = (a_exp < b_exp) | ((a_exp == b_exp) & (a_mant < b_mant));
			fp_max = (a_greater ? a : b);
		end
	endfunction
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_valid_d1 <= 1'b0;
			r_max <= 8'h00;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_data_d1[i] <= 8'h00;
			end
		end
		else begin
			r_valid_d1 <= i_valid;
			if (i_valid) begin
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < 8; i = i + 1)
						r_data_d1[i] <= i_data[(7 - i) * 8+:8];
				end
				r_max <= fp_max(fp_max(fp_max(i_data[56+:8], i_data[48+:8]), fp_max(i_data[40+:8], i_data[32+:8])), fp_max(fp_max(i_data[24+:8], i_data[16+:8]), fp_max(i_data[8+:8], i_data[0+:8])));
			end
		end
	reg [7:0] r_exp_approx [0:7];
	wire r_valid_d2_reg;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_valid_d2 <= 1'b0;
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_exp_approx[i] <= 8'h00;
			end
		end
		else begin
			r_valid_d2 <= r_valid_d1;
			if (r_valid_d1) begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					if (r_data_d1[i] == r_max)
						r_exp_approx[i] <= 8'h3c;
					else
						r_exp_approx[i] <= 8'h30;
			end
		end
	reg [63:0] r_result;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_valid_d3 <= 1'b0;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_result[(7 - i) * 8+:8] <= 8'h00;
			end
		end
		else begin
			r_valid_d3 <= r_valid_d2;
			if (r_valid_d2) begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					if (r_exp_approx[i][6:2] > 5'd3)
						r_result[(7 - i) * 8+:8] <= {r_exp_approx[i][7], r_exp_approx[i][6:2] - 5'd3, r_exp_approx[i][1:0]};
					else
						r_result[(7 - i) * 8+:8] <= 8'h00;
			end
		end
	assign ow_valid = r_valid_d3;
	assign ow_result = r_result;
endmodule
