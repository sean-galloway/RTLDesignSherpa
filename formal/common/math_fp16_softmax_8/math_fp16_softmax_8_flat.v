module math_fp16_softmax_8 (
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
	input wire [127:0] i_data;
	output wire ow_valid;
	output wire [127:0] ow_result;
	reg r_valid_d1;
	reg r_valid_d2;
	reg r_valid_d3;
	reg [15:0] r_data_d1 [0:7];
	reg [15:0] r_max;
	function automatic [15:0] fp_max;
		input reg [15:0] a;
		input reg [15:0] b;
		reg a_sign;
		reg b_sign;
		reg [4:0] a_exp;
		reg [4:0] b_exp;
		reg [9:0] a_mant;
		reg [9:0] b_mant;
		reg a_greater;
		begin
			a_sign = a[15];
			b_sign = b[15];
			a_exp = a[14:10];
			b_exp = b[14:10];
			a_mant = a[9:0];
			b_mant = b[9:0];
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
			r_max <= 16'h0000;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_data_d1[i] <= 16'h0000;
			end
		end
		else begin
			r_valid_d1 <= i_valid;
			if (i_valid) begin
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < 8; i = i + 1)
						r_data_d1[i] <= i_data[(7 - i) * 16+:16];
				end
				r_max <= fp_max(fp_max(fp_max(i_data[112+:16], i_data[96+:16]), fp_max(i_data[80+:16], i_data[64+:16])), fp_max(fp_max(i_data[48+:16], i_data[32+:16]), fp_max(i_data[16+:16], i_data[0+:16])));
			end
		end
	reg [15:0] r_exp_approx [0:7];
	wire r_valid_d2_reg;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_valid_d2 <= 1'b0;
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_exp_approx[i] <= 16'h0000;
			end
		end
		else begin
			r_valid_d2 <= r_valid_d1;
			if (r_valid_d1) begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					if (r_data_d1[i] == r_max)
						r_exp_approx[i] <= 16'h3c00;
					else
						r_exp_approx[i] <= 16'h3000;
			end
		end
	reg [127:0] r_result;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_valid_d3 <= 1'b0;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					r_result[(7 - i) * 16+:16] <= 16'h0000;
			end
		end
		else begin
			r_valid_d3 <= r_valid_d2;
			if (r_valid_d2) begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < 8; i = i + 1)
					if (r_exp_approx[i][14:10] > 5'd3)
						r_result[(7 - i) * 16+:16] <= {r_exp_approx[i][15], r_exp_approx[i][14:10] - 5'd3, r_exp_approx[i][9:0]};
					else
						r_result[(7 - i) * 16+:16] <= 16'h0000;
			end
		end
	assign ow_valid = r_valid_d3;
	assign ow_result = r_result;
endmodule
