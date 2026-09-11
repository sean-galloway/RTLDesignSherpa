module glitch_free_n_dff_arn (
	clk,
	rst_n,
	d,
	q
);
	parameter signed [31:0] FLOP_COUNT = 3;
	parameter signed [31:0] WIDTH = 4;
	input wire clk;
	input wire rst_n;
	input wire [WIDTH - 1:0] d;
	output reg [WIDTH - 1:0] q;
	localparam signed [31:0] FC = FLOP_COUNT;
	localparam signed [31:0] DW = WIDTH;
	reg [(FC * WIDTH) - 1:0] r_q_array;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_q_array <= {FC {{DW {1'b0}}}};
		else begin
			r_q_array[0+:WIDTH] <= d;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 1; i < FC; i = i + 1)
					r_q_array[i * WIDTH+:WIDTH] <= r_q_array[(i - 1) * WIDTH+:WIDTH];
			end
		end
	wire [WIDTH:1] sv2v_tmp_60F54;
	assign sv2v_tmp_60F54 = r_q_array[(FC - 1) * WIDTH+:WIDTH];
	always @(*) q = sv2v_tmp_60F54;
	wire [(DW * FC) - 1:0] flat_r_q;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < FC; _gv_i_1 = _gv_i_1 + 1) begin : gen_flatten_memory
			localparam i = _gv_i_1;
			assign flat_r_q[i * DW+:DW] = r_q_array[i * WIDTH+:WIDTH];
		end
	endgenerate
endmodule
module cdc_synchronizer (
	clk,
	rst_n,
	async_in,
	sync_out
);
	parameter signed [31:0] WIDTH = 1;
	parameter signed [31:0] FLOP_COUNT = 3;
	input wire clk;
	input wire rst_n;
	input wire [WIDTH - 1:0] async_in;
	output wire [WIDTH - 1:0] sync_out;
	glitch_free_n_dff_arn #(
		.FLOP_COUNT(FLOP_COUNT),
		.WIDTH(WIDTH)
	) u_sync(
		.clk(clk),
		.rst_n(rst_n),
		.d(async_in),
		.q(sync_out)
	);
endmodule
