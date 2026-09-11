module gaxi_skid_buffer_dbldrn (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	count,
	rd_valid,
	rd_ready,
	rd_ready2,
	rd_count,
	rd_data,
	rd_data2
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DEPTH = 4;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] BUF_WIDTH = DATA_WIDTH * DEPTH;
	parameter signed [31:0] BW = BUF_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output reg wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire [3:0] count;
	output reg rd_valid;
	input wire rd_ready;
	input wire rd_ready2;
	output wire [3:0] rd_count;
	output wire [DW - 1:0] rd_data;
	output wire [DW - 1:0] rd_data2;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/claude-1000/defork_gaxi_skid_buffer_dbldrn/gaxi_skid_buffer_dbldrn.sv:54:13 - gaxi_skid_buffer_dbldrn.gen_depth_guard\n msg: ", "gaxi_skid_buffer_dbldrn: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	reg [BW - 1:0] r_data;
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	wire w_rd_dbl_xfer;
	wire [DW - 1:0] zeros;
	assign zeros = 'b0;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = (rd_valid & rd_ready) & ~rd_ready2;
	assign w_rd_dbl_xfer = ((rd_valid & rd_ready) & rd_ready2) & (r_data_count >= 4'd2);
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_data <= 'b0;
			r_data_count <= 'b0;
		end
		else
			case ({w_wr_xfer, w_rd_dbl_xfer, w_rd_xfer})
				3'b100: begin
					r_data[DW * r_data_count+:DW] <= wr_data;
					r_data_count <= r_data_count + 1;
				end
				3'b001: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data_count <= r_data_count - 1;
				end
				3'b010: begin
					r_data <= {{2 {zeros}}, r_data[BUF_WIDTH - 1:2 * DW]};
					r_data_count <= r_data_count - 2;
				end
				3'b101: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data[DW * (sv2v_cast_32(r_data_count) - 1)+:DW] <= wr_data;
				end
				3'b110: begin
					r_data <= {{2 {zeros}}, r_data[BUF_WIDTH - 1:2 * DW]};
					r_data[DW * (sv2v_cast_32(r_data_count) - 2)+:DW] <= wr_data;
					r_data_count <= r_data_count - 1;
				end
				default:
					;
			endcase
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && ((~w_wr_xfer || w_rd_xfer) || w_rd_dbl_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && (w_rd_xfer || w_rd_dbl_xfer));
			rd_valid <= (((r_data_count >= 4'd3) || ((r_data_count == 4'd2) && (~w_rd_dbl_xfer || w_wr_xfer))) || ((r_data_count == 4'd1) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'd0) && w_wr_xfer);
		end
	assign rd_data = r_data[DW - 1:0];
	assign rd_data2 = r_data[(2 * DW) - 1:DW];
	assign rd_count = r_data_count;
	assign count = r_data_count;
	always @(posedge axi_aclk)
		if (((axi_aresetn && rd_ready) && rd_ready2) && (r_data_count < 2))
			$display("Error [%0t] /tmp/claude-1000/defork_gaxi_skid_buffer_dbldrn/gaxi_skid_buffer_dbldrn.sv:146:13 - gaxi_skid_buffer_dbldrn.<unnamed_block>.<unnamed_block>\n msg: ", $time, "ERROR: rd_ready2 asserted when rd_count < 2 (rd_count=%0d)", r_data_count);
endmodule
