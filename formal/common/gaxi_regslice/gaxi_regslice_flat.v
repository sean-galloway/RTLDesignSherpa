module gaxi_regslice (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_valid,
	rd_ready,
	rd_data,
	count,
	rd_count
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire rd_valid;
	input wire rd_ready;
	output wire [DW - 1:0] rd_data;
	output wire [3:0] count;
	output wire [3:0] rd_count;
	reg r_valid;
	reg [DW - 1:0] r_data;
	wire w_wxfer = wr_valid & wr_ready;
	wire w_rxfer = rd_valid & rd_ready;
	assign wr_ready = !r_valid || (r_valid && rd_ready);
	assign rd_valid = r_valid;
	assign rd_data = r_data;
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_valid <= 1'b0;
			r_data <= 1'sb0;
		end
		else
			(* full_case, parallel_case *)
			case ({w_wxfer, w_rxfer})
				2'b10: begin
					r_valid <= 1'b1;
					r_data <= wr_data;
				end
				2'b01: r_valid <= 1'b0;
				2'b11: begin
					r_valid <= 1'b1;
					r_data <= wr_data;
				end
				default: begin
					r_valid <= r_valid;
					r_data <= r_data;
				end
			endcase
	assign count = (r_valid ? 4'd1 : 4'd0);
	assign rd_count = count;
	always @(posedge axi_aclk)
		if (axi_aresetn) begin
			if (count > 4'd1)
				$display("Error [%0t] /tmp/claude-1000/defork_gaxi_regslice/gaxi_regslice.sv:112:13 - gaxi_regslice.<unnamed_block>.<unnamed_block>\n msg: ", $time, "[%m] count > 1 (=%0d) @ %0t", count, $time);
		end
endmodule
