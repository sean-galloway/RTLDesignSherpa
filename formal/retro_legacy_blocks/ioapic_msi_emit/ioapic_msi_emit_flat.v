module ioapic_msi_emit (
	deliv_valid,
	deliv_vector,
	deliv_dest,
	deliv_dest_mode,
	deliv_deliv_mode,
	deliv_ready,
	deliv_retry,
	msi_addr_base,
	msi_data_template,
	cmd_valid,
	cmd_ready,
	cmd_data,
	rsp_valid,
	rsp_ready,
	rsp_data
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] CPW = ((ADDR_WIDTH + DATA_WIDTH) + STRB_WIDTH) + 6;
	parameter signed [31:0] RPW = DATA_WIDTH + 3;
	input wire deliv_valid;
	input wire [7:0] deliv_vector;
	input wire [7:0] deliv_dest;
	input wire deliv_dest_mode;
	input wire [2:0] deliv_deliv_mode;
	output wire deliv_ready;
	output wire deliv_retry;
	input wire [ADDR_WIDTH - 1:0] msi_addr_base;
	input wire [DATA_WIDTH - 1:0] msi_data_template;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire [CPW - 1:0] cmd_data;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [RPW - 1:0] rsp_data;
	reg [ADDR_WIDTH - 1:0] w_msi_addr;
	reg [DATA_WIDTH - 1:0] w_msi_data;
	always @(*) begin
		if (_sv2v_0)
			;
		w_msi_addr = msi_addr_base;
		w_msi_addr[19:12] = deliv_dest;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_msi_data = msi_data_template;
		w_msi_data[7:0] = deliv_vector;
		w_msi_data[10:8] = deliv_deliv_mode;
		w_msi_data[11] = deliv_dest_mode;
	end
	localparam [2:0] MSI_PPROT = 3'b010;
	assign cmd_data = {3'b111, MSI_PPROT, {STRB_WIDTH {1'b1}}, w_msi_addr, w_msi_data};
	assign cmd_valid = deliv_valid;
	assign deliv_ready = cmd_ready;
	wire w_rsp_pslverr;
	assign w_rsp_pslverr = rsp_data[DATA_WIDTH];
	assign rsp_ready = 1'b1;
	assign deliv_retry = rsp_valid && w_rsp_pslverr;
	initial begin : param_check
		if (DATA_WIDTH < 12)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_msi_emit.sv:180:13 - ioapic_msi_emit.param_check.<unnamed_block>\n msg: ", $time, "ioapic_msi_emit: DATA_WIDTH must be >= 12 to carry vector, delivery mode and destination mode (got %0d)", DATA_WIDTH);
		if (ADDR_WIDTH < 20)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_msi_emit.sv:182:13 - ioapic_msi_emit.param_check.<unnamed_block>\n msg: ", $time, "ioapic_msi_emit: ADDR_WIDTH must be >= 20 to carry the destination at [19:12] (got %0d)", ADDR_WIDTH);
	end
	initial _sv2v_0 = 0;
endmodule
