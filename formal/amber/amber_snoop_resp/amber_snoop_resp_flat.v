module gaxi_skid_buffer (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	count,
	rd_valid,
	rd_ready,
	rd_count,
	rd_data
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DEPTH = 2;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output reg wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire [3:0] count;
	output reg rd_valid;
	input wire rd_ready;
	output wire [3:0] rd_count;
	output wire [DW - 1:0] rd_data;
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/formal_amber_snoop_resp/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
			localparam gi = _gv_gi_1;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_data[gi] <= 1'sb0;
				else
					(* full_case, parallel_case *)
					case ({w_wr_xfer, w_rd_xfer})
						2'b10:
							if (r_data_count == gi[3:0])
								r_data[gi] <= wr_data;
						2'b01:
							if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						2'b11:
							if ((r_data_count >= 1) && (gi[3:0] == (r_data_count - 4'd1)))
								r_data[gi] <= wr_data;
							else if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						default:
							;
					endcase
		end
	endgenerate
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_data_count <= 1'sb0;
		else
			(* full_case, parallel_case *)
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: r_data_count <= r_data_count + 4'd1;
				2'b01: r_data_count <= r_data_count - 4'd1;
				default:
					;
			endcase
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[0];
	assign rd_count = r_data_count;
	assign count = r_data_count;
endmodule
module axi4ace_snoop_slave (
	aclk,
	aresetn,
	m_axi_acaddr,
	m_axi_acsnoop,
	m_axi_acprot,
	m_axi_acvalid,
	m_axi_acready,
	m_axi_crresp,
	m_axi_crvalid,
	m_axi_crready,
	m_axi_cddata,
	m_axi_cdlast,
	m_axi_cdvalid,
	m_axi_cdready,
	fub_acaddr,
	fub_acsnoop,
	fub_acprot,
	fub_acvalid,
	fub_acready,
	fub_crresp,
	fub_crvalid,
	fub_crready,
	fub_cddata,
	fub_cdlast,
	fub_cdvalid,
	fub_cdready,
	busy
);
	parameter signed [31:0] SKID_DEPTH_AC = 2;
	parameter signed [31:0] SKID_DEPTH_CR = 4;
	parameter signed [31:0] SKID_DEPTH_CD = 4;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] ACSize = AW + 7;
	parameter signed [31:0] CRSize = 5;
	parameter signed [31:0] CDSize = DW + 1;
	input wire aclk;
	input wire aresetn;
	input wire [AW - 1:0] m_axi_acaddr;
	input wire [3:0] m_axi_acsnoop;
	input wire [2:0] m_axi_acprot;
	input wire m_axi_acvalid;
	output wire m_axi_acready;
	output wire [4:0] m_axi_crresp;
	output wire m_axi_crvalid;
	input wire m_axi_crready;
	output wire [DW - 1:0] m_axi_cddata;
	output wire m_axi_cdlast;
	output wire m_axi_cdvalid;
	input wire m_axi_cdready;
	output wire [AW - 1:0] fub_acaddr;
	output wire [3:0] fub_acsnoop;
	output wire [2:0] fub_acprot;
	output wire fub_acvalid;
	input wire fub_acready;
	input wire [4:0] fub_crresp;
	input wire fub_crvalid;
	output wire fub_crready;
	input wire [DW - 1:0] fub_cddata;
	input wire fub_cdlast;
	input wire fub_cdvalid;
	output wire fub_cdready;
	output wire busy;
	wire [3:0] int_ac_count;
	wire [ACSize - 1:0] int_ac_pkt;
	wire int_skid_acvalid;
	wire int_skid_acready;
	wire [3:0] int_cr_count;
	wire [CRSize - 1:0] int_cr_pkt;
	wire int_skid_crvalid;
	wire int_skid_crready;
	wire [3:0] int_cd_count;
	wire [CDSize - 1:0] int_cd_pkt;
	wire int_skid_cdvalid;
	wire int_skid_cdready;
	assign busy = (((((int_ac_count > 0) || (int_cr_count > 0)) || (int_cd_count > 0)) || m_axi_acvalid) || fub_crvalid) || fub_cdvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AC),
		.DATA_WIDTH(ACSize)
	) ac_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(m_axi_acvalid),
		.wr_ready(m_axi_acready),
		.wr_data({m_axi_acaddr, m_axi_acsnoop, m_axi_acprot}),
		.rd_valid(int_skid_acvalid),
		.rd_ready(int_skid_acready),
		.rd_count(int_ac_count),
		.rd_data(int_ac_pkt),
		.count()
	);
	assign {fub_acaddr, fub_acsnoop, fub_acprot} = int_ac_pkt;
	assign fub_acvalid = int_skid_acvalid;
	assign int_skid_acready = fub_acready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_CR),
		.DATA_WIDTH(CRSize)
	) cr_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_crvalid),
		.wr_ready(fub_crready),
		.wr_data({fub_crresp}),
		.rd_valid(int_skid_crvalid),
		.rd_ready(int_skid_crready),
		.rd_count(int_cr_count),
		.rd_data(int_cr_pkt),
		.count()
	);
	assign m_axi_crresp = int_cr_pkt;
	assign m_axi_crvalid = int_skid_crvalid;
	assign int_skid_crready = m_axi_crready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_CD),
		.DATA_WIDTH(CDSize)
	) cd_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_cdvalid),
		.wr_ready(fub_cdready),
		.wr_data({fub_cddata, fub_cdlast}),
		.rd_valid(int_skid_cdvalid),
		.rd_ready(int_skid_cdready),
		.rd_count(int_cd_count),
		.rd_data(int_cd_pkt),
		.count()
	);
	assign {m_axi_cddata, m_axi_cdlast} = int_cd_pkt;
	assign m_axi_cdvalid = int_skid_cdvalid;
	assign int_skid_cdready = m_axi_cdready;
endmodule
module amber_snoop_resp (
	aclk,
	aresetn,
	m_axi_acaddr,
	m_axi_acsnoop,
	m_axi_acprot,
	m_axi_acvalid,
	m_axi_acready,
	m_axi_crresp,
	m_axi_crvalid,
	m_axi_crready,
	m_axi_cddata,
	m_axi_cdlast,
	m_axi_cdvalid,
	m_axi_cdready,
	ctrl_snoop_req,
	ctrl_snoop_addr,
	ctrl_snoop_type,
	ctrl_snoop_ready,
	ctrl_crresp,
	ctrl_cddata,
	ctrl_cdlast,
	ctrl_cdvalid,
	ctrl_cdready
);
	reg _sv2v_0;
	localparam signed [31:0] amber_pkg_AMBER_ADDR_WIDTH = 32;
	localparam signed [31:0] amber_pkg_AMBER_BUS_WIDTH = 64;
	localparam signed [31:0] amber_pkg_AMBER_LINE_BYTES = 64;
	input wire aclk;
	input wire aresetn;
	input wire [32 - 1:0] m_axi_acaddr;
	input wire [3:0] m_axi_acsnoop;
	input wire [2:0] m_axi_acprot;
	input wire m_axi_acvalid;
	output wire m_axi_acready;
	output wire [4:0] m_axi_crresp;
	output wire m_axi_crvalid;
	input wire m_axi_crready;
	output wire [64 - 1:0] m_axi_cddata;
	output wire m_axi_cdlast;
	output wire m_axi_cdvalid;
	input wire m_axi_cdready;
	output wire ctrl_snoop_req;
	output wire [32 - 1:0] ctrl_snoop_addr;
	output wire [2:0] ctrl_snoop_type;
	input wire ctrl_snoop_ready;
	input wire [4:0] ctrl_crresp;
	input wire [64 - 1:0] ctrl_cddata;
	input wire ctrl_cdlast;
	input wire ctrl_cdvalid;
	output wire ctrl_cdready;
	wire [32 - 1:0] fub_acaddr;
	wire [3:0] fub_acsnoop;
	wire [2:0] fub_acprot;
	wire fub_acvalid;
	wire fub_acready;
	wire [4:0] fub_crresp;
	wire fub_crvalid;
	wire fub_crready;
	wire [64 - 1:0] fub_cddata;
	wire fub_cdlast;
	wire fub_cdvalid;
	wire fub_cdready;
	wire w_busy;
	axi4ace_snoop_slave #(
		.ADDR_WIDTH(32),
		.DATA_WIDTH(64)
	) u_transport(
		.aclk(aclk),
		.aresetn(aresetn),
		.m_axi_acaddr(m_axi_acaddr),
		.m_axi_acsnoop(m_axi_acsnoop),
		.m_axi_acprot(m_axi_acprot),
		.m_axi_acvalid(m_axi_acvalid),
		.m_axi_acready(m_axi_acready),
		.m_axi_crresp(m_axi_crresp),
		.m_axi_crvalid(m_axi_crvalid),
		.m_axi_crready(m_axi_crready),
		.m_axi_cddata(m_axi_cddata),
		.m_axi_cdlast(m_axi_cdlast),
		.m_axi_cdvalid(m_axi_cdvalid),
		.m_axi_cdready(m_axi_cdready),
		.fub_acaddr(fub_acaddr),
		.fub_acsnoop(fub_acsnoop),
		.fub_acprot(fub_acprot),
		.fub_acvalid(fub_acvalid),
		.fub_acready(fub_acready),
		.fub_crresp(fub_crresp),
		.fub_crvalid(fub_crvalid),
		.fub_crready(fub_crready),
		.fub_cddata(fub_cddata),
		.fub_cdlast(fub_cdlast),
		.fub_cdvalid(fub_cdvalid),
		.fub_cdready(fub_cdready),
		.busy(w_busy)
	);
	reg [2:0] w_snoop_type;
	always @(*) begin
		if (_sv2v_0)
			;
		case (fub_acsnoop)
			4'h0: w_snoop_type = 3'b001;
			4'h1: w_snoop_type = 3'b000;
			4'h7: w_snoop_type = 3'b010;
			4'h8: w_snoop_type = 3'b011;
			4'h9: w_snoop_type = 3'b100;
			4'hc: w_snoop_type = 3'b101;
			default: w_snoop_type = 3'b110;
		endcase
	end
	reg [1:0] r_state;
	reg [4:0] r_crresp;
	reg [32 - 1:0] r_snoop_addr;
	reg [2:0] r_snoop_type;
	assign ctrl_snoop_req = r_state == 2'd1;
	assign ctrl_snoop_addr = r_snoop_addr;
	assign ctrl_snoop_type = r_snoop_type;
	assign fub_acready = r_state == 2'd0;
	assign fub_crresp = r_crresp;
	assign fub_crvalid = r_state == 2'd3;
	assign fub_cddata = ctrl_cddata;
	assign fub_cdlast = ctrl_cdlast;
	assign fub_cdvalid = (r_state == 2'd2) && ctrl_cdvalid;
	assign ctrl_cdready = (r_state == 2'd2) && fub_cdready;
	localparam signed [31:0] amber_pkg_AMBER_CRRESP_DT = 0;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_state <= 2'd0;
			r_crresp <= 1'sb0;
			r_snoop_addr <= 1'sb0;
			r_snoop_type <= 1'sb0;
		end
		else
			(* full_case, parallel_case *)
			case (r_state)
				2'd0:
					if (fub_acvalid && fub_acready) begin
						r_snoop_addr <= fub_acaddr;
						r_snoop_type <= w_snoop_type;
						r_state <= 2'd1;
					end
				2'd1:
					if (ctrl_snoop_req && ctrl_snoop_ready) begin
						r_crresp <= ctrl_crresp;
						r_state <= (ctrl_crresp[amber_pkg_AMBER_CRRESP_DT] ? 2'd2 : 2'd3);
					end
				2'd2:
					if ((fub_cdvalid && fub_cdready) && fub_cdlast)
						r_state <= 2'd3;
				2'd3:
					if (fub_crvalid && fub_crready)
						r_state <= 2'd0;
				default: r_state <= 2'd0;
			endcase
	initial _sv2v_0 = 0;
endmodule
