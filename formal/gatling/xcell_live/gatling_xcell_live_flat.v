module reset_sync (
	clk,
	rst_n,
	sync_rst_n
);
	reg _sv2v_0;
	parameter signed [31:0] N = 3;
	parameter [0:0] KEEP_ATTRS = 1'b1;
	parameter [0:0] IN_ACTIVE_LOW = 1'b1;
	parameter [0:0] OUT_ACTIVE_LOW = 1'b1;
	parameter [0:0] ASYNC_ASSERT = 1'b1;
	parameter [0:0] REPLICATED_OUT = 1'b0;
	input wire clk;
	input wire rst_n;
	output reg sync_rst_n;
	generate
		if (N < 2) begin : g_illegal
			initial $display("Error [%0t] /tmp/rds-canonical-repo-root/rtl/cdc/reset_sync.sv:261:17 - reset_sync.g_illegal.<unnamed_block>\n msg: ", $time, "reset_sync: N must be >= 2 (got %0d)", N);
		end
	endgenerate
	wire rst_in_h = (IN_ACTIVE_LOW ? ~rst_n : rst_n);
	wire w_sync_rst_h;
	generate
		if (ASYNC_ASSERT) begin : g_async_assert
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				assign w_sync_rst_h = r_sync_reg[N - 1];
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				assign w_sync_rst_h = r_sync_reg[N - 1];
			end
		end
		else begin : g_sync_only
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				assign w_sync_rst_h = r_sync_reg[N - 1];
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				assign w_sync_rst_h = r_sync_reg[N - 1];
			end
		end
		if (REPLICATED_OUT) begin : g_rep_out
			localparam [0:0] OUT_ASSERTED = (OUT_ACTIVE_LOW ? 1'b0 : 1'b1);
			wire w_out_next = (OUT_ACTIVE_LOW ? ~w_sync_rst_h : w_sync_rst_h);
			(* max_fanout = 512 *) reg r_out = OUT_ASSERTED;
			if (ASYNC_ASSERT) begin : g_async
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_out <= OUT_ASSERTED;
					else
						r_out <= w_out_next;
			end
			else begin : g_sync
				always @(posedge clk)
					if (rst_in_h)
						r_out <= OUT_ASSERTED;
					else
						r_out <= w_out_next;
			end
			wire [1:1] sv2v_tmp_AFEC5;
			assign sv2v_tmp_AFEC5 = r_out;
			always @(*) sync_rst_n = sv2v_tmp_AFEC5;
		end
		else begin : g_comb_out
			always @(*) begin
				if (_sv2v_0)
					;
				sync_rst_n = (OUT_ACTIVE_LOW ? ~w_sync_rst_h : w_sync_rst_h);
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module rv32i_alu (
	op,
	a,
	b,
	y,
	eq,
	lt,
	ltu
);
	reg _sv2v_0;
	input wire [3:0] op;
	input wire [31:0] a;
	input wire [31:0] b;
	output wire [31:0] y;
	output wire eq;
	output wire lt;
	output wire ltu;
	localparam signed [31:0] SHAMT_WIDTH = 5;
	localparam signed [31:0] PAD_WIDTH = 31;
	wire [4:0] shamt;
	assign shamt = b[4:0];
	assign eq = a == b;
	assign lt = $signed(a) < $signed(b);
	assign ltu = a < b;
	wire is_slt;
	wire is_sub;
	wire slt_signed;
	wire [32:0] a_ext;
	wire [32:0] b_ext;
	wire [32:0] w_sum;
	assign is_slt = (op == 4'd8) || (op == 4'd9);
	assign is_sub = (op == 4'd1) || is_slt;
	assign slt_signed = op == 4'd8;
	assign a_ext = {slt_signed & a[31], a};
	assign b_ext = {slt_signed & b[31], b};
	assign w_sum = (a_ext + (b_ext ^ {33 {is_sub}})) + {32'd0, is_sub};
	wire is_sll;
	wire sh_fill;
	reg [31:0] a_rev;
	wire [31:0] sh_in;
	wire [31:0] sh_out;
	reg [31:0] sh_out_rev;
	assign is_sll = op == 4'd5;
	assign sh_fill = (op == 4'd7) & a[31];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < 32; i = i + 1)
				a_rev[i] = a[31 - i];
		end
	end
	assign sh_in = (is_sll ? a_rev : a);
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	assign sh_out = sv2v_cast_32_signed($signed({sh_fill, sh_in}) >>> shamt);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < 32; i = i + 1)
				sh_out_rev[i] = sh_out[31 - i];
		end
	end
	wire sel_addsub;
	wire sel_and;
	wire sel_or;
	wire sel_xor;
	wire sel_sr;
	assign sel_addsub = (op == 4'd0) || (op == 4'd1);
	assign sel_and = op == 4'd2;
	assign sel_or = op == 4'd3;
	assign sel_xor = op == 4'd4;
	assign sel_sr = (op == 4'd6) || (op == 4'd7);
	assign y = (((((({32 {sel_addsub}} & w_sum[31:0]) | ({32 {sel_and}} & (a & b))) | ({32 {sel_or}} & (a | b))) | ({32 {sel_xor}} & (a ^ b))) | ({32 {sel_sr}} & sh_out)) | ({32 {is_sll}} & sh_out_rev)) | ({32 {is_slt}} & {{PAD_WIDTH {1'b0}}, w_sum[32]});
	initial _sv2v_0 = 0;
endmodule
module rv32i_imm_gen (
	insn,
	imm
);
	reg _sv2v_0;
	input wire [31:0] insn;
	output reg [31:0] imm;
	localparam signed [31:0] IMM_I_SIGN_BITS = 20;
	localparam signed [31:0] IMM_S_SIGN_BITS = 20;
	localparam signed [31:0] IMM_B_SIGN_BITS = 20;
	localparam signed [31:0] IMM_J_SIGN_BITS = 12;
	localparam signed [31:0] IMM_U_LOW_BITS = 12;
	localparam signed [31:0] IMM_B_J_LSB_BITS = 1;
	localparam [4:0] OPC_STORE = 5'b01000;
	localparam [4:0] OPC_BRANCH = 5'b11000;
	localparam [4:0] OPC_LUI = 5'b01101;
	localparam [4:0] OPC_AUIPC = 5'b00101;
	localparam [4:0] OPC_JAL = 5'b11011;
	wire [31:0] imm_i;
	wire [31:0] imm_s;
	wire [31:0] imm_b;
	wire [31:0] imm_u;
	wire [31:0] imm_j;
	assign imm_i = {{IMM_I_SIGN_BITS {insn[31]}}, insn[31:20]};
	assign imm_s = {{IMM_S_SIGN_BITS {insn[31]}}, insn[31:25], insn[11:7]};
	assign imm_b = {{IMM_B_SIGN_BITS {insn[31]}}, insn[7], insn[30:25], insn[11:8], {IMM_B_J_LSB_BITS {1'b0}}};
	assign imm_u = {insn[31:12], {IMM_U_LOW_BITS {1'b0}}};
	assign imm_j = {{IMM_J_SIGN_BITS {insn[31]}}, insn[19:12], insn[20], insn[30:21], {IMM_B_J_LSB_BITS {1'b0}}};
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (insn[6:2])
			OPC_STORE: imm = imm_s;
			OPC_BRANCH: imm = imm_b;
			OPC_LUI, OPC_AUIPC: imm = imm_u;
			OPC_JAL: imm = imm_j;
			default: imm = imm_i;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module rv32i_decode (
	insn,
	alu_op,
	imm_sel,
	alu_src_a_pc,
	alu_src_b_imm,
	rd_wen,
	dmem_req,
	dmem_we,
	dmem_size,
	branch,
	jump,
	jalr,
	halt_cause,
	csr_stub,
	m_op,
	csr_op,
	mret
);
	reg _sv2v_0;
	parameter [0:0] M_EXT = 1'b0;
	parameter [0:0] ZICSR = 1'b0;
	input wire [31:0] insn;
	output reg [3:0] alu_op;
	output reg [2:0] imm_sel;
	output reg alu_src_a_pc;
	output reg alu_src_b_imm;
	output reg rd_wen;
	output reg dmem_req;
	output reg dmem_we;
	output reg [1:0] dmem_size;
	output reg branch;
	output reg jump;
	output reg jalr;
	output reg [3:0] halt_cause;
	output reg csr_stub;
	output reg m_op;
	output reg csr_op;
	output reg mret;
	localparam [6:0] OPCODE_OP = 7'b0110011;
	localparam [6:0] OPCODE_OP_IMM = 7'b0010011;
	localparam [6:0] OPCODE_LOAD = 7'b0000011;
	localparam [6:0] OPCODE_STORE = 7'b0100011;
	localparam [6:0] OPCODE_BRANCH = 7'b1100011;
	localparam [6:0] OPCODE_JAL = 7'b1101111;
	localparam [6:0] OPCODE_JALR = 7'b1100111;
	localparam [6:0] OPCODE_LUI = 7'b0110111;
	localparam [6:0] OPCODE_AUIPC = 7'b0010111;
	localparam [6:0] OPCODE_SYSTEM = 7'b1110011;
	localparam [6:0] OPCODE_FENCE = 7'b0001111;
	localparam [2:0] F3_ADD = 3'b000;
	localparam [2:0] F3_SLL = 3'b001;
	localparam [2:0] F3_SLT = 3'b010;
	localparam [2:0] F3_SLTU = 3'b011;
	localparam [2:0] F3_XOR = 3'b100;
	localparam [2:0] F3_SR = 3'b101;
	localparam [2:0] F3_OR = 3'b110;
	localparam [2:0] F3_AND = 3'b111;
	localparam [6:0] F7_ZERO = 7'b0000000;
	localparam [6:0] F7_SUB = 7'b0100000;
	localparam [6:0] F7_SRA = 7'b0100000;
	localparam [6:0] F7_MULDIV = 7'b0000001;
	localparam [2:0] F3_PRIV = 3'b000;
	localparam [2:0] F3_CSRRW = 3'b001;
	localparam [2:0] F3_CSRRS = 3'b010;
	localparam [2:0] F3_CSRRC = 3'b011;
	localparam [2:0] F3_CSRRWI = 3'b101;
	localparam [2:0] F3_CSRRSI = 3'b110;
	localparam [2:0] F3_CSRRCI = 3'b111;
	localparam [11:0] SYS_ECALL = 12'h000;
	localparam [11:0] SYS_EBREAK = 12'h001;
	localparam [11:0] SYS_MRET = 12'h302;
	localparam [11:0] SYS_WFI = 12'h105;
	localparam [2:0] F3_FENCE = 3'b000;
	localparam [2:0] F3_FENCEI = 3'b001;
	localparam [2:0] F3_DC = 3'bzzz;
	localparam [6:0] F7_DC = 7'bzzzzzzz;
	wire [6:0] opcode;
	wire [2:0] funct3;
	wire [6:0] funct7;
	assign opcode = insn[6:0];
	assign funct3 = insn[14:12];
	assign funct7 = insn[31:25];
	localparam [3:0] rv32i_pkg_HALT_EBREAK = 4'h2;
	localparam [3:0] rv32i_pkg_HALT_ECALL = 4'h1;
	localparam [3:0] rv32i_pkg_HALT_ILL = 4'hf;
	localparam [3:0] rv32i_pkg_HALT_NONE = 4'h0;
	always @(*) begin
		if (_sv2v_0)
			;
		alu_op = 4'd0;
		imm_sel = 3'd0;
		alu_src_a_pc = 1'b0;
		alu_src_b_imm = 1'b0;
		rd_wen = 1'b0;
		dmem_req = 1'b0;
		dmem_we = 1'b0;
		dmem_size = 2'b00;
		branch = 1'b0;
		jump = 1'b0;
		jalr = 1'b0;
		halt_cause = rv32i_pkg_HALT_NONE;
		csr_stub = 1'b0;
		m_op = 1'b0;
		csr_op = 1'b0;
		mret = 1'b0;
		(* full_case, parallel_case *)
		casez ({opcode, funct3, funct7})
			{OPCODE_OP, F3_ADD, F7_ZERO}: begin
				alu_op = 4'd0;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_ADD, F7_SUB}: begin
				alu_op = 4'd1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_SLL, F7_ZERO}: begin
				alu_op = 4'd5;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_SLT, F7_ZERO}: begin
				alu_op = 4'd8;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_SLTU, F7_ZERO}: begin
				alu_op = 4'd9;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_XOR, F7_ZERO}: begin
				alu_op = 4'd4;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_SR, F7_ZERO}: begin
				alu_op = 4'd6;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_SR, F7_SRA}: begin
				alu_op = 4'd7;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_OR, F7_ZERO}: begin
				alu_op = 4'd3;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_AND, F7_ZERO}: begin
				alu_op = 4'd2;
				rd_wen = 1'b1;
			end
			{OPCODE_OP, F3_DC, F7_MULDIV}:
				if (M_EXT) begin
					m_op = 1'b1;
					rd_wen = 1'b1;
				end
				else
					halt_cause = rv32i_pkg_HALT_ILL;
			{OPCODE_OP_IMM, F3_ADD, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_SLT, F7_DC}: begin
				alu_op = 4'd8;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_SLTU, F7_DC}: begin
				alu_op = 4'd9;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_XOR, F7_DC}: begin
				alu_op = 4'd4;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_OR, F7_DC}: begin
				alu_op = 4'd3;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_AND, F7_DC}: begin
				alu_op = 4'd2;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_SLL, F7_ZERO}: begin
				alu_op = 4'd5;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_SR, F7_ZERO}: begin
				alu_op = 4'd6;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_OP_IMM, F3_SR, F7_SRA}: begin
				alu_op = 4'd7;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_LOAD, F3_ADD, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				dmem_req = 1'b1;
				dmem_size = 2'b00;
			end
			{OPCODE_LOAD, F3_SLL, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				dmem_req = 1'b1;
				dmem_size = 2'b01;
			end
			{OPCODE_LOAD, F3_SLT, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				dmem_req = 1'b1;
				dmem_size = 2'b10;
			end
			{OPCODE_LOAD, F3_XOR, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				dmem_req = 1'b1;
				dmem_size = 2'b00;
			end
			{OPCODE_LOAD, F3_SR, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				dmem_req = 1'b1;
				dmem_size = 2'b01;
			end
			{OPCODE_STORE, F3_ADD, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd1;
				alu_src_b_imm = 1'b1;
				dmem_req = 1'b1;
				dmem_we = 1'b1;
				dmem_size = 2'b00;
			end
			{OPCODE_STORE, F3_SLL, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd1;
				alu_src_b_imm = 1'b1;
				dmem_req = 1'b1;
				dmem_we = 1'b1;
				dmem_size = 2'b01;
			end
			{OPCODE_STORE, F3_SLT, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd1;
				alu_src_b_imm = 1'b1;
				dmem_req = 1'b1;
				dmem_we = 1'b1;
				dmem_size = 2'b10;
			end
			{OPCODE_BRANCH, F3_ADD, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_BRANCH, F3_SLL, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_BRANCH, F3_XOR, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_BRANCH, F3_SR, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_BRANCH, F3_OR, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_BRANCH, F3_AND, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd2;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				branch = 1'b1;
			end
			{OPCODE_JAL, F3_DC, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd4;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				jump = 1'b1;
			end
			{OPCODE_JALR, F3_ADD, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd0;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
				jalr = 1'b1;
			end
			{OPCODE_LUI, F3_DC, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd3;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_AUIPC, F3_DC, F7_DC}: begin
				alu_op = 4'd0;
				imm_sel = 3'd3;
				alu_src_a_pc = 1'b1;
				alu_src_b_imm = 1'b1;
				rd_wen = 1'b1;
			end
			{OPCODE_SYSTEM, F3_PRIV, F7_DC}:
				if (ZICSR && (insn[19:7] != 13'd0))
					halt_cause = rv32i_pkg_HALT_ILL;
				else
					(* full_case, parallel_case *)
					case (insn[31:20])
						SYS_ECALL: halt_cause = rv32i_pkg_HALT_ECALL;
						SYS_EBREAK: halt_cause = rv32i_pkg_HALT_EBREAK;
						SYS_MRET: mret = ZICSR;
						SYS_WFI:
							if (!ZICSR)
								halt_cause = rv32i_pkg_HALT_ILL;
						default: halt_cause = rv32i_pkg_HALT_ILL;
					endcase
			{OPCODE_SYSTEM, F3_CSRRW, F7_DC}, {OPCODE_SYSTEM, F3_CSRRS, F7_DC}, {OPCODE_SYSTEM, F3_CSRRC, F7_DC}, {OPCODE_SYSTEM, F3_CSRRWI, F7_DC}, {OPCODE_SYSTEM, F3_CSRRSI, F7_DC}, {OPCODE_SYSTEM, F3_CSRRCI, F7_DC}: begin
				csr_stub = ~ZICSR;
				csr_op = ZICSR;
				rd_wen = 1'b1;
			end
			{OPCODE_FENCE, F3_FENCE, F7_DC}:
				;
			{OPCODE_FENCE, F3_FENCEI, F7_DC}:
				;
			default: halt_cause = rv32i_pkg_HALT_ILL;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module gatling_regfile (
	clk,
	rs_ctx,
	rs1_addr,
	rs2_addr,
	rs1_data,
	rs2_data,
	rd_ctx,
	rd_addr,
	rd_data,
	rd_wen
);
	parameter signed [31:0] NUM_HARTS = 4;
	input wire clk;
	input wire [$clog2(NUM_HARTS) - 1:0] rs_ctx;
	input wire [4:0] rs1_addr;
	input wire [4:0] rs2_addr;
	output wire [31:0] rs1_data;
	output wire [31:0] rs2_data;
	input wire [$clog2(NUM_HARTS) - 1:0] rd_ctx;
	input wire [4:0] rd_addr;
	input wire [31:0] rd_data;
	input wire rd_wen;
	localparam signed [31:0] REGS_PER_CTX = 32;
	localparam signed [31:0] ENTRIES = NUM_HARTS * REGS_PER_CTX;
	(* ram_style = "block" *) reg [31:0] regs_a [0:ENTRIES - 1];
	(* ram_style = "block" *) reg [31:0] regs_b [0:ENTRIES - 1];
	reg [31:0] q1;
	reg [31:0] q2;
	reg rs1_zero_q;
	reg rs2_zero_q;
	always @(posedge clk) begin
		if (rd_wen)
			regs_a[{rd_ctx, rd_addr}] <= rd_data;
		q1 <= regs_a[{rs_ctx, rs1_addr}];
	end
	always @(posedge clk) begin
		if (rd_wen)
			regs_b[{rd_ctx, rd_addr}] <= rd_data;
		q2 <= regs_b[{rs_ctx, rs2_addr}];
	end
	always @(posedge clk) begin
		rs1_zero_q <= rs1_addr == 5'd0;
		rs2_zero_q <= rs2_addr == 5'd0;
	end
	assign rs1_data = (rs1_zero_q ? 32'd0 : q1);
	assign rs2_data = (rs2_zero_q ? 32'd0 : q2);
endmodule
module gatling_core (
	clk,
	rst_n,
	hart_run,
	imem_ctx,
	imem_addr,
	imem_rdata,
	dmem_req,
	dmem_ctx,
	dmem_addr,
	dmem_rdata,
	dmem_wstrb,
	dmem_wdata,
	halted,
	halt_cause,
	done,
	xc_req,
	xc_ctx,
	xc_funct3,
	xc_reg0,
	xc_rs1,
	xc_imm,
	xc_ok,
	xc_rdata,
	rvfi_valid,
	rvfi_ctx,
	rvfi_order,
	rvfi_pc_rdata,
	rvfi_pc_wdata,
	rvfi_insn,
	rvfi_trap,
	rvfi_rs1_addr,
	rvfi_rs2_addr,
	rvfi_rs1_rdata,
	rvfi_rs2_rdata,
	rvfi_rd_addr,
	rvfi_rd_wdata,
	rvfi_mem_addr,
	rvfi_mem_rmask,
	rvfi_mem_wmask,
	rvfi_mem_rdata,
	rvfi_mem_wdata
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_HARTS = 4;
	parameter [31:0] RESET_ADDR = 32'h00000000;
	parameter [0:0] XCELL_EN = 1'b0;
	input wire clk;
	input wire rst_n;
	input wire [NUM_HARTS - 1:0] hart_run;
	output wire [$clog2(NUM_HARTS) - 1:0] imem_ctx;
	output wire [31:0] imem_addr;
	input wire [31:0] imem_rdata;
	output wire dmem_req;
	output wire [$clog2(NUM_HARTS) - 1:0] dmem_ctx;
	output wire [31:0] dmem_addr;
	input wire [31:0] dmem_rdata;
	output wire [3:0] dmem_wstrb;
	output wire [31:0] dmem_wdata;
	output wire [NUM_HARTS - 1:0] halted;
	output wire [(NUM_HARTS * 4) - 1:0] halt_cause;
	output reg [NUM_HARTS - 1:0] done;
	output wire xc_req;
	output wire [$clog2(NUM_HARTS) - 1:0] xc_ctx;
	output wire [2:0] xc_funct3;
	output wire xc_reg0;
	output wire [31:0] xc_rs1;
	output wire [11:0] xc_imm;
	input wire xc_ok;
	input wire [31:0] xc_rdata;
	output wire rvfi_valid;
	output wire [$clog2(NUM_HARTS) - 1:0] rvfi_ctx;
	output wire [63:0] rvfi_order;
	output wire [31:0] rvfi_pc_rdata;
	output wire [31:0] rvfi_pc_wdata;
	output wire [31:0] rvfi_insn;
	output wire rvfi_trap;
	output wire [4:0] rvfi_rs1_addr;
	output wire [4:0] rvfi_rs2_addr;
	output wire [31:0] rvfi_rs1_rdata;
	output wire [31:0] rvfi_rs2_rdata;
	output wire [4:0] rvfi_rd_addr;
	output wire [31:0] rvfi_rd_wdata;
	output wire [31:0] rvfi_mem_addr;
	output wire [3:0] rvfi_mem_rmask;
	output wire [3:0] rvfi_mem_wmask;
	output wire [31:0] rvfi_mem_rdata;
	output wire [31:0] rvfi_mem_wdata;
	localparam signed [31:0] HART_W = $clog2(NUM_HARTS);
	localparam signed [31:0] PIPELINE_DEPTH = 4;
	initial begin : param_check
		if (NUM_HARTS < PIPELINE_DEPTH)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/riscv-ip/gatling-rv32i/rtl/top/gatling_core.sv:152:13 - gatling_core.param_check.<unnamed_block>\n msg: ", $time, "gatling_core: NUM_HARTS (%0d) must be >= the pipeline depth (%0d) -- fewer contexts than stages puts two instructions of one context in flight", NUM_HARTS, PIPELINE_DEPTH);
	end
	localparam [31:0] PC_INCR = 32'd4;
	localparam [31:0] JALR_ALIGN_MASK = 32'hfffffffe;
	localparam [6:0] OPCODE_LUI = 7'b0110111;
	localparam [2:0] F3_BEQ = 3'b000;
	localparam [2:0] F3_BNE = 3'b001;
	localparam [2:0] F3_BLT = 3'b100;
	localparam [2:0] F3_BGE = 3'b101;
	localparam [2:0] F3_BLTU = 3'b110;
	localparam [2:0] F3_BGEU = 3'b111;
	localparam [3:0] STRB_BYTE = 4'b0001;
	localparam [3:0] STRB_HALF = 4'b0011;
	localparam [3:0] STRB_WORD = 4'b1111;
	localparam [6:0] OPCODE_XCELL = 7'b0001011;
	localparam [2:0] XC_POP = 3'b000;
	localparam [2:0] XC_ECTX = 3'b010;
	localparam [2:0] XC_CFG = 3'b110;
	localparam [2:0] XC_RSVD = 3'b111;
	localparam [3:0] HALT_DONE = 4'h8;
	wire w_aresetn;
	reset_sync #(
		.N(3),
		.KEEP_ATTRS(1'b1),
		.IN_ACTIVE_LOW(1'b1),
		.OUT_ACTIVE_LOW(1'b1),
		.ASYNC_ASSERT(1'b1)
	) u_reset_sync(
		.clk(clk),
		.rst_n(rst_n),
		.sync_rst_n(w_aresetn)
	);
	(* ram_style = "distributed" *) reg [31:0] pc_mem [0:NUM_HARTS - 1];
	reg [NUM_HARTS - 1:0] pc_fresh;
	wire [31:0] f_pc;
	reg [NUM_HARTS - 1:0] halted_q;
	reg [(NUM_HARTS * 4) - 1:0] cause_q;
	reg [(NUM_HARTS * 64) - 1:0] order_q;
	reg [HART_W - 1:0] sel_q;
	function automatic signed [HART_W - 1:0] sv2v_cast_3EA94_signed;
		input reg signed [HART_W - 1:0] inp;
		sv2v_cast_3EA94_signed = inp;
	endfunction
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn)
			sel_q <= 1'sb0;
		else if (sel_q == sv2v_cast_3EA94_signed(NUM_HARTS - 1))
			sel_q <= 1'sb0;
		else
			sel_q <= sel_q + 1'b1;
	wire f_valid;
	assign f_valid = (w_aresetn & hart_run[sel_q]) & ~halted_q[sel_q];
	assign f_pc = (pc_fresh[sel_q] ? RESET_ADDR : pc_mem[sel_q]);
	assign imem_ctx = sel_q;
	assign imem_addr = f_pc;
	reg d_valid;
	reg [HART_W - 1:0] d_ctx;
	reg [31:0] d_pc;
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn)
			d_valid <= 1'b0;
		else
			d_valid <= f_valid;
	always @(posedge clk) begin
		d_ctx <= sel_q;
		d_pc <= f_pc;
	end
	wire [31:0] d_insn;
	wire d_live;
	assign d_insn = imem_rdata;
	assign d_live = d_valid & hart_run[d_ctx];
	wire [3:0] dec_alu_op;
	wire dec_src_a_pc;
	wire dec_src_b_imm;
	wire dec_rd_wen;
	wire dec_dmem_req;
	wire dec_dmem_we;
	wire dec_branch;
	wire dec_jump;
	wire dec_jalr;
	wire dec_csr_stub;
	wire [3:0] dec_halt_cause;
	wire [31:0] d_imm;
	rv32i_decode u_decode(
		.insn(d_insn),
		.alu_op(dec_alu_op),
		.imm_sel(),
		.alu_src_a_pc(dec_src_a_pc),
		.alu_src_b_imm(dec_src_b_imm),
		.rd_wen(dec_rd_wen),
		.dmem_req(dec_dmem_req),
		.dmem_we(dec_dmem_we),
		.dmem_size(),
		.branch(dec_branch),
		.jump(dec_jump),
		.jalr(dec_jalr),
		.halt_cause(dec_halt_cause),
		.csr_stub(dec_csr_stub),
		.m_op(),
		.csr_op(),
		.mret()
	);
	rv32i_imm_gen u_imm_gen(
		.insn(d_insn),
		.imm(d_imm)
	);
	wire d_is_xc;
	assign d_is_xc = (XCELL_EN && (d_insn[6:0] == OPCODE_XCELL)) && (d_insn[14:12] != XC_RSVD);
	wire [31:0] x_rs1;
	wire [31:0] x_rs2;
	wire rf_wen;
	wire [HART_W - 1:0] rf_wctx;
	wire [4:0] rf_waddr;
	wire [31:0] rf_wdata;
	gatling_regfile #(.NUM_HARTS(NUM_HARTS)) u_regfile(
		.clk(clk),
		.rs_ctx(d_ctx),
		.rs1_addr((d_is_xc ? d_insn[11:7] : d_insn[19:15])),
		.rs2_addr(d_insn[24:20]),
		.rs1_data(x_rs1),
		.rs2_data(x_rs2),
		.rd_ctx(rf_wctx),
		.rd_addr(rf_waddr),
		.rd_data(rf_wdata),
		.rd_wen(rf_wen)
	);
	reg x_valid;
	reg [HART_W - 1:0] x_ctx;
	reg [31:0] x_pc;
	reg [31:0] x_pc_imm;
	reg [31:0] x_pc4;
	reg [31:0] x_insn;
	reg [31:0] x_imm;
	reg [3:0] x_alu_op;
	reg x_src_a_pc;
	reg x_src_b_imm;
	reg x_rd_wen;
	reg x_dmem_req;
	reg x_dmem_we;
	reg x_branch;
	reg x_jump;
	reg x_jalr;
	reg x_csr_stub;
	reg x_lui;
	reg x_is_xc;
	reg [3:0] x_dec_cause;
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn)
			x_valid <= 1'b0;
		else
			x_valid <= d_live;
	localparam [3:0] rv32i_pkg_HALT_NONE = 4'h0;
	always @(posedge clk) begin
		x_ctx <= d_ctx;
		x_pc <= d_pc;
		x_pc_imm <= d_pc + d_imm;
		x_pc4 <= d_pc + PC_INCR;
		x_insn <= d_insn;
		x_imm <= d_imm;
		x_alu_op <= dec_alu_op;
		x_src_a_pc <= dec_src_a_pc;
		x_src_b_imm <= dec_src_b_imm;
		x_rd_wen <= (d_is_xc ? (d_insn[14:12] == XC_POP) || (d_insn[14:12] == XC_CFG) : dec_rd_wen);
		x_dmem_req <= dec_dmem_req & ~d_is_xc;
		x_dmem_we <= dec_dmem_we;
		x_branch <= dec_branch;
		x_jump <= dec_jump;
		x_jalr <= dec_jalr;
		x_csr_stub <= dec_csr_stub;
		x_lui <= d_insn[6:0] == OPCODE_LUI;
		x_dec_cause <= (d_is_xc ? rv32i_pkg_HALT_NONE : dec_halt_cause);
		x_is_xc <= d_is_xc;
	end
	wire x_live;
	wire [2:0] x_funct3;
	wire [4:0] x_rd;
	assign x_live = x_valid & hart_run[x_ctx];
	assign x_funct3 = x_insn[14:12];
	assign x_rd = x_insn[11:7];
	wire [31:0] alu_a;
	wire [31:0] alu_b;
	wire [31:0] alu_y;
	assign alu_a = (x_src_a_pc ? x_pc : x_rs1);
	assign alu_b = (x_src_b_imm ? x_imm : x_rs2);
	rv32i_alu u_alu(
		.op(x_alu_op),
		.a(alu_a),
		.b(alu_b),
		.y(alu_y),
		.eq(),
		.lt(),
		.ltu()
	);
	wire cmp_eq;
	wire cmp_lt;
	wire cmp_signed;
	reg branch_cond;
	wire branch_taken;
	assign cmp_signed = ~x_funct3[1];
	assign cmp_eq = x_rs1 == x_rs2;
	assign cmp_lt = $signed({cmp_signed & x_rs1[31], x_rs1}) < $signed({cmp_signed & x_rs2[31], x_rs2});
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (x_funct3)
			F3_BEQ: branch_cond = cmp_eq;
			F3_BNE: branch_cond = ~cmp_eq;
			F3_BLT: branch_cond = cmp_lt;
			F3_BGE: branch_cond = ~cmp_lt;
			F3_BLTU: branch_cond = cmp_lt;
			F3_BGEU: branch_cond = ~cmp_lt;
			default: branch_cond = 1'b0;
		endcase
	end
	assign branch_taken = x_branch & branch_cond;
	reg [31:0] next_pc;
	always @(*) begin
		if (_sv2v_0)
			;
		if (x_jalr)
			next_pc = (x_rs1 + x_imm) & JALR_ALIGN_MASK;
		else if (x_jump || branch_taken)
			next_pc = x_pc_imm;
		else
			next_pc = x_pc4;
	end
	wire ls_active;
	wire ls_load;
	wire ls_store;
	wire ls_misalign;
	wire ls_ok;
	wire [1:0] ls_offset;
	reg [3:0] ls_size_mask;
	reg [31:0] ls_data_mask;
	assign ls_active = x_live & x_dmem_req;
	assign ls_load = ls_active & ~x_dmem_we;
	assign ls_store = ls_active & x_dmem_we;
	assign ls_offset = x_rs1[1:0] + x_imm[1:0];
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (x_funct3[1:0])
			2'b00: begin
				ls_size_mask = STRB_BYTE;
				ls_data_mask = 32'h000000ff;
			end
			2'b01: begin
				ls_size_mask = STRB_HALF;
				ls_data_mask = 32'h0000ffff;
			end
			default: begin
				ls_size_mask = STRB_WORD;
				ls_data_mask = 32'hffffffff;
			end
		endcase
	end
	assign ls_misalign = ls_active & (x_funct3[1:0] == 2'b01 ? ls_offset[0] : (x_funct3[1:0] == 2'b10 ? ls_offset != 2'b00 : 1'b0));
	assign ls_ok = ls_active & ~ls_misalign;
	assign dmem_req = ls_active;
	assign dmem_ctx = x_ctx;
	assign dmem_addr = {alu_y[31:2], 2'b00};
	assign dmem_wdata = x_rs2 << {ls_offset, 3'b000};
	assign dmem_wstrb = (ls_store & ~ls_misalign ? ls_size_mask << ls_offset : 4'b0000);
	wire [1:0] tgt_lo_jalr;
	wire misalign_target;
	wire [3:0] halt_cause_eff;
	wire halt_now;
	assign tgt_lo_jalr = (x_rs1[1:0] + x_imm[1:0]) & 2'b10;
	assign misalign_target = ((x_jump | branch_taken) & (x_pc_imm[1:0] != 2'b00)) | (x_jalr & (tgt_lo_jalr != 2'b00));
	localparam [3:0] rv32i_pkg_HALT_IALIGN = 4'h3;
	localparam [3:0] rv32i_pkg_HALT_LALIGN = 4'h4;
	localparam [3:0] rv32i_pkg_HALT_SALIGN = 4'h5;
	assign halt_cause_eff = (x_dec_cause | (misalign_target ? rv32i_pkg_HALT_IALIGN : rv32i_pkg_HALT_NONE)) | (ls_misalign ? (x_dmem_we ? rv32i_pkg_HALT_SALIGN : rv32i_pkg_HALT_LALIGN) : rv32i_pkg_HALT_NONE);
	assign halt_now = x_live & |halt_cause_eff;
	wire x_stall;
	wire x_ectx;
	assign xc_req = x_live & x_is_xc;
	assign xc_ctx = x_ctx;
	assign xc_funct3 = x_funct3;
	assign xc_reg0 = x_rd == 5'd0;
	assign xc_rs1 = x_rs1;
	assign xc_imm = x_insn[31:20];
	assign x_stall = xc_req & ~xc_ok;
	assign x_ectx = (xc_req & xc_ok) & (x_funct3 == XC_ECTX);
	wire x_rd_wb;
	wire [31:0] x_wb;
	assign x_rd_wb = (x_rd_wen & (x_rd != 5'd0)) & ~halt_now;
	assign x_wb = (x_csr_stub ? 32'd0 : (x_lui ? x_imm : (x_jump || x_jalr ? x_pc4 : alu_y)));
	wire pc_we;
	assign pc_we = ((x_live & ~halt_now) & ~x_stall) & ~x_ectx;
	always @(posedge clk)
		if (pc_we)
			pc_mem[x_ctx] <= next_pc;
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn) begin : sv2v_autoblock_1
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				begin
					pc_fresh[c] <= 1'b1;
					halted_q[c] <= 1'b0;
					cause_q[c * 4+:4] <= rv32i_pkg_HALT_NONE;
				end
		end
		else begin : sv2v_autoblock_2
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				if (!hart_run[c]) begin
					pc_fresh[c] <= 1'b1;
					halted_q[c] <= 1'b0;
					cause_q[c * 4+:4] <= rv32i_pkg_HALT_NONE;
				end
				else if (x_live && (x_ctx == sv2v_cast_3EA94_signed(c))) begin
					if (halt_now) begin
						halted_q[c] <= 1'b1;
						cause_q[c * 4+:4] <= halt_cause_eff;
					end
					else if (x_ectx) begin
						halted_q[c] <= 1'b1;
						cause_q[c * 4+:4] <= HALT_DONE;
					end
					else if (!x_stall)
						pc_fresh[c] <= 1'b0;
				end
		end
	assign halted = halted_q;
	assign halt_cause = cause_q;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				done[c] = halted_q[c] & (cause_q[c * 4+:4] == HALT_DONE);
		end
	end
	reg w_valid;
	reg [HART_W - 1:0] w_ctx;
	reg [31:0] w_pc;
	reg [31:0] w_pc_wdata;
	reg [31:0] w_insn;
	reg [31:0] w_wb;
	reg w_trap;
	reg w_rd_wb;
	reg w_load;
	reg w_xc_rd;
	reg [2:0] w_funct3;
	reg [1:0] w_offset;
	reg [4:0] w_rs1_addr;
	reg [4:0] w_rs2_addr;
	reg [4:0] w_rd;
	reg [31:0] w_rs1;
	reg [31:0] w_rs2;
	reg [31:0] w_mem_addr;
	reg [31:0] w_mem_wdata;
	reg [3:0] w_mem_rmask;
	reg [3:0] w_mem_wmask;
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn)
			w_valid <= 1'b0;
		else
			w_valid <= x_live & ~x_stall;
	always @(posedge clk) begin
		w_ctx <= x_ctx;
		w_pc <= x_pc;
		w_pc_wdata <= next_pc;
		w_insn <= x_insn;
		w_trap <= halt_now;
		w_rd_wb <= x_rd_wb;
		w_rd <= x_rd;
		w_wb <= x_wb;
		w_load <= ls_load & ~ls_misalign;
		w_xc_rd <= x_is_xc;
		w_funct3 <= x_funct3;
		w_offset <= ls_offset;
		w_rs1_addr <= (x_is_xc && !x_rd_wen ? x_insn[11:7] : x_insn[19:15]);
		w_rs2_addr <= x_insn[24:20];
		w_rs1 <= x_rs1;
		w_rs2 <= x_rs2;
		w_mem_addr <= (ls_ok ? dmem_addr : 32'd0);
		w_mem_rmask <= (ls_ok & ~x_dmem_we ? ls_size_mask << ls_offset : 4'd0);
		w_mem_wmask <= (ls_ok & x_dmem_we ? ls_size_mask << ls_offset : 4'd0);
		w_mem_wdata <= (ls_ok & x_dmem_we ? (x_rs2 & ls_data_mask) << {ls_offset, 3'b000} : 32'd0);
	end
	wire w_live;
	wire [31:0] ld_shifted;
	reg [31:0] ld_data;
	wire [31:0] w_rd_wdata;
	assign w_live = w_valid & hart_run[w_ctx];
	assign ld_shifted = dmem_rdata >> {w_offset, 3'b000};
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (w_funct3)
			3'b000: ld_data = {{24 {ld_shifted[7]}}, ld_shifted[7:0]};
			3'b100: ld_data = {24'b000000000000000000000000, ld_shifted[7:0]};
			3'b001: ld_data = {{16 {ld_shifted[15]}}, ld_shifted[15:0]};
			3'b101: ld_data = {16'b0000000000000000, ld_shifted[15:0]};
			default: ld_data = dmem_rdata;
		endcase
	end
	assign w_rd_wdata = (w_xc_rd ? xc_rdata : (w_load ? ld_data : w_wb));
	assign rf_wen = w_live & w_rd_wb;
	assign rf_wctx = w_ctx;
	assign rf_waddr = w_rd;
	assign rf_wdata = w_rd_wdata;
	always @(posedge clk or negedge w_aresetn)
		if (!w_aresetn) begin : sv2v_autoblock_4
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				order_q[c * 64+:64] <= 1'sb0;
		end
		else begin : sv2v_autoblock_5
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				if (!hart_run[c])
					order_q[c * 64+:64] <= 1'sb0;
				else if (w_live && (w_ctx == sv2v_cast_3EA94_signed(c)))
					order_q[c * 64+:64] <= order_q[c * 64+:64] + 64'd1;
		end
	assign rvfi_valid = w_live;
	assign rvfi_ctx = w_ctx;
	assign rvfi_order = order_q[w_ctx * 64+:64];
	assign rvfi_pc_rdata = w_pc;
	assign rvfi_pc_wdata = w_pc_wdata;
	assign rvfi_insn = w_insn;
	assign rvfi_trap = w_trap;
	assign rvfi_rs1_addr = w_rs1_addr;
	assign rvfi_rs2_addr = w_rs2_addr;
	assign rvfi_rs1_rdata = w_rs1;
	assign rvfi_rs2_rdata = w_rs2;
	assign rvfi_rd_addr = (w_rd_wb ? w_rd : 5'd0);
	assign rvfi_rd_wdata = (w_rd_wb ? w_rd_wdata : 32'd0);
	assign rvfi_mem_addr = w_mem_addr;
	assign rvfi_mem_rmask = w_mem_rmask;
	assign rvfi_mem_wmask = w_mem_wmask;
	assign rvfi_mem_rdata = (w_mem_rmask != 4'd0 ? dmem_rdata : 32'd0);
	assign rvfi_mem_wdata = w_mem_wdata;
	initial _sv2v_0 = 0;
endmodule
module gatling_xcell (
	clk,
	aresetn,
	xc_req,
	xc_ctx,
	xc_funct3,
	xc_reg0,
	xc_rs1,
	xc_imm,
	xc_ok,
	xc_rdata,
	hart_run,
	done,
	cfg_func_sel,
	cfg_op_lines,
	cfg_threshold,
	cfg_credit_batch,
	min_rd_valid,
	min_rd_addr,
	min_rd_data,
	min_occupancy,
	line_consumed,
	mout_wr_valid,
	mout_wr_addr,
	mout_wr_data,
	mout_full,
	alu_valid,
	alu_ready,
	alu_op_line_a,
	alu_op_line_b,
	alu_func_sel,
	alu_acc_ctrl,
	alu_threshold,
	alu_result_valid,
	alu_result_ready,
	alu_result_line,
	alu_result_flags,
	flush_valid,
	flush_ready,
	flush_dest,
	flush_tag,
	kick_valid,
	kick_value,
	event_flags,
	ctx_stalled,
	ctx_stall_op
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_HARTS = 4;
	parameter signed [31:0] LINE_W = 32;
	parameter signed [31:0] IN_DEPTH = 32;
	parameter signed [31:0] OUT_DEPTH = 32;
	parameter signed [31:0] HART_W = $clog2(NUM_HARTS);
	parameter signed [31:0] IN_AW = $clog2(IN_DEPTH);
	parameter signed [31:0] OUT_AW = $clog2(OUT_DEPTH);
	parameter signed [31:0] IN_OCC_W = $clog2(IN_DEPTH + 1);
	input wire clk;
	input wire aresetn;
	input wire xc_req;
	input wire [HART_W - 1:0] xc_ctx;
	input wire [2:0] xc_funct3;
	input wire xc_reg0;
	input wire [31:0] xc_rs1;
	input wire [11:0] xc_imm;
	output reg xc_ok;
	output wire [31:0] xc_rdata;
	input wire [NUM_HARTS - 1:0] hart_run;
	input wire [NUM_HARTS - 1:0] done;
	input wire [(NUM_HARTS * 9) - 1:0] cfg_func_sel;
	input wire [(NUM_HARTS * 2) - 1:0] cfg_op_lines;
	input wire [(NUM_HARTS * 16) - 1:0] cfg_threshold;
	input wire [(NUM_HARTS * 32) - 1:0] cfg_credit_batch;
	output reg [0:NUM_HARTS - 1] min_rd_valid;
	output reg [(NUM_HARTS * IN_AW) - 1:0] min_rd_addr;
	input wire [(NUM_HARTS * LINE_W) - 1:0] min_rd_data;
	input wire [(NUM_HARTS * IN_OCC_W) - 1:0] min_occupancy;
	output reg [0:NUM_HARTS - 1] line_consumed;
	output reg [0:NUM_HARTS - 1] mout_wr_valid;
	output reg [(NUM_HARTS * OUT_AW) - 1:0] mout_wr_addr;
	output reg [(NUM_HARTS * LINE_W) - 1:0] mout_wr_data;
	input wire [0:NUM_HARTS - 1] mout_full;
	output reg [0:NUM_HARTS - 1] alu_valid;
	input wire [0:NUM_HARTS - 1] alu_ready;
	output reg [(NUM_HARTS * LINE_W) - 1:0] alu_op_line_a;
	output reg [(NUM_HARTS * LINE_W) - 1:0] alu_op_line_b;
	output reg [(NUM_HARTS * 9) - 1:0] alu_func_sel;
	output reg [(NUM_HARTS * 2) - 1:0] alu_acc_ctrl;
	output reg [(NUM_HARTS * 16) - 1:0] alu_threshold;
	input wire [0:NUM_HARTS - 1] alu_result_valid;
	output reg [0:NUM_HARTS - 1] alu_result_ready;
	input wire [(NUM_HARTS * LINE_W) - 1:0] alu_result_line;
	input wire [(NUM_HARTS * LINE_W) - 1:0] alu_result_flags;
	output reg [0:NUM_HARTS - 1] flush_valid;
	input wire [0:NUM_HARTS - 1] flush_ready;
	output reg [(NUM_HARTS * 15) - 1:0] flush_dest;
	output reg [(NUM_HARTS * 4) - 1:0] flush_tag;
	output reg [0:NUM_HARTS - 1] kick_valid;
	output reg [(NUM_HARTS * 32) - 1:0] kick_value;
	output wire [NUM_HARTS - 1:0] event_flags;
	output wire [NUM_HARTS - 1:0] ctx_stalled;
	output reg [(NUM_HARTS * 3) - 1:0] ctx_stall_op;
	initial begin : param_check
		if (LINE_W != 32)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/riscv-ip/gatling-rv32i/rtl/fub/gatling_xcell.sv:150:13 - gatling_xcell.param_check.<unnamed_block>\n msg: ", $time, "gatling_xcell: LINE_W must be 32 (one register holds one line), got %0d", LINE_W);
		if ((NUM_HARTS < 4) || (NUM_HARTS > 32))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/riscv-ip/gatling-rv32i/rtl/fub/gatling_xcell.sv:152:13 - gatling_xcell.param_check.<unnamed_block>\n msg: ", $time, "gatling_xcell: NUM_HARTS must be in [4,32], got %0d", NUM_HARTS);
		if ((IN_DEPTH < 2) || (OUT_DEPTH < 2))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/riscv-ip/gatling-rv32i/rtl/fub/gatling_xcell.sv:154:13 - gatling_xcell.param_check.<unnamed_block>\n msg: ", $time, "gatling_xcell: IN_DEPTH and OUT_DEPTH must be >= 2");
	end
	localparam [2:0] XC_POP = 3'b000;
	localparam [2:0] XC_PUSH = 3'b001;
	localparam [2:0] XC_FLUSH = 3'b011;
	localparam [2:0] XC_KICK = 3'b100;
	localparam [2:0] XC_WAIT = 3'b101;
	localparam [11:0] CFG_ELEM_MODE = 12'd0;
	localparam [11:0] CFG_CREDIT_BATCH = 12'd1;
	reg [IN_AW - 1:0] ip_q [0:NUM_HARTS - 1];
	reg [OUT_AW - 1:0] op_q [0:NUM_HARTS - 1];
	reg [NUM_HARTS - 1:0] stg_cap_a_q;
	reg [NUM_HARTS - 1:0] stg_cap_b_q;
	reg [NUM_HARTS - 1:0] stg_two_q;
	reg [NUM_HARTS - 1:0] op_v_q;
	reg [NUM_HARTS - 1:0] flush_pend_q;
	reg [NUM_HARTS - 1:0] event_q;
	reg [NUM_HARTS - 1:0] stall_q;
	reg [2:0] stall_op_q [0:NUM_HARTS - 1];
	reg [LINE_W - 1:0] op_a_q [0:NUM_HARTS - 1];
	reg [LINE_W - 1:0] op_b_q [0:NUM_HARTS - 1];
	reg [8:0] func_q [0:NUM_HARTS - 1];
	reg [1:0] acc_q [0:NUM_HARTS - 1];
	reg [15:0] thr_q [0:NUM_HARTS - 1];
	reg [14:0] fdest_q [0:NUM_HARTS - 1];
	reg [3:0] ftag_q [0:NUM_HARTS - 1];
	reg [31:0] kval_q [0:NUM_HARTS - 1];
	reg [NUM_HARTS - 1:0] kvalid_q;
	wire k_stg_idle;
	wire k_need_two;
	wire k_lines_ok;
	wire k_wait_ok;
	wire [NUM_HARTS - 1:0] wait_mask;
	wire fire;
	assign k_stg_idle = (~stg_cap_a_q[xc_ctx] & ~stg_cap_b_q[xc_ctx]) & ~op_v_q[xc_ctx];
	assign k_need_two = cfg_op_lines[((NUM_HARTS - 1) - xc_ctx) * 2+:2] == 2'd2;
	function automatic signed [IN_OCC_W - 1:0] sv2v_cast_0A072_signed;
		input reg signed [IN_OCC_W - 1:0] inp;
		sv2v_cast_0A072_signed = inp;
	endfunction
	assign k_lines_ok = min_occupancy[((NUM_HARTS - 1) - xc_ctx) * IN_OCC_W+:IN_OCC_W] >= (k_need_two ? sv2v_cast_0A072_signed(2) : sv2v_cast_0A072_signed(1));
	assign wait_mask = xc_rs1[NUM_HARTS - 1:0];
	assign k_wait_ok = &((event_q | done) | ~wait_mask);
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (xc_funct3)
			XC_POP: xc_ok = (xc_reg0 ? k_stg_idle & k_lines_ok : min_occupancy[((NUM_HARTS - 1) - xc_ctx) * IN_OCC_W+:IN_OCC_W] != {IN_OCC_W * 1 {1'sb0}});
			XC_PUSH: xc_ok = ~mout_full[xc_ctx] & (~xc_reg0 | alu_result_valid[xc_ctx]);
			XC_FLUSH: xc_ok = ~flush_pend_q[xc_ctx];
			XC_WAIT: xc_ok = k_wait_ok;
			default: xc_ok = 1'b1;
		endcase
	end
	assign fire = xc_req & xc_ok;
	reg [NUM_HARTS - 1:0] in_x;
	reg [NUM_HARTS - 1:0] f_pop_alu;
	reg [NUM_HARTS - 1:0] f_pop_reg;
	reg [NUM_HARTS - 1:0] f_push;
	reg [NUM_HARTS - 1:0] f_push_alu;
	reg [NUM_HARTS - 1:0] f_flush;
	reg [NUM_HARTS - 1:0] f_kick;
	function automatic signed [HART_W - 1:0] sv2v_cast_3EA94_signed;
		input reg signed [HART_W - 1:0] inp;
		sv2v_cast_3EA94_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				begin
					in_x[c] = xc_req & (xc_ctx == sv2v_cast_3EA94_signed(c));
					f_pop_alu[c] = ((fire & in_x[c]) & (xc_funct3 == XC_POP)) & xc_reg0;
					f_pop_reg[c] = ((fire & in_x[c]) & (xc_funct3 == XC_POP)) & ~xc_reg0;
					f_push[c] = (fire & in_x[c]) & (xc_funct3 == XC_PUSH);
					f_push_alu[c] = f_push[c] & xc_reg0;
					f_flush[c] = (fire & in_x[c]) & (xc_funct3 == XC_FLUSH);
					f_kick[c] = (fire & in_x[c]) & (xc_funct3 == XC_KICK);
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				begin
					min_rd_valid[c] = (f_pop_alu[c] | f_pop_reg[c]) | (stg_cap_a_q[c] & stg_two_q[c]);
					min_rd_addr[((NUM_HARTS - 1) - c) * IN_AW+:IN_AW] = ip_q[c];
					line_consumed[c] = min_rd_valid[c];
					mout_wr_valid[c] = f_push[c];
					mout_wr_addr[((NUM_HARTS - 1) - c) * OUT_AW+:OUT_AW] = op_q[c];
					mout_wr_data[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W] = (xc_reg0 ? alu_result_line[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W] | alu_result_flags[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W] : xc_rs1);
					alu_result_ready[c] = f_push_alu[c];
					alu_valid[c] = op_v_q[c];
					alu_op_line_a[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W] = op_a_q[c];
					alu_op_line_b[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W] = op_b_q[c];
					alu_func_sel[((NUM_HARTS - 1) - c) * 9+:9] = func_q[c];
					alu_acc_ctrl[((NUM_HARTS - 1) - c) * 2+:2] = acc_q[c];
					alu_threshold[((NUM_HARTS - 1) - c) * 16+:16] = thr_q[c];
					flush_valid[c] = flush_pend_q[c];
					flush_dest[((NUM_HARTS - 1) - c) * 15+:15] = fdest_q[c];
					flush_tag[((NUM_HARTS - 1) - c) * 4+:4] = ftag_q[c];
					kick_valid[c] = kvalid_q[c];
					kick_value[((NUM_HARTS - 1) - c) * 32+:32] = kval_q[c];
					ctx_stall_op[((NUM_HARTS - 1) - c) * 3+:3] = stall_op_q[c];
				end
		end
	end
	assign event_flags = event_q;
	assign ctx_stalled = stall_q;
	function automatic signed [IN_AW - 1:0] sv2v_cast_175BE_signed;
		input reg signed [IN_AW - 1:0] inp;
		sv2v_cast_175BE_signed = inp;
	endfunction
	function automatic signed [OUT_AW - 1:0] sv2v_cast_67DA4_signed;
		input reg signed [OUT_AW - 1:0] inp;
		sv2v_cast_67DA4_signed = inp;
	endfunction
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			begin : sv2v_autoblock_3
				reg signed [31:0] c;
				for (c = 0; c < NUM_HARTS; c = c + 1)
					begin
						ip_q[c] <= 1'sb0;
						op_q[c] <= 1'sb0;
					end
			end
			stg_cap_b_q <= 1'sb0;
			stg_cap_a_q <= 1'sb0;
			stg_two_q <= 1'sb0;
			op_v_q <= 1'sb0;
			flush_pend_q <= 1'sb0;
			event_q <= 1'sb0;
			stall_q <= 1'sb0;
			kvalid_q <= 1'sb0;
		end
		else begin : sv2v_autoblock_4
			reg signed [31:0] c;
			for (c = 0; c < NUM_HARTS; c = c + 1)
				begin
					if (min_rd_valid[c])
						ip_q[c] <= (ip_q[c] == sv2v_cast_175BE_signed(IN_DEPTH - 1) ? {IN_AW {1'sb0}} : ip_q[c] + 1'b1);
					if (f_push[c])
						op_q[c] <= (op_q[c] == sv2v_cast_67DA4_signed(OUT_DEPTH - 1) ? {OUT_AW {1'sb0}} : op_q[c] + 1'b1);
					stg_cap_a_q[c] <= f_pop_alu[c];
					if (f_pop_alu[c])
						stg_two_q[c] <= k_need_two;
					stg_cap_b_q[c] <= stg_cap_a_q[c] & stg_two_q[c];
					if (alu_valid[c] && alu_ready[c])
						op_v_q[c] <= 1'b0;
					else if ((stg_cap_a_q[c] && !stg_two_q[c]) || stg_cap_b_q[c])
						op_v_q[c] <= 1'b1;
					if (flush_valid[c] && flush_ready[c])
						flush_pend_q[c] <= 1'b0;
					else if (f_flush[c])
						flush_pend_q[c] <= 1'b1;
					kvalid_q[c] <= f_kick[c];
					if (!hart_run[c])
						event_q[c] <= 1'b0;
					else if (f_kick[c])
						event_q[c] <= 1'b1;
					if (!hart_run[c])
						stall_q[c] <= 1'b0;
					else if (in_x[c] && !xc_ok)
						stall_q[c] <= 1'b1;
					else if (in_x[c])
						stall_q[c] <= 1'b0;
				end
		end
	always @(posedge clk) begin : sv2v_autoblock_5
		reg signed [31:0] c;
		for (c = 0; c < NUM_HARTS; c = c + 1)
			begin
				if (f_pop_alu[c]) begin
					func_q[c] <= cfg_func_sel[((NUM_HARTS - 1) - c) * 9+:9];
					acc_q[c] <= xc_imm[1:0];
					thr_q[c] <= cfg_threshold[((NUM_HARTS - 1) - c) * 16+:16];
				end
				if (stg_cap_a_q[c]) begin
					op_a_q[c] <= min_rd_data[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W];
					op_b_q[c] <= 1'sb0;
				end
				if (stg_cap_b_q[c])
					op_b_q[c] <= min_rd_data[((NUM_HARTS - 1) - c) * LINE_W+:LINE_W];
				if (f_flush[c]) begin
					fdest_q[c] <= xc_rs1[14:0];
					ftag_q[c] <= xc_rs1[18:15];
				end
				if (f_kick[c])
					kval_q[c] <= xc_rs1;
				if (in_x[c] && !xc_ok)
					stall_op_q[c] <= xc_funct3;
			end
	end
	reg w_from_mem;
	reg [HART_W - 1:0] w_k;
	reg [31:0] cfg_q;
	always @(posedge clk) begin
		w_from_mem <= xc_funct3 == XC_POP;
		w_k <= xc_ctx;
		(* full_case, parallel_case *)
		case (xc_imm)
			CFG_ELEM_MODE: cfg_q <= {30'd0, cfg_func_sel[(((NUM_HARTS - 1) - xc_ctx) * 9) + 8-:2]};
			CFG_CREDIT_BATCH: cfg_q <= cfg_credit_batch[((NUM_HARTS - 1) - xc_ctx) * 32+:32];
			default: cfg_q <= 32'd0;
		endcase
	end
	assign xc_rdata = (w_from_mem ? min_rd_data[((NUM_HARTS - 1) - w_k) * LINE_W+:LINE_W] : cfg_q);
	initial _sv2v_0 = 0;
endmodule
