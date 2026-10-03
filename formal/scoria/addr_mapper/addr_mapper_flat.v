module scoria_addr_mapper (
	axi_addr_i,
	bank_lsb_i,
	hash_en_i,
	hash_seed_i,
	rank_o,
	bank_o,
	row_o,
	col_o
);
	reg _sv2v_0;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] NUM_RANKS = 1;
	parameter signed [31:0] NUM_BANKS = 8;
	parameter signed [31:0] ROW_WIDTH = 14;
	parameter signed [31:0] COL_WIDTH = 10;
	parameter signed [31:0] BYTE_OFFSET_WIDTH = 3;
	input wire [AXI_ADDR_WIDTH - 1:0] axi_addr_i;
	input wire [4:0] bank_lsb_i;
	input wire hash_en_i;
	input wire [7:0] hash_seed_i;
	output wire [$clog2((NUM_RANKS > 1 ? NUM_RANKS : 2)) - 1:0] rank_o;
	output wire [$clog2(NUM_BANKS) - 1:0] bank_o;
	output wire [ROW_WIDTH - 1:0] row_o;
	output wire [COL_WIDTH - 1:0] col_o;
	localparam signed [31:0] AW = AXI_ADDR_WIDTH;
	localparam signed [31:0] RW = ROW_WIDTH;
	localparam signed [31:0] CW = COL_WIDTH;
	localparam signed [31:0] BW = (NUM_BANKS > 1 ? $clog2(NUM_BANKS) : 1);
	localparam signed [31:0] KW = (NUM_RANKS > 1 ? $clog2(NUM_RANKS) : 1);
	localparam signed [31:0] BO = BYTE_OFFSET_WIDTH;
	wire [31:0] w_word;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign w_word = sv2v_cast_32(axi_addr_i[AW - 1:BO]);
	reg [5:0] w_blsb;
	function automatic signed [5:0] sv2v_cast_6_signed;
		input reg signed [5:0] inp;
		sv2v_cast_6_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_blsb = ({1'b0, bank_lsb_i} > sv2v_cast_6_signed(CW) ? sv2v_cast_6_signed(CW) : {1'b0, bank_lsb_i});
	end
	wire [31:0] w_col_lo;
	wire [31:0] w_col_hi;
	wire [31:0] w_row32;
	wire [31:0] w_rank32;
	wire [31:0] w_bank32;
	assign w_col_lo = w_word & ((32'd1 << w_blsb) - 32'd1);
	assign w_bank32 = (w_word >> w_blsb) & ((32'd1 << BW) - 32'd1);
	assign w_col_hi = (w_word >> (w_blsb + sv2v_cast_6_signed(BW))) & ((32'd1 << (sv2v_cast_6_signed(CW) - w_blsb)) - 32'd1);
	assign w_row32 = (w_word >> (sv2v_cast_6_signed(CW) + sv2v_cast_6_signed(BW))) & ((32'd1 << RW) - 32'd1);
	assign w_rank32 = (NUM_RANKS > 1 ? (w_word >> ((sv2v_cast_6_signed(CW) + sv2v_cast_6_signed(BW)) + sv2v_cast_6_signed(RW))) & ((32'd1 << KW) - 32'd1) : 32'd0);
	wire [CW - 1:0] w_col;
	function automatic [CW - 1:0] sv2v_cast_3D2D3;
		input reg [CW - 1:0] inp;
		sv2v_cast_3D2D3 = inp;
	endfunction
	assign w_col = sv2v_cast_3D2D3(w_col_lo | (w_col_hi << w_blsb));
	wire [RW - 1:0] w_row;
	wire [BW - 1:0] w_bank_raw;
	wire [BW - 1:0] w_bank_hashed;
	wire [BW - 1:0] w_bank;
	function automatic [RW - 1:0] sv2v_cast_301C2;
		input reg [RW - 1:0] inp;
		sv2v_cast_301C2 = inp;
	endfunction
	assign w_row = sv2v_cast_301C2(w_row32);
	function automatic [BW - 1:0] sv2v_cast_F35F2;
		input reg [BW - 1:0] inp;
		sv2v_cast_F35F2 = inp;
	endfunction
	assign w_bank_raw = sv2v_cast_F35F2(w_bank32);
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < BW; _gv_i_1 = _gv_i_1 + 1) begin : g_hash
			localparam i = _gv_i_1;
			localparam signed [31:0] MID = ((i + BW) < RW ? i + BW : RW - 1);
			assign w_bank_hashed[i] = ((w_bank_raw[i] ^ w_row[i]) ^ w_row[MID]) ^ hash_seed_i[i];
		end
	endgenerate
	assign w_bank = (hash_en_i ? w_bank_hashed : w_bank_raw);
	assign col_o = w_col;
	assign bank_o = w_bank;
	assign row_o = w_row;
	assign rank_o = (NUM_RANKS > 1 ? w_rank32[$clog2((NUM_RANKS > 1 ? NUM_RANKS : 2)) - 1:0] : {$clog2((NUM_RANKS > 1 ? NUM_RANKS : 2)) {1'sb0}});
	initial _sv2v_0 = 0;
endmodule
