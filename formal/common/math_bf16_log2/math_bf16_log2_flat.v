module math_bf16_log2 (
	i_bf16,
	ow_log2,
	ow_is_zero,
	ow_is_inf,
	ow_is_nan,
	ow_is_neg
);
	reg _sv2v_0;
	parameter signed [31:0] LUT_DEPTH = 32;
	parameter signed [31:0] LUT_ADDR_BITS = $clog2(LUT_DEPTH);
	input wire [15:0] i_bf16;
	output wire [15:0] ow_log2;
	output wire ow_is_zero;
	output wire ow_is_inf;
	output wire ow_is_nan;
	output wire ow_is_neg;
	localparam [15:0] BF16_ZERO = 16'h0000;
	localparam [15:0] BF16_POS_INF = 16'h7f80;
	localparam [15:0] BF16_NEG_INF = 16'hff80;
	localparam [15:0] BF16_NAN = 16'h7fc0;
	wire w_sign;
	wire [7:0] w_exp;
	wire [6:0] w_mant;
	assign w_sign = i_bf16[15];
	assign w_exp = i_bf16[14:7];
	assign w_mant = i_bf16[6:0];
	wire w_is_zero_or_subnormal;
	wire w_is_inf;
	wire w_is_nan_input;
	assign w_is_zero_or_subnormal = w_exp == 8'd0;
	assign w_is_inf = (w_exp == 8'd255) && (w_mant == 7'd0);
	assign w_is_nan_input = (w_exp == 8'd255) && (w_mant != 7'd0);
	wire signed [8:0] w_int_part;
	assign w_int_part = $signed({1'b0, w_exp}) - $signed(9'd127);
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr;
	reg [7:0] w_frac_lut;
	reg [8:0] w_frac_next;
	wire [7:0] w_frac_part;
	assign w_lut_addr = w_mant[6-:LUT_ADDR_BITS];
	generate
		if (LUT_DEPTH == 32) begin : gen_lut_32
			function automatic [8:0] lut_32;
				input reg [4:0] addr;
				reg [7:0] f;
				begin
					case (addr)
						5'd0: f = 8'd0;
						5'd1: f = 8'd11;
						5'd2: f = 8'd22;
						5'd3: f = 8'd33;
						5'd4: f = 8'd44;
						5'd5: f = 8'd54;
						5'd6: f = 8'd63;
						5'd7: f = 8'd73;
						5'd8: f = 8'd82;
						5'd9: f = 8'd92;
						5'd10: f = 8'd100;
						5'd11: f = 8'd109;
						5'd12: f = 8'd118;
						5'd13: f = 8'd126;
						5'd14: f = 8'd134;
						5'd15: f = 8'd142;
						5'd16: f = 8'd150;
						5'd17: f = 8'd157;
						5'd18: f = 8'd165;
						5'd19: f = 8'd172;
						5'd20: f = 8'd179;
						5'd21: f = 8'd186;
						5'd22: f = 8'd193;
						5'd23: f = 8'd200;
						5'd24: f = 8'd207;
						5'd25: f = 8'd213;
						5'd26: f = 8'd220;
						5'd27: f = 8'd226;
						5'd28: f = 8'd232;
						5'd29: f = 8'd238;
						5'd30: f = 8'd244;
						5'd31: f = 8'd250;
						default: f = 8'd0;
					endcase
					lut_32 = {1'b0, f};
				end
			endfunction
			reg [8:0] w_lut_this_32;
			always @(*) begin
				if (_sv2v_0)
					;
				w_lut_this_32 = lut_32(w_lut_addr);
				w_frac_lut = w_lut_this_32[7:0];
				w_frac_next = (w_lut_addr == {5 {1'b1}} ? 9'd256 : lut_32(w_lut_addr + 1'b1));
			end
		end
		else if (LUT_DEPTH == 64) begin : gen_lut_64
			function automatic [8:0] lut_64;
				input reg [5:0] addr;
				reg [7:0] f;
				begin
					case (addr)
						6'd0: f = 8'd0;
						6'd1: f = 8'd6;
						6'd2: f = 8'd11;
						6'd3: f = 8'd17;
						6'd4: f = 8'd22;
						6'd5: f = 8'd28;
						6'd6: f = 8'd33;
						6'd7: f = 8'd38;
						6'd8: f = 8'd44;
						6'd9: f = 8'd49;
						6'd10: f = 8'd54;
						6'd11: f = 8'd59;
						6'd12: f = 8'd63;
						6'd13: f = 8'd68;
						6'd14: f = 8'd73;
						6'd15: f = 8'd78;
						6'd16: f = 8'd82;
						6'd17: f = 8'd87;
						6'd18: f = 8'd92;
						6'd19: f = 8'd96;
						6'd20: f = 8'd100;
						6'd21: f = 8'd105;
						6'd22: f = 8'd109;
						6'd23: f = 8'd113;
						6'd24: f = 8'd118;
						6'd25: f = 8'd122;
						6'd26: f = 8'd126;
						6'd27: f = 8'd130;
						6'd28: f = 8'd134;
						6'd29: f = 8'd138;
						6'd30: f = 8'd142;
						6'd31: f = 8'd146;
						6'd32: f = 8'd150;
						6'd33: f = 8'd154;
						6'd34: f = 8'd157;
						6'd35: f = 8'd161;
						6'd36: f = 8'd165;
						6'd37: f = 8'd169;
						6'd38: f = 8'd172;
						6'd39: f = 8'd176;
						6'd40: f = 8'd179;
						6'd41: f = 8'd183;
						6'd42: f = 8'd186;
						6'd43: f = 8'd190;
						6'd44: f = 8'd193;
						6'd45: f = 8'd197;
						6'd46: f = 8'd200;
						6'd47: f = 8'd203;
						6'd48: f = 8'd207;
						6'd49: f = 8'd210;
						6'd50: f = 8'd213;
						6'd51: f = 8'd216;
						6'd52: f = 8'd220;
						6'd53: f = 8'd223;
						6'd54: f = 8'd226;
						6'd55: f = 8'd229;
						6'd56: f = 8'd232;
						6'd57: f = 8'd235;
						6'd58: f = 8'd238;
						6'd59: f = 8'd241;
						6'd60: f = 8'd244;
						6'd61: f = 8'd247;
						6'd62: f = 8'd250;
						6'd63: f = 8'd253;
						default: f = 8'd0;
					endcase
					lut_64 = {1'b0, f};
				end
			endfunction
			reg [8:0] w_lut_this_64;
			always @(*) begin
				if (_sv2v_0)
					;
				w_lut_this_64 = lut_64(w_lut_addr);
				w_frac_lut = w_lut_this_64[7:0];
				w_frac_next = (w_lut_addr == {6 {1'b1}} ? 9'd256 : lut_64(w_lut_addr + 1'b1));
			end
		end
		else begin : gen_lut_128
			function automatic [8:0] lut_128;
				input reg [6:0] addr;
				reg [7:0] f;
				begin
					case (addr)
						7'd0: f = 8'd0;
						7'd1: f = 8'd3;
						7'd2: f = 8'd6;
						7'd3: f = 8'd9;
						7'd4: f = 8'd11;
						7'd5: f = 8'd14;
						7'd6: f = 8'd17;
						7'd7: f = 8'd20;
						7'd8: f = 8'd22;
						7'd9: f = 8'd25;
						7'd10: f = 8'd28;
						7'd11: f = 8'd30;
						7'd12: f = 8'd33;
						7'd13: f = 8'd36;
						7'd14: f = 8'd38;
						7'd15: f = 8'd41;
						7'd16: f = 8'd44;
						7'd17: f = 8'd46;
						7'd18: f = 8'd49;
						7'd19: f = 8'd51;
						7'd20: f = 8'd54;
						7'd21: f = 8'd56;
						7'd22: f = 8'd59;
						7'd23: f = 8'd61;
						7'd24: f = 8'd63;
						7'd25: f = 8'd66;
						7'd26: f = 8'd68;
						7'd27: f = 8'd71;
						7'd28: f = 8'd73;
						7'd29: f = 8'd75;
						7'd30: f = 8'd78;
						7'd31: f = 8'd80;
						7'd32: f = 8'd82;
						7'd33: f = 8'd85;
						7'd34: f = 8'd87;
						7'd35: f = 8'd89;
						7'd36: f = 8'd92;
						7'd37: f = 8'd94;
						7'd38: f = 8'd96;
						7'd39: f = 8'd98;
						7'd40: f = 8'd100;
						7'd41: f = 8'd103;
						7'd42: f = 8'd105;
						7'd43: f = 8'd107;
						7'd44: f = 8'd109;
						7'd45: f = 8'd111;
						7'd46: f = 8'd113;
						7'd47: f = 8'd116;
						7'd48: f = 8'd118;
						7'd49: f = 8'd120;
						7'd50: f = 8'd122;
						7'd51: f = 8'd124;
						7'd52: f = 8'd126;
						7'd53: f = 8'd128;
						7'd54: f = 8'd130;
						7'd55: f = 8'd132;
						7'd56: f = 8'd134;
						7'd57: f = 8'd136;
						7'd58: f = 8'd138;
						7'd59: f = 8'd140;
						7'd60: f = 8'd142;
						7'd61: f = 8'd144;
						7'd62: f = 8'd146;
						7'd63: f = 8'd148;
						7'd64: f = 8'd150;
						7'd65: f = 8'd152;
						7'd66: f = 8'd154;
						7'd67: f = 8'd155;
						7'd68: f = 8'd157;
						7'd69: f = 8'd159;
						7'd70: f = 8'd161;
						7'd71: f = 8'd163;
						7'd72: f = 8'd165;
						7'd73: f = 8'd167;
						7'd74: f = 8'd169;
						7'd75: f = 8'd170;
						7'd76: f = 8'd172;
						7'd77: f = 8'd174;
						7'd78: f = 8'd176;
						7'd79: f = 8'd178;
						7'd80: f = 8'd179;
						7'd81: f = 8'd181;
						7'd82: f = 8'd183;
						7'd83: f = 8'd185;
						7'd84: f = 8'd186;
						7'd85: f = 8'd188;
						7'd86: f = 8'd190;
						7'd87: f = 8'd192;
						7'd88: f = 8'd193;
						7'd89: f = 8'd195;
						7'd90: f = 8'd197;
						7'd91: f = 8'd198;
						7'd92: f = 8'd200;
						7'd93: f = 8'd202;
						7'd94: f = 8'd203;
						7'd95: f = 8'd205;
						7'd96: f = 8'd207;
						7'd97: f = 8'd208;
						7'd98: f = 8'd210;
						7'd99: f = 8'd212;
						7'd100: f = 8'd213;
						7'd101: f = 8'd215;
						7'd102: f = 8'd216;
						7'd103: f = 8'd218;
						7'd104: f = 8'd220;
						7'd105: f = 8'd221;
						7'd106: f = 8'd223;
						7'd107: f = 8'd224;
						7'd108: f = 8'd226;
						7'd109: f = 8'd228;
						7'd110: f = 8'd229;
						7'd111: f = 8'd231;
						7'd112: f = 8'd232;
						7'd113: f = 8'd234;
						7'd114: f = 8'd235;
						7'd115: f = 8'd237;
						7'd116: f = 8'd238;
						7'd117: f = 8'd240;
						7'd118: f = 8'd241;
						7'd119: f = 8'd243;
						7'd120: f = 8'd244;
						7'd121: f = 8'd246;
						7'd122: f = 8'd247;
						7'd123: f = 8'd249;
						7'd124: f = 8'd250;
						7'd125: f = 8'd252;
						7'd126: f = 8'd253;
						7'd127: f = 8'd255;
						default: f = 8'd0;
					endcase
					lut_128 = {1'b0, f};
				end
			endfunction
			reg [8:0] w_lut_this_128;
			always @(*) begin
				if (_sv2v_0)
					;
				w_lut_this_128 = lut_128(w_lut_addr);
				w_frac_lut = w_lut_this_128[7:0];
				w_frac_next = (w_lut_addr == {7 {1'b1}} ? 9'd256 : lut_128(w_lut_addr + 1'b1));
			end
		end
	endgenerate
	reg [15:0] w_result;
	wire [7:0] w_abs_int;
	wire [7:0] w_adj_int;
	wire [7:0] w_adj_frac;
	assign w_abs_int = (w_int_part < 0 ? -w_int_part[7:0] : 8'd0);
	function automatic signed [15:0] sv2v_cast_16_signed;
		input reg signed [15:0] inp;
		sv2v_cast_16_signed = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	generate
		if (LUT_ADDR_BITS >= 7) begin : gen_no_interp
			assign w_frac_part = w_frac_lut;
		end
		else begin : gen_interp
			localparam signed [31:0] FRAC_BITS = 7 - LUT_ADDR_BITS;
			localparam signed [31:0] FRAC_HALF = 1 << (FRAC_BITS - 1);
			wire [FRAC_BITS - 1:0] w_sub;
			assign w_sub = w_mant[FRAC_BITS - 1:0];
			wire [8:0] w_step;
			wire [15:0] w_scaled;
			assign w_step = w_frac_next - {1'b0, w_frac_lut};
			assign w_scaled = ({{9 - FRAC_BITS {1'b0}}, w_sub} * w_step) + sv2v_cast_16_signed(FRAC_HALF);
			assign w_frac_part = w_frac_lut + sv2v_cast_8(w_scaled >> FRAC_BITS);
		end
	endgenerate
	assign w_adj_int = (w_frac_part > 0 ? w_abs_int - 8'd1 : w_abs_int);
	assign w_adj_frac = (w_frac_part > 0 ? 8'd0 - w_frac_part : 8'd0);
	always @(*) begin
		if (_sv2v_0)
			;
		if ((w_int_part == 0) && (w_frac_part == 0))
			w_result = BF16_ZERO;
		else if (w_int_part >= 0) begin
			if (w_int_part >= 64)
				w_result = {9'h085, w_int_part[5:0], w_frac_part[7]};
			else if (w_int_part >= 32)
				w_result = {9'h084, w_int_part[4:0], w_frac_part[7:6]};
			else if (w_int_part >= 16)
				w_result = {9'h083, w_int_part[3:0], w_frac_part[7:5]};
			else if (w_int_part >= 8)
				w_result = {9'h082, w_int_part[2:0], w_frac_part[7:4]};
			else if (w_int_part >= 4)
				w_result = {9'h081, w_int_part[1:0], w_frac_part[7:3]};
			else if (w_int_part >= 2)
				w_result = {9'h080, w_int_part[0], w_frac_part[7:2]};
			else if (w_int_part >= 1)
				w_result = {9'h07f, w_frac_part[7:1]};
			else if (w_frac_part >= 128)
				w_result = {9'h07e, w_frac_part[6:0]};
			else if (w_frac_part >= 64)
				w_result = {9'h07d, w_frac_part[5:0], 1'b0};
			else if (w_frac_part >= 32)
				w_result = {9'h07c, w_frac_part[4:0], 2'b00};
			else if (w_frac_part >= 16)
				w_result = {9'h07b, w_frac_part[3:0], 3'b000};
			else if (w_frac_part >= 8)
				w_result = {9'h07a, w_frac_part[2:0], 4'b0000};
			else if (w_frac_part >= 4)
				w_result = {9'h079, w_frac_part[1:0], 5'b00000};
			else if (w_frac_part >= 2)
				w_result = {9'h078, w_frac_part[0], 6'b000000};
			else
				w_result = 16'h3b80;
		end
		else if (w_adj_int >= 64)
			w_result = {9'h185, w_adj_int[5:0], w_adj_frac[7]};
		else if (w_adj_int >= 32)
			w_result = {9'h184, w_adj_int[4:0], w_adj_frac[7:6]};
		else if (w_adj_int >= 16)
			w_result = {9'h183, w_adj_int[3:0], w_adj_frac[7:5]};
		else if (w_adj_int >= 8)
			w_result = {9'h182, w_adj_int[2:0], w_adj_frac[7:4]};
		else if (w_adj_int >= 4)
			w_result = {9'h181, w_adj_int[1:0], w_adj_frac[7:3]};
		else if (w_adj_int >= 2)
			w_result = {9'h180, w_adj_int[0], w_adj_frac[7:2]};
		else if (w_adj_int >= 1)
			w_result = {9'h17f, w_adj_frac[7:1]};
		else if (w_adj_frac >= 128)
			w_result = {9'h17e, w_adj_frac[6:0]};
		else if (w_adj_frac >= 64)
			w_result = {9'h17d, w_adj_frac[5:0], 1'b0};
		else if (w_adj_frac >= 32)
			w_result = {9'h17c, w_adj_frac[4:0], 2'b00};
		else if (w_adj_frac >= 16)
			w_result = {9'h17b, w_adj_frac[3:0], 3'b000};
		else if (w_adj_frac >= 8)
			w_result = {9'h17a, w_adj_frac[2:0], 4'b0000};
		else if (w_adj_frac >= 4)
			w_result = {9'h179, w_adj_frac[1:0], 5'b00000};
		else if (w_adj_frac >= 2)
			w_result = {9'h178, w_adj_frac[0], 6'b000000};
		else
			w_result = 16'hbb80;
	end
	assign ow_is_zero = w_is_zero_or_subnormal;
	assign ow_is_inf = w_is_inf;
	assign ow_is_nan = w_is_nan_input || w_sign;
	assign ow_is_neg = w_sign && !w_is_nan_input;
	assign ow_log2 = (w_is_nan_input ? BF16_NAN : (w_sign ? BF16_NAN : (w_is_zero_or_subnormal ? BF16_NEG_INF : (w_is_inf ? BF16_POS_INF : w_result))));
	initial _sv2v_0 = 0;
endmodule
