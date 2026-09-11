module math_bf16_fast_reciprocal (
	i_bf16,
	ow_reciprocal,
	ow_is_zero,
	ow_is_inf,
	ow_is_nan,
	ow_underflow,
	ow_mant_approx,
	ow_mant_interp
);
	reg _sv2v_0;
	parameter signed [31:0] LUT_DEPTH = 32;
	parameter signed [31:0] LUT_ADDR_BITS = $clog2(LUT_DEPTH);
	input wire [15:0] i_bf16;
	output reg [15:0] ow_reciprocal;
	output wire ow_is_zero;
	output wire ow_is_inf;
	output wire ow_is_nan;
	output wire ow_underflow;
	output wire [6:0] ow_mant_approx;
	output wire [6:0] ow_mant_interp;
	wire w_sign;
	wire [7:0] w_exp;
	wire [6:0] w_mant;
	assign w_sign = i_bf16[15];
	assign w_exp = i_bf16[14:7];
	assign w_mant = i_bf16[6:0];
	wire w_is_zero_or_subnormal;
	wire w_is_inf;
	wire w_is_nan;
	assign w_is_zero_or_subnormal = w_exp == 8'd0;
	assign w_is_inf = (w_exp == 8'd255) && (w_mant == 7'd0);
	assign w_is_nan = (w_exp == 8'd255) && (w_mant != 7'd0);
	reg [6:0] w_recip_mant_lut;
	reg [6:0] w_recip_mant_nxt;
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr;
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr_nxt;
	assign w_lut_addr = w_mant[6-:LUT_ADDR_BITS];
	assign w_lut_addr_nxt = (w_lut_addr == {LUT_ADDR_BITS {1'b1}} ? w_lut_addr : w_lut_addr + 1'b1);
	generate
		if (LUT_DEPTH == 32) begin : gen_lut_32
			function automatic [6:0] lut_32;
				input reg [4:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						5'd0: lut = 7'd127;
						5'd1: lut = 7'd120;
						5'd2: lut = 7'd113;
						5'd3: lut = 7'd107;
						5'd4: lut = 7'd100;
						5'd5: lut = 7'd94;
						5'd6: lut = 7'd88;
						5'd7: lut = 7'd83;
						5'd8: lut = 7'd78;
						5'd9: lut = 7'd73;
						5'd10: lut = 7'd68;
						5'd11: lut = 7'd64;
						5'd12: lut = 7'd59;
						5'd13: lut = 7'd55;
						5'd14: lut = 7'd51;
						5'd15: lut = 7'd47;
						5'd16: lut = 7'd43;
						5'd17: lut = 7'd40;
						5'd18: lut = 7'd36;
						5'd19: lut = 7'd33;
						5'd20: lut = 7'd30;
						5'd21: lut = 7'd27;
						5'd22: lut = 7'd24;
						5'd23: lut = 7'd21;
						5'd24: lut = 7'd18;
						5'd25: lut = 7'd16;
						5'd26: lut = 7'd13;
						5'd27: lut = 7'd11;
						5'd28: lut = 7'd8;
						5'd29: lut = 7'd6;
						5'd30: lut = 7'd4;
						5'd31: lut = 7'd2;
					endcase
					lut_32 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_32(w_lut_addr);
				w_recip_mant_nxt = lut_32(w_lut_addr_nxt);
			end
		end
		else if (LUT_DEPTH == 64) begin : gen_lut_64
			function automatic [6:0] lut_64;
				input reg [5:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						6'd0: lut = 7'd127;
						6'd1: lut = 7'd123;
						6'd2: lut = 7'd120;
						6'd3: lut = 7'd117;
						6'd4: lut = 7'd113;
						6'd5: lut = 7'd110;
						6'd6: lut = 7'd107;
						6'd7: lut = 7'd104;
						6'd8: lut = 7'd100;
						6'd9: lut = 7'd97;
						6'd10: lut = 7'd94;
						6'd11: lut = 7'd91;
						6'd12: lut = 7'd88;
						6'd13: lut = 7'd86;
						6'd14: lut = 7'd83;
						6'd15: lut = 7'd80;
						6'd16: lut = 7'd78;
						6'd17: lut = 7'd75;
						6'd18: lut = 7'd73;
						6'd19: lut = 7'd70;
						6'd20: lut = 7'd68;
						6'd21: lut = 7'd66;
						6'd22: lut = 7'd64;
						6'd23: lut = 7'd61;
						6'd24: lut = 7'd59;
						6'd25: lut = 7'd57;
						6'd26: lut = 7'd55;
						6'd27: lut = 7'd53;
						6'd28: lut = 7'd51;
						6'd29: lut = 7'd49;
						6'd30: lut = 7'd47;
						6'd31: lut = 7'd46;
						6'd32: lut = 7'd44;
						6'd33: lut = 7'd42;
						6'd34: lut = 7'd40;
						6'd35: lut = 7'd39;
						6'd36: lut = 7'd37;
						6'd37: lut = 7'd35;
						6'd38: lut = 7'd34;
						6'd39: lut = 7'd32;
						6'd40: lut = 7'd31;
						6'd41: lut = 7'd29;
						6'd42: lut = 7'd28;
						6'd43: lut = 7'd26;
						6'd44: lut = 7'd25;
						6'd45: lut = 7'd23;
						6'd46: lut = 7'd22;
						6'd47: lut = 7'd21;
						6'd48: lut = 7'd19;
						6'd49: lut = 7'd18;
						6'd50: lut = 7'd17;
						6'd51: lut = 7'd15;
						6'd52: lut = 7'd14;
						6'd53: lut = 7'd13;
						6'd54: lut = 7'd12;
						6'd55: lut = 7'd10;
						6'd56: lut = 7'd9;
						6'd57: lut = 7'd8;
						6'd58: lut = 7'd7;
						6'd59: lut = 7'd6;
						6'd60: lut = 7'd5;
						6'd61: lut = 7'd4;
						6'd62: lut = 7'd3;
						6'd63: lut = 7'd2;
					endcase
					lut_64 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_64(w_lut_addr);
				w_recip_mant_nxt = lut_64(w_lut_addr_nxt);
			end
		end
		else begin : gen_lut_128
			function automatic [6:0] lut_128;
				input reg [6:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						7'd0: lut = 7'd127;
						7'd1: lut = 7'd126;
						7'd2: lut = 7'd124;
						7'd3: lut = 7'd122;
						7'd4: lut = 7'd120;
						7'd5: lut = 7'd118;
						7'd6: lut = 7'd117;
						7'd7: lut = 7'd115;
						7'd8: lut = 7'd113;
						7'd9: lut = 7'd111;
						7'd10: lut = 7'd109;
						7'd11: lut = 7'd108;
						7'd12: lut = 7'd106;
						7'd13: lut = 7'd104;
						7'd14: lut = 7'd103;
						7'd15: lut = 7'd101;
						7'd16: lut = 7'd100;
						7'd17: lut = 7'd98;
						7'd18: lut = 7'd96;
						7'd19: lut = 7'd95;
						7'd20: lut = 7'd93;
						7'd21: lut = 7'd92;
						7'd22: lut = 7'd90;
						7'd23: lut = 7'd89;
						7'd24: lut = 7'd88;
						7'd25: lut = 7'd86;
						7'd26: lut = 7'd85;
						7'd27: lut = 7'd83;
						7'd28: lut = 7'd82;
						7'd29: lut = 7'd81;
						7'd30: lut = 7'd79;
						7'd31: lut = 7'd78;
						7'd32: lut = 7'd77;
						7'd33: lut = 7'd76;
						7'd34: lut = 7'd74;
						7'd35: lut = 7'd73;
						7'd36: lut = 7'd72;
						7'd37: lut = 7'd71;
						7'd38: lut = 7'd69;
						7'd39: lut = 7'd68;
						7'd40: lut = 7'd67;
						7'd41: lut = 7'd66;
						7'd42: lut = 7'd65;
						7'd43: lut = 7'd64;
						7'd44: lut = 7'd63;
						7'd45: lut = 7'd61;
						7'd46: lut = 7'd60;
						7'd47: lut = 7'd59;
						7'd48: lut = 7'd58;
						7'd49: lut = 7'd57;
						7'd50: lut = 7'd56;
						7'd51: lut = 7'd55;
						7'd52: lut = 7'd54;
						7'd53: lut = 7'd53;
						7'd54: lut = 7'd52;
						7'd55: lut = 7'd51;
						7'd56: lut = 7'd50;
						7'd57: lut = 7'd49;
						7'd58: lut = 7'd48;
						7'd59: lut = 7'd47;
						7'd60: lut = 7'd46;
						7'd61: lut = 7'd45;
						7'd62: lut = 7'd44;
						7'd63: lut = 7'd44;
						7'd64: lut = 7'd43;
						7'd65: lut = 7'd42;
						7'd66: lut = 7'd41;
						7'd67: lut = 7'd40;
						7'd68: lut = 7'd39;
						7'd69: lut = 7'd38;
						7'd70: lut = 7'd37;
						7'd71: lut = 7'd37;
						7'd72: lut = 7'd36;
						7'd73: lut = 7'd35;
						7'd74: lut = 7'd34;
						7'd75: lut = 7'd33;
						7'd76: lut = 7'd33;
						7'd77: lut = 7'd32;
						7'd78: lut = 7'd31;
						7'd79: lut = 7'd30;
						7'd80: lut = 7'd30;
						7'd81: lut = 7'd29;
						7'd82: lut = 7'd28;
						7'd83: lut = 7'd27;
						7'd84: lut = 7'd27;
						7'd85: lut = 7'd26;
						7'd86: lut = 7'd25;
						7'd87: lut = 7'd24;
						7'd88: lut = 7'd24;
						7'd89: lut = 7'd23;
						7'd90: lut = 7'd22;
						7'd91: lut = 7'd22;
						7'd92: lut = 7'd21;
						7'd93: lut = 7'd20;
						7'd94: lut = 7'd20;
						7'd95: lut = 7'd19;
						7'd96: lut = 7'd18;
						7'd97: lut = 7'd18;
						7'd98: lut = 7'd17;
						7'd99: lut = 7'd16;
						7'd100: lut = 7'd16;
						7'd101: lut = 7'd15;
						7'd102: lut = 7'd14;
						7'd103: lut = 7'd14;
						7'd104: lut = 7'd13;
						7'd105: lut = 7'd13;
						7'd106: lut = 7'd12;
						7'd107: lut = 7'd11;
						7'd108: lut = 7'd11;
						7'd109: lut = 7'd10;
						7'd110: lut = 7'd10;
						7'd111: lut = 7'd9;
						7'd112: lut = 7'd9;
						7'd113: lut = 7'd8;
						7'd114: lut = 7'd7;
						7'd115: lut = 7'd7;
						7'd116: lut = 7'd6;
						7'd117: lut = 7'd6;
						7'd118: lut = 7'd5;
						7'd119: lut = 7'd5;
						7'd120: lut = 7'd4;
						7'd121: lut = 7'd4;
						7'd122: lut = 7'd3;
						7'd123: lut = 7'd3;
						7'd124: lut = 7'd2;
						7'd125: lut = 7'd2;
						7'd126: lut = 7'd1;
						7'd127: lut = 7'd1;
					endcase
					lut_128 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_128(w_lut_addr);
				w_recip_mant_nxt = lut_128(w_lut_addr_nxt);
			end
		end
	endgenerate
	wire [7:0] w_recip_exp;
	wire w_mant_nonzero;
	wire w_recip_underflow;
	assign w_mant_nonzero = w_mant != 7'd0;
	assign w_recip_underflow = (w_mant_nonzero ? w_exp > 8'd253 : w_exp > 8'd254);
	assign w_recip_exp = (w_recip_underflow ? 8'd0 : (w_mant_nonzero ? 8'd253 - w_exp : 8'd254 - w_exp));
	wire [6:0] w_recip_mant;
	assign w_recip_mant = (w_mant_nonzero ? w_recip_mant_lut : 7'd0);
	localparam [15:0] BF16_POS_INF = 16'h7f80;
	localparam [15:0] BF16_NEG_INF = 16'hff80;
	localparam [15:0] BF16_POS_ZERO = 16'h0000;
	localparam [15:0] BF16_NEG_ZERO = 16'h8000;
	localparam [15:0] BF16_QNAN = 16'h7fc0;
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_is_nan)
			ow_reciprocal = BF16_QNAN;
		else if (w_is_inf)
			ow_reciprocal = (w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO);
		else if (w_is_zero_or_subnormal)
			ow_reciprocal = (w_sign ? BF16_NEG_INF : BF16_POS_INF);
		else if (w_recip_underflow)
			ow_reciprocal = (w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO);
		else
			ow_reciprocal = {w_sign, w_recip_exp, w_recip_mant};
	end
	assign ow_is_zero = w_is_zero_or_subnormal;
	assign ow_is_inf = w_is_inf;
	assign ow_is_nan = w_is_nan;
	assign ow_underflow = w_recip_underflow;
	function automatic signed [13:0] sv2v_cast_14_signed;
		input reg signed [13:0] inp;
		sv2v_cast_14_signed = inp;
	endfunction
	function automatic [6:0] sv2v_cast_7;
		input reg [6:0] inp;
		sv2v_cast_7 = inp;
	endfunction
	generate
		if (LUT_ADDR_BITS >= 7) begin : gen_no_interp
			assign ow_mant_interp = w_recip_mant;
		end
		else begin : gen_interp
			localparam signed [31:0] FRAC_BITS = 7 - LUT_ADDR_BITS;
			localparam signed [31:0] FRAC_HALF = 1 << (FRAC_BITS - 1);
			wire [FRAC_BITS - 1:0] w_frac;
			assign w_frac = w_mant[FRAC_BITS - 1:0];
			wire [6:0] w_step;
			assign w_step = w_recip_mant_lut - w_recip_mant_nxt;
			wire [13:0] w_scaled;
			assign w_scaled = ({{7 - FRAC_BITS {1'b0}}, w_frac} * w_step) + sv2v_cast_14_signed(FRAC_HALF);
			assign ow_mant_interp = w_recip_mant - sv2v_cast_7(w_scaled >> FRAC_BITS);
		end
	endgenerate
	assign ow_mant_approx = w_recip_mant;
	initial _sv2v_0 = 0;
endmodule
