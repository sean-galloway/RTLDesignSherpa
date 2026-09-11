module math_bf16_exp2 (
	i_bf16,
	ow_exp2,
	ow_is_zero,
	ow_is_inf,
	ow_is_nan
);
	reg _sv2v_0;
	parameter signed [31:0] LUT_DEPTH = 32;
	parameter signed [31:0] LUT_ADDR_BITS = $clog2(LUT_DEPTH);
	input wire [15:0] i_bf16;
	output wire [15:0] ow_exp2;
	output wire ow_is_zero;
	output wire ow_is_inf;
	output wire ow_is_nan;
	localparam [15:0] BF16_ONE = 16'h3f80;
	localparam [15:0] BF16_ZERO = 16'h0000;
	localparam [15:0] BF16_POS_INF = 16'h7f80;
	localparam [15:0] BF16_NAN = 16'h7fc0;
	wire w_sign;
	wire [7:0] w_exp;
	wire [6:0] w_mant;
	assign w_sign = i_bf16[15];
	assign w_exp = i_bf16[14:7];
	assign w_mant = i_bf16[6:0];
	wire w_is_zero_input;
	wire w_is_inf_input;
	wire w_is_nan_input;
	assign w_is_zero_input = w_exp == 8'd0;
	assign w_is_inf_input = (w_exp == 8'd255) && (w_mant == 7'd0);
	assign w_is_nan_input = (w_exp == 8'd255) && (w_mant != 7'd0);
	reg signed [8:0] w_int_part;
	reg [7:0] w_frac_part;
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_exp >= 8'd135) begin
			w_int_part = (w_sign ? -9'sd256 : 9'sd256);
			w_frac_part = 8'd0;
		end
		else if (w_exp >= 8'd127)
			case (w_exp - 8'd127)
				8'd0: begin
					w_int_part = (w_sign ? -9'sd1 : 9'sd1);
					w_frac_part = {w_mant, 1'b0};
				end
				8'd1: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6]})));
					w_frac_part = {w_mant[5:0], 2'b00};
				end
				8'd2: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6:5]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6:5]})));
					w_frac_part = {w_mant[4:0], 3'b000};
				end
				8'd3: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6:4]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6:4]})));
					w_frac_part = {w_mant[3:0], 4'b0000};
				end
				8'd4: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6:3]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6:3]})));
					w_frac_part = {w_mant[2:0], 5'b00000};
				end
				8'd5: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6:2]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6:2]})));
					w_frac_part = {w_mant[1:0], 6'b000000};
				end
				8'd6: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant[6:1]})) : sv2v_cast_9_signed($signed({2'b01, w_mant[6:1]})));
					w_frac_part = {w_mant[0], 7'b0000000};
				end
				8'd7: begin
					w_int_part = (w_sign ? -sv2v_cast_9_signed($signed({2'b01, w_mant})) : sv2v_cast_9_signed($signed({2'b01, w_mant})));
					w_frac_part = 8'd0;
				end
				default: begin
					w_int_part = (w_sign ? -9'sd256 : 9'sd256);
					w_frac_part = 8'd0;
				end
			endcase
		else if (w_exp == 8'd126) begin
			w_int_part = 9'sd0;
			w_frac_part = {1'b1, w_mant};
		end
		else if (w_exp == 8'd125) begin
			w_int_part = 9'sd0;
			w_frac_part = {2'b01, w_mant[6:1]};
		end
		else if (w_exp == 8'd124) begin
			w_int_part = 9'sd0;
			w_frac_part = {3'b001, w_mant[6:2]};
		end
		else if (w_exp == 8'd123) begin
			w_int_part = 9'sd0;
			w_frac_part = {4'b0001, w_mant[6:3]};
		end
		else begin
			w_int_part = 9'sd0;
			w_frac_part = 8'd0;
		end
	end
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr;
	reg [6:0] w_result_mant;
	assign w_lut_addr = w_frac_part[7:8 - LUT_ADDR_BITS];
	generate
		if (LUT_DEPTH == 32) begin : gen_lut_32
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_lut_addr)
					5'd0: w_result_mant = 7'd0;
					5'd1: w_result_mant = 7'd3;
					5'd2: w_result_mant = 7'd6;
					5'd3: w_result_mant = 7'd9;
					5'd4: w_result_mant = 7'd12;
					5'd5: w_result_mant = 7'd15;
					5'd6: w_result_mant = 7'd18;
					5'd7: w_result_mant = 7'd21;
					5'd8: w_result_mant = 7'd24;
					5'd9: w_result_mant = 7'd28;
					5'd10: w_result_mant = 7'd31;
					5'd11: w_result_mant = 7'd34;
					5'd12: w_result_mant = 7'd38;
					5'd13: w_result_mant = 7'd42;
					5'd14: w_result_mant = 7'd45;
					5'd15: w_result_mant = 7'd49;
					5'd16: w_result_mant = 7'd53;
					5'd17: w_result_mant = 7'd57;
					5'd18: w_result_mant = 7'd61;
					5'd19: w_result_mant = 7'd65;
					5'd20: w_result_mant = 7'd69;
					5'd21: w_result_mant = 7'd74;
					5'd22: w_result_mant = 7'd78;
					5'd23: w_result_mant = 7'd83;
					5'd24: w_result_mant = 7'd87;
					5'd25: w_result_mant = 7'd92;
					5'd26: w_result_mant = 7'd97;
					5'd27: w_result_mant = 7'd102;
					5'd28: w_result_mant = 7'd107;
					5'd29: w_result_mant = 7'd112;
					5'd30: w_result_mant = 7'd117;
					5'd31: w_result_mant = 7'd123;
					default: w_result_mant = 7'd0;
				endcase
			end
		end
		else if (LUT_DEPTH == 64) begin : gen_lut_64
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_lut_addr)
					6'd0: w_result_mant = 7'd0;
					6'd1: w_result_mant = 7'd1;
					6'd2: w_result_mant = 7'd3;
					6'd3: w_result_mant = 7'd4;
					6'd4: w_result_mant = 7'd6;
					6'd5: w_result_mant = 7'd7;
					6'd6: w_result_mant = 7'd9;
					6'd7: w_result_mant = 7'd10;
					6'd8: w_result_mant = 7'd12;
					6'd9: w_result_mant = 7'd13;
					6'd10: w_result_mant = 7'd15;
					6'd11: w_result_mant = 7'd16;
					6'd12: w_result_mant = 7'd18;
					6'd13: w_result_mant = 7'd19;
					6'd14: w_result_mant = 7'd21;
					6'd15: w_result_mant = 7'd23;
					6'd16: w_result_mant = 7'd24;
					6'd17: w_result_mant = 7'd26;
					6'd18: w_result_mant = 7'd28;
					6'd19: w_result_mant = 7'd29;
					6'd20: w_result_mant = 7'd31;
					6'd21: w_result_mant = 7'd33;
					6'd22: w_result_mant = 7'd34;
					6'd23: w_result_mant = 7'd36;
					6'd24: w_result_mant = 7'd38;
					6'd25: w_result_mant = 7'd40;
					6'd26: w_result_mant = 7'd42;
					6'd27: w_result_mant = 7'd43;
					6'd28: w_result_mant = 7'd45;
					6'd29: w_result_mant = 7'd47;
					6'd30: w_result_mant = 7'd49;
					6'd31: w_result_mant = 7'd51;
					6'd32: w_result_mant = 7'd53;
					6'd33: w_result_mant = 7'd55;
					6'd34: w_result_mant = 7'd57;
					6'd35: w_result_mant = 7'd59;
					6'd36: w_result_mant = 7'd61;
					6'd37: w_result_mant = 7'd63;
					6'd38: w_result_mant = 7'd65;
					6'd39: w_result_mant = 7'd67;
					6'd40: w_result_mant = 7'd69;
					6'd41: w_result_mant = 7'd72;
					6'd42: w_result_mant = 7'd74;
					6'd43: w_result_mant = 7'd76;
					6'd44: w_result_mant = 7'd78;
					6'd45: w_result_mant = 7'd80;
					6'd46: w_result_mant = 7'd83;
					6'd47: w_result_mant = 7'd85;
					6'd48: w_result_mant = 7'd87;
					6'd49: w_result_mant = 7'd90;
					6'd50: w_result_mant = 7'd92;
					6'd51: w_result_mant = 7'd94;
					6'd52: w_result_mant = 7'd97;
					6'd53: w_result_mant = 7'd99;
					6'd54: w_result_mant = 7'd102;
					6'd55: w_result_mant = 7'd104;
					6'd56: w_result_mant = 7'd107;
					6'd57: w_result_mant = 7'd109;
					6'd58: w_result_mant = 7'd112;
					6'd59: w_result_mant = 7'd115;
					6'd60: w_result_mant = 7'd117;
					6'd61: w_result_mant = 7'd120;
					6'd62: w_result_mant = 7'd123;
					6'd63: w_result_mant = 7'd125;
					default: w_result_mant = 7'd0;
				endcase
			end
		end
		else begin : gen_lut_128
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_lut_addr)
					7'd0: w_result_mant = 7'd0;
					7'd1: w_result_mant = 7'd1;
					7'd2: w_result_mant = 7'd1;
					7'd3: w_result_mant = 7'd2;
					7'd4: w_result_mant = 7'd3;
					7'd5: w_result_mant = 7'd3;
					7'd6: w_result_mant = 7'd4;
					7'd7: w_result_mant = 7'd5;
					7'd8: w_result_mant = 7'd6;
					7'd9: w_result_mant = 7'd6;
					7'd10: w_result_mant = 7'd7;
					7'd11: w_result_mant = 7'd8;
					7'd12: w_result_mant = 7'd9;
					7'd13: w_result_mant = 7'd9;
					7'd14: w_result_mant = 7'd10;
					7'd15: w_result_mant = 7'd11;
					7'd16: w_result_mant = 7'd11;
					7'd17: w_result_mant = 7'd12;
					7'd18: w_result_mant = 7'd13;
					7'd19: w_result_mant = 7'd14;
					7'd20: w_result_mant = 7'd14;
					7'd21: w_result_mant = 7'd15;
					7'd22: w_result_mant = 7'd16;
					7'd23: w_result_mant = 7'd17;
					7'd24: w_result_mant = 7'd17;
					7'd25: w_result_mant = 7'd18;
					7'd26: w_result_mant = 7'd19;
					7'd27: w_result_mant = 7'd20;
					7'd28: w_result_mant = 7'd20;
					7'd29: w_result_mant = 7'd21;
					7'd30: w_result_mant = 7'd22;
					7'd31: w_result_mant = 7'd23;
					7'd32: w_result_mant = 7'd23;
					7'd33: w_result_mant = 7'd24;
					7'd34: w_result_mant = 7'd25;
					7'd35: w_result_mant = 7'd26;
					7'd36: w_result_mant = 7'd27;
					7'd37: w_result_mant = 7'd27;
					7'd38: w_result_mant = 7'd28;
					7'd39: w_result_mant = 7'd29;
					7'd40: w_result_mant = 7'd30;
					7'd41: w_result_mant = 7'd31;
					7'd42: w_result_mant = 7'd31;
					7'd43: w_result_mant = 7'd32;
					7'd44: w_result_mant = 7'd33;
					7'd45: w_result_mant = 7'd34;
					7'd46: w_result_mant = 7'd35;
					7'd47: w_result_mant = 7'd36;
					7'd48: w_result_mant = 7'd36;
					7'd49: w_result_mant = 7'd37;
					7'd50: w_result_mant = 7'd38;
					7'd51: w_result_mant = 7'd39;
					7'd52: w_result_mant = 7'd40;
					7'd53: w_result_mant = 7'd41;
					7'd54: w_result_mant = 7'd42;
					7'd55: w_result_mant = 7'd43;
					7'd56: w_result_mant = 7'd43;
					7'd57: w_result_mant = 7'd44;
					7'd58: w_result_mant = 7'd45;
					7'd59: w_result_mant = 7'd46;
					7'd60: w_result_mant = 7'd47;
					7'd61: w_result_mant = 7'd48;
					7'd62: w_result_mant = 7'd49;
					7'd63: w_result_mant = 7'd50;
					7'd64: w_result_mant = 7'd50;
					7'd65: w_result_mant = 7'd51;
					7'd66: w_result_mant = 7'd52;
					7'd67: w_result_mant = 7'd53;
					7'd68: w_result_mant = 7'd54;
					7'd69: w_result_mant = 7'd55;
					7'd70: w_result_mant = 7'd56;
					7'd71: w_result_mant = 7'd57;
					7'd72: w_result_mant = 7'd57;
					7'd73: w_result_mant = 7'd58;
					7'd74: w_result_mant = 7'd59;
					7'd75: w_result_mant = 7'd60;
					7'd76: w_result_mant = 7'd61;
					7'd77: w_result_mant = 7'd62;
					7'd78: w_result_mant = 7'd63;
					7'd79: w_result_mant = 7'd64;
					7'd80: w_result_mant = 7'd65;
					7'd81: w_result_mant = 7'd66;
					7'd82: w_result_mant = 7'd67;
					7'd83: w_result_mant = 7'd68;
					7'd84: w_result_mant = 7'd69;
					7'd85: w_result_mant = 7'd70;
					7'd86: w_result_mant = 7'd71;
					7'd87: w_result_mant = 7'd72;
					7'd88: w_result_mant = 7'd73;
					7'd89: w_result_mant = 7'd74;
					7'd90: w_result_mant = 7'd75;
					7'd91: w_result_mant = 7'd76;
					7'd92: w_result_mant = 7'd77;
					7'd93: w_result_mant = 7'd78;
					7'd94: w_result_mant = 7'd79;
					7'd95: w_result_mant = 7'd80;
					7'd96: w_result_mant = 7'd81;
					7'd97: w_result_mant = 7'd82;
					7'd98: w_result_mant = 7'd83;
					7'd99: w_result_mant = 7'd84;
					7'd100: w_result_mant = 7'd85;
					7'd101: w_result_mant = 7'd86;
					7'd102: w_result_mant = 7'd87;
					7'd103: w_result_mant = 7'd88;
					7'd104: w_result_mant = 7'd89;
					7'd105: w_result_mant = 7'd90;
					7'd106: w_result_mant = 7'd91;
					7'd107: w_result_mant = 7'd92;
					7'd108: w_result_mant = 7'd93;
					7'd109: w_result_mant = 7'd94;
					7'd110: w_result_mant = 7'd95;
					7'd111: w_result_mant = 7'd96;
					7'd112: w_result_mant = 7'd97;
					7'd113: w_result_mant = 7'd98;
					7'd114: w_result_mant = 7'd99;
					7'd115: w_result_mant = 7'd100;
					7'd116: w_result_mant = 7'd101;
					7'd117: w_result_mant = 7'd102;
					7'd118: w_result_mant = 7'd103;
					7'd119: w_result_mant = 7'd104;
					7'd120: w_result_mant = 7'd105;
					7'd121: w_result_mant = 7'd106;
					7'd122: w_result_mant = 7'd107;
					7'd123: w_result_mant = 7'd108;
					7'd124: w_result_mant = 7'd109;
					7'd125: w_result_mant = 7'd110;
					7'd126: w_result_mant = 7'd111;
					7'd127: w_result_mant = 7'd112;
					default: w_result_mant = 7'd0;
				endcase
			end
		end
	endgenerate
	wire signed [8:0] w_adj_int_part;
	wire [7:0] w_adj_frac_part;
	wire [LUT_ADDR_BITS - 1:0] w_adj_lut_addr;
	reg [6:0] w_adj_result_mant;
	assign w_adj_int_part = (w_sign && (w_frac_part > 0) ? w_int_part - 9'sd1 : w_int_part);
	assign w_adj_frac_part = (w_sign && (w_frac_part > 0) ? 8'd0 - w_frac_part : w_frac_part);
	assign w_adj_lut_addr = w_adj_frac_part[7:8 - LUT_ADDR_BITS];
	generate
		if (LUT_DEPTH == 32) begin : gen_adj_lut_32
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_adj_lut_addr)
					5'd0: w_adj_result_mant = 7'd0;
					5'd1: w_adj_result_mant = 7'd3;
					5'd2: w_adj_result_mant = 7'd6;
					5'd3: w_adj_result_mant = 7'd9;
					5'd4: w_adj_result_mant = 7'd12;
					5'd5: w_adj_result_mant = 7'd15;
					5'd6: w_adj_result_mant = 7'd18;
					5'd7: w_adj_result_mant = 7'd21;
					5'd8: w_adj_result_mant = 7'd24;
					5'd9: w_adj_result_mant = 7'd28;
					5'd10: w_adj_result_mant = 7'd31;
					5'd11: w_adj_result_mant = 7'd34;
					5'd12: w_adj_result_mant = 7'd38;
					5'd13: w_adj_result_mant = 7'd42;
					5'd14: w_adj_result_mant = 7'd45;
					5'd15: w_adj_result_mant = 7'd49;
					5'd16: w_adj_result_mant = 7'd53;
					5'd17: w_adj_result_mant = 7'd57;
					5'd18: w_adj_result_mant = 7'd61;
					5'd19: w_adj_result_mant = 7'd65;
					5'd20: w_adj_result_mant = 7'd69;
					5'd21: w_adj_result_mant = 7'd74;
					5'd22: w_adj_result_mant = 7'd78;
					5'd23: w_adj_result_mant = 7'd83;
					5'd24: w_adj_result_mant = 7'd87;
					5'd25: w_adj_result_mant = 7'd92;
					5'd26: w_adj_result_mant = 7'd97;
					5'd27: w_adj_result_mant = 7'd102;
					5'd28: w_adj_result_mant = 7'd107;
					5'd29: w_adj_result_mant = 7'd112;
					5'd30: w_adj_result_mant = 7'd117;
					5'd31: w_adj_result_mant = 7'd123;
					default: w_adj_result_mant = 7'd0;
				endcase
			end
		end
		else if (LUT_DEPTH == 64) begin : gen_adj_lut_64
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_adj_lut_addr)
					6'd0: w_adj_result_mant = 7'd0;
					6'd1: w_adj_result_mant = 7'd1;
					6'd2: w_adj_result_mant = 7'd3;
					6'd3: w_adj_result_mant = 7'd4;
					6'd4: w_adj_result_mant = 7'd6;
					6'd5: w_adj_result_mant = 7'd7;
					6'd6: w_adj_result_mant = 7'd9;
					6'd7: w_adj_result_mant = 7'd10;
					6'd8: w_adj_result_mant = 7'd12;
					6'd9: w_adj_result_mant = 7'd13;
					6'd10: w_adj_result_mant = 7'd15;
					6'd11: w_adj_result_mant = 7'd16;
					6'd12: w_adj_result_mant = 7'd18;
					6'd13: w_adj_result_mant = 7'd19;
					6'd14: w_adj_result_mant = 7'd21;
					6'd15: w_adj_result_mant = 7'd23;
					6'd16: w_adj_result_mant = 7'd24;
					6'd17: w_adj_result_mant = 7'd26;
					6'd18: w_adj_result_mant = 7'd28;
					6'd19: w_adj_result_mant = 7'd29;
					6'd20: w_adj_result_mant = 7'd31;
					6'd21: w_adj_result_mant = 7'd33;
					6'd22: w_adj_result_mant = 7'd34;
					6'd23: w_adj_result_mant = 7'd36;
					6'd24: w_adj_result_mant = 7'd38;
					6'd25: w_adj_result_mant = 7'd40;
					6'd26: w_adj_result_mant = 7'd42;
					6'd27: w_adj_result_mant = 7'd43;
					6'd28: w_adj_result_mant = 7'd45;
					6'd29: w_adj_result_mant = 7'd47;
					6'd30: w_adj_result_mant = 7'd49;
					6'd31: w_adj_result_mant = 7'd51;
					6'd32: w_adj_result_mant = 7'd53;
					6'd33: w_adj_result_mant = 7'd55;
					6'd34: w_adj_result_mant = 7'd57;
					6'd35: w_adj_result_mant = 7'd59;
					6'd36: w_adj_result_mant = 7'd61;
					6'd37: w_adj_result_mant = 7'd63;
					6'd38: w_adj_result_mant = 7'd65;
					6'd39: w_adj_result_mant = 7'd67;
					6'd40: w_adj_result_mant = 7'd69;
					6'd41: w_adj_result_mant = 7'd72;
					6'd42: w_adj_result_mant = 7'd74;
					6'd43: w_adj_result_mant = 7'd76;
					6'd44: w_adj_result_mant = 7'd78;
					6'd45: w_adj_result_mant = 7'd80;
					6'd46: w_adj_result_mant = 7'd83;
					6'd47: w_adj_result_mant = 7'd85;
					6'd48: w_adj_result_mant = 7'd87;
					6'd49: w_adj_result_mant = 7'd90;
					6'd50: w_adj_result_mant = 7'd92;
					6'd51: w_adj_result_mant = 7'd94;
					6'd52: w_adj_result_mant = 7'd97;
					6'd53: w_adj_result_mant = 7'd99;
					6'd54: w_adj_result_mant = 7'd102;
					6'd55: w_adj_result_mant = 7'd104;
					6'd56: w_adj_result_mant = 7'd107;
					6'd57: w_adj_result_mant = 7'd109;
					6'd58: w_adj_result_mant = 7'd112;
					6'd59: w_adj_result_mant = 7'd114;
					6'd60: w_adj_result_mant = 7'd117;
					6'd61: w_adj_result_mant = 7'd120;
					6'd62: w_adj_result_mant = 7'd122;
					6'd63: w_adj_result_mant = 7'd125;
					default: w_adj_result_mant = 7'd0;
				endcase
			end
		end
		else begin : gen_adj_lut_128
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_adj_lut_addr)
					7'd0: w_adj_result_mant = 7'd0;
					7'd1: w_adj_result_mant = 7'd1;
					7'd2: w_adj_result_mant = 7'd1;
					7'd3: w_adj_result_mant = 7'd2;
					7'd4: w_adj_result_mant = 7'd3;
					7'd5: w_adj_result_mant = 7'd3;
					7'd6: w_adj_result_mant = 7'd4;
					7'd7: w_adj_result_mant = 7'd5;
					7'd8: w_adj_result_mant = 7'd6;
					7'd9: w_adj_result_mant = 7'd6;
					7'd10: w_adj_result_mant = 7'd7;
					7'd11: w_adj_result_mant = 7'd8;
					7'd12: w_adj_result_mant = 7'd9;
					7'd13: w_adj_result_mant = 7'd9;
					7'd14: w_adj_result_mant = 7'd10;
					7'd15: w_adj_result_mant = 7'd11;
					7'd16: w_adj_result_mant = 7'd11;
					7'd17: w_adj_result_mant = 7'd12;
					7'd18: w_adj_result_mant = 7'd13;
					7'd19: w_adj_result_mant = 7'd14;
					7'd20: w_adj_result_mant = 7'd14;
					7'd21: w_adj_result_mant = 7'd15;
					7'd22: w_adj_result_mant = 7'd16;
					7'd23: w_adj_result_mant = 7'd17;
					7'd24: w_adj_result_mant = 7'd17;
					7'd25: w_adj_result_mant = 7'd18;
					7'd26: w_adj_result_mant = 7'd19;
					7'd27: w_adj_result_mant = 7'd20;
					7'd28: w_adj_result_mant = 7'd20;
					7'd29: w_adj_result_mant = 7'd21;
					7'd30: w_adj_result_mant = 7'd22;
					7'd31: w_adj_result_mant = 7'd23;
					7'd32: w_adj_result_mant = 7'd23;
					7'd33: w_adj_result_mant = 7'd24;
					7'd34: w_adj_result_mant = 7'd25;
					7'd35: w_adj_result_mant = 7'd26;
					7'd36: w_adj_result_mant = 7'd27;
					7'd37: w_adj_result_mant = 7'd27;
					7'd38: w_adj_result_mant = 7'd28;
					7'd39: w_adj_result_mant = 7'd29;
					7'd40: w_adj_result_mant = 7'd30;
					7'd41: w_adj_result_mant = 7'd31;
					7'd42: w_adj_result_mant = 7'd31;
					7'd43: w_adj_result_mant = 7'd32;
					7'd44: w_adj_result_mant = 7'd33;
					7'd45: w_adj_result_mant = 7'd34;
					7'd46: w_adj_result_mant = 7'd35;
					7'd47: w_adj_result_mant = 7'd36;
					7'd48: w_adj_result_mant = 7'd36;
					7'd49: w_adj_result_mant = 7'd37;
					7'd50: w_adj_result_mant = 7'd38;
					7'd51: w_adj_result_mant = 7'd39;
					7'd52: w_adj_result_mant = 7'd40;
					7'd53: w_adj_result_mant = 7'd41;
					7'd54: w_adj_result_mant = 7'd42;
					7'd55: w_adj_result_mant = 7'd43;
					7'd56: w_adj_result_mant = 7'd43;
					7'd57: w_adj_result_mant = 7'd44;
					7'd58: w_adj_result_mant = 7'd45;
					7'd59: w_adj_result_mant = 7'd46;
					7'd60: w_adj_result_mant = 7'd47;
					7'd61: w_adj_result_mant = 7'd48;
					7'd62: w_adj_result_mant = 7'd49;
					7'd63: w_adj_result_mant = 7'd50;
					7'd64: w_adj_result_mant = 7'd50;
					7'd65: w_adj_result_mant = 7'd51;
					7'd66: w_adj_result_mant = 7'd52;
					7'd67: w_adj_result_mant = 7'd53;
					7'd68: w_adj_result_mant = 7'd54;
					7'd69: w_adj_result_mant = 7'd55;
					7'd70: w_adj_result_mant = 7'd56;
					7'd71: w_adj_result_mant = 7'd57;
					7'd72: w_adj_result_mant = 7'd57;
					7'd73: w_adj_result_mant = 7'd58;
					7'd74: w_adj_result_mant = 7'd59;
					7'd75: w_adj_result_mant = 7'd60;
					7'd76: w_adj_result_mant = 7'd61;
					7'd77: w_adj_result_mant = 7'd62;
					7'd78: w_adj_result_mant = 7'd63;
					7'd79: w_adj_result_mant = 7'd64;
					7'd80: w_adj_result_mant = 7'd65;
					7'd81: w_adj_result_mant = 7'd66;
					7'd82: w_adj_result_mant = 7'd67;
					7'd83: w_adj_result_mant = 7'd68;
					7'd84: w_adj_result_mant = 7'd69;
					7'd85: w_adj_result_mant = 7'd70;
					7'd86: w_adj_result_mant = 7'd71;
					7'd87: w_adj_result_mant = 7'd72;
					7'd88: w_adj_result_mant = 7'd73;
					7'd89: w_adj_result_mant = 7'd74;
					7'd90: w_adj_result_mant = 7'd75;
					7'd91: w_adj_result_mant = 7'd76;
					7'd92: w_adj_result_mant = 7'd77;
					7'd93: w_adj_result_mant = 7'd78;
					7'd94: w_adj_result_mant = 7'd79;
					7'd95: w_adj_result_mant = 7'd80;
					7'd96: w_adj_result_mant = 7'd81;
					7'd97: w_adj_result_mant = 7'd82;
					7'd98: w_adj_result_mant = 7'd83;
					7'd99: w_adj_result_mant = 7'd84;
					7'd100: w_adj_result_mant = 7'd85;
					7'd101: w_adj_result_mant = 7'd86;
					7'd102: w_adj_result_mant = 7'd87;
					7'd103: w_adj_result_mant = 7'd88;
					7'd104: w_adj_result_mant = 7'd89;
					7'd105: w_adj_result_mant = 7'd90;
					7'd106: w_adj_result_mant = 7'd91;
					7'd107: w_adj_result_mant = 7'd92;
					7'd108: w_adj_result_mant = 7'd93;
					7'd109: w_adj_result_mant = 7'd94;
					7'd110: w_adj_result_mant = 7'd95;
					7'd111: w_adj_result_mant = 7'd96;
					7'd112: w_adj_result_mant = 7'd97;
					7'd113: w_adj_result_mant = 7'd98;
					7'd114: w_adj_result_mant = 7'd99;
					7'd115: w_adj_result_mant = 7'd100;
					7'd116: w_adj_result_mant = 7'd101;
					7'd117: w_adj_result_mant = 7'd102;
					7'd118: w_adj_result_mant = 7'd103;
					7'd119: w_adj_result_mant = 7'd104;
					7'd120: w_adj_result_mant = 7'd105;
					7'd121: w_adj_result_mant = 7'd106;
					7'd122: w_adj_result_mant = 7'd107;
					7'd123: w_adj_result_mant = 7'd108;
					7'd124: w_adj_result_mant = 7'd109;
					7'd125: w_adj_result_mant = 7'd110;
					7'd126: w_adj_result_mant = 7'd111;
					7'd127: w_adj_result_mant = 7'd112;
					default: w_adj_result_mant = 7'd0;
				endcase
			end
		end
	endgenerate
	wire [6:0] w_final_mant;
	assign w_final_mant = (w_sign ? w_adj_result_mant : w_result_mant);
	wire signed [9:0] w_result_exp_signed;
	wire [7:0] w_result_exp;
	wire w_overflow;
	wire w_underflow;
	assign w_result_exp_signed = 10'sd127 + w_adj_int_part;
	assign w_overflow = w_result_exp_signed >= 10'sd255;
	assign w_underflow = w_result_exp_signed <= 10'sd0;
	assign w_result_exp = w_result_exp_signed[7:0];
	reg [15:0] w_result;
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_is_nan_input)
			w_result = BF16_NAN;
		else if (w_is_zero_input)
			w_result = BF16_ONE;
		else if (w_sign && w_is_inf_input)
			w_result = BF16_ZERO;
		else if (!w_sign && w_is_inf_input)
			w_result = BF16_POS_INF;
		else if (w_overflow)
			w_result = BF16_POS_INF;
		else if (w_underflow)
			w_result = BF16_ZERO;
		else
			w_result = {1'b0, w_result_exp, w_final_mant};
	end
	assign ow_exp2 = w_result;
	assign ow_is_zero = w_underflow || (w_sign && w_is_inf_input);
	assign ow_is_inf = w_overflow || (!w_sign && w_is_inf_input);
	assign ow_is_nan = w_is_nan_input;
	initial _sv2v_0 = 0;
endmodule
