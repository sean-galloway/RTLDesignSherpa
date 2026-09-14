module arbiter_priority_encoder (
	requests_masked,
	requests_unmasked,
	any_masked_requests,
	winner,
	winner_valid
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire [CLIENTS - 1:0] requests_masked;
	input wire [CLIENTS - 1:0] requests_unmasked;
	input wire any_masked_requests;
	output reg [N - 1:0] winner;
	output reg winner_valid;
	wire [CLIENTS - 1:0] w_priority_requests;
	assign w_priority_requests = (any_masked_requests ? requests_masked : requests_unmasked);
	generate
		if (CLIENTS == 4) begin : gen_pe_4
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					4'bzzz1: begin
						winner = 2'd0;
						winner_valid = 1'b1;
					end
					4'bzz10: begin
						winner = 2'd1;
						winner_valid = 1'b1;
					end
					4'bz100: begin
						winner = 2'd2;
						winner_valid = 1'b1;
					end
					4'b1000: begin
						winner = 2'd3;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 2'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 8) begin : gen_pe_8
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					8'bzzzzzzz1: begin
						winner = 3'd0;
						winner_valid = 1'b1;
					end
					8'bzzzzzz10: begin
						winner = 3'd1;
						winner_valid = 1'b1;
					end
					8'bzzzzz100: begin
						winner = 3'd2;
						winner_valid = 1'b1;
					end
					8'bzzzz1000: begin
						winner = 3'd3;
						winner_valid = 1'b1;
					end
					8'bzzz10000: begin
						winner = 3'd4;
						winner_valid = 1'b1;
					end
					8'bzz100000: begin
						winner = 3'd5;
						winner_valid = 1'b1;
					end
					8'bz1000000: begin
						winner = 3'd6;
						winner_valid = 1'b1;
					end
					8'b10000000: begin
						winner = 3'd7;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 3'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 16) begin : gen_pe_16
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					16'bzzzzzzzzzzzzzzz1: begin
						winner = 4'd0;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzzzz10: begin
						winner = 4'd1;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzzz100: begin
						winner = 4'd2;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzz1000: begin
						winner = 4'd3;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzz10000: begin
						winner = 4'd4;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzz100000: begin
						winner = 4'd5;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzz1000000: begin
						winner = 4'd6;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzz10000000: begin
						winner = 4'd7;
						winner_valid = 1'b1;
					end
					16'bzzzzzzz100000000: begin
						winner = 4'd8;
						winner_valid = 1'b1;
					end
					16'bzzzzzz1000000000: begin
						winner = 4'd9;
						winner_valid = 1'b1;
					end
					16'bzzzzz10000000000: begin
						winner = 4'd10;
						winner_valid = 1'b1;
					end
					16'bzzzz100000000000: begin
						winner = 4'd11;
						winner_valid = 1'b1;
					end
					16'bzzz1000000000000: begin
						winner = 4'd12;
						winner_valid = 1'b1;
					end
					16'bzz10000000000000: begin
						winner = 4'd13;
						winner_valid = 1'b1;
					end
					16'bz100000000000000: begin
						winner = 4'd14;
						winner_valid = 1'b1;
					end
					16'b1000000000000000: begin
						winner = 4'd15;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 4'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 32) begin : gen_pe_32
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz1: begin
						winner = 5'd0;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz10: begin
						winner = 5'd1;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzz100: begin
						winner = 5'd2;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzz1000: begin
						winner = 5'd3;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzz10000: begin
						winner = 5'd4;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzz100000: begin
						winner = 5'd5;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzz1000000: begin
						winner = 5'd6;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzz10000000: begin
						winner = 5'd7;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzz100000000: begin
						winner = 5'd8;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzz1000000000: begin
						winner = 5'd9;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzz10000000000: begin
						winner = 5'd10;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzz100000000000: begin
						winner = 5'd11;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzz1000000000000: begin
						winner = 5'd12;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzz10000000000000: begin
						winner = 5'd13;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzz100000000000000: begin
						winner = 5'd14;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzz1000000000000000: begin
						winner = 5'd15;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzz10000000000000000: begin
						winner = 5'd16;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzz100000000000000000: begin
						winner = 5'd17;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzz1000000000000000000: begin
						winner = 5'd18;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzz10000000000000000000: begin
						winner = 5'd19;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzz100000000000000000000: begin
						winner = 5'd20;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzz1000000000000000000000: begin
						winner = 5'd21;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzz10000000000000000000000: begin
						winner = 5'd22;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzz100000000000000000000000: begin
						winner = 5'd23;
						winner_valid = 1'b1;
					end
					32'bzzzzzzz1000000000000000000000000: begin
						winner = 5'd24;
						winner_valid = 1'b1;
					end
					32'bzzzzzz10000000000000000000000000: begin
						winner = 5'd25;
						winner_valid = 1'b1;
					end
					32'bzzzzz100000000000000000000000000: begin
						winner = 5'd26;
						winner_valid = 1'b1;
					end
					32'bzzzz1000000000000000000000000000: begin
						winner = 5'd27;
						winner_valid = 1'b1;
					end
					32'bzzz10000000000000000000000000000: begin
						winner = 5'd28;
						winner_valid = 1'b1;
					end
					32'bzz100000000000000000000000000000: begin
						winner = 5'd29;
						winner_valid = 1'b1;
					end
					32'bz1000000000000000000000000000000: begin
						winner = 5'd30;
						winner_valid = 1'b1;
					end
					32'b10000000000000000000000000000000: begin
						winner = 5'd31;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 5'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else begin : gen_pe_generic
			always @(*) begin
				if (_sv2v_0)
					;
				winner = 1'sb0;
				winner_valid = 1'b0;
				begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (w_priority_requests[i] && !winner_valid) begin
							winner = i[N - 1:0];
							winner_valid = 1'b1;
						end
				end
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module arbiter_round_robin (
	clk,
	rst_n,
	block_arb,
	request,
	grant_ack,
	grant_valid,
	grant,
	grant_id,
	last_grant
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] WAIT_GNT_ACK = 0;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire clk;
	input wire rst_n;
	input wire block_arb;
	input wire [CLIENTS - 1:0] request;
	input wire [CLIENTS - 1:0] grant_ack;
	output reg grant_valid;
	output reg [CLIENTS - 1:0] grant;
	output reg [N - 1:0] grant_id;
	output reg [CLIENTS - 1:0] last_grant;
	wire [CLIENTS - 1:0] w_mask_decode [0:CLIENTS - 1];
	wire [CLIENTS - 1:0] w_win_mask_decode [0:CLIENTS - 1];
	genvar _gv_i_1;
	function automatic signed [CLIENTS - 1:0] sv2v_cast_6D6F8_signed;
		input reg signed [CLIENTS - 1:0] inp;
		sv2v_cast_6D6F8_signed = inp;
	endfunction
	generate
		for (_gv_i_1 = 0; _gv_i_1 < CLIENTS; _gv_i_1 = _gv_i_1 + 1) begin : gen_mask_lut
			localparam i = _gv_i_1;
			assign w_mask_decode[i] = (sv2v_cast_6D6F8_signed(1) << i) - sv2v_cast_6D6F8_signed(1);
			assign w_win_mask_decode[i] = ~((sv2v_cast_6D6F8_signed(1) << (i + 1)) - sv2v_cast_6D6F8_signed(1));
		end
	endgenerate
	reg [N - 1:0] r_last_grant_id;
	reg r_last_valid;
	reg r_pending_ack;
	reg [N - 1:0] r_pending_client;
	wire [CLIENTS - 1:0] w_requests_gated;
	wire [CLIENTS - 1:0] w_requests_masked;
	wire [CLIENTS - 1:0] w_requests_unmasked;
	wire w_any_requests;
	wire w_any_masked_requests;
	wire [CLIENTS - 1:0] w_curr_mask_decode;
	assign w_requests_gated = (block_arb ? {CLIENTS {1'sb0}} : request);
	assign w_any_requests = |w_requests_gated;
	assign w_curr_mask_decode = (grant_valid ? w_win_mask_decode[grant_id] : (r_last_valid ? w_win_mask_decode[r_last_grant_id] : sv2v_cast_6D6F8_signed(1)));
	assign w_requests_masked = w_requests_gated & w_curr_mask_decode;
	assign w_requests_unmasked = w_requests_gated;
	assign w_any_masked_requests = |w_requests_masked;
	wire [N - 1:0] w_winner;
	wire w_winner_valid;
	arbiter_priority_encoder #(
		.CLIENTS(CLIENTS),
		.N(N)
	) u_priority_encoder(
		.requests_masked(w_requests_masked),
		.requests_unmasked(w_requests_unmasked),
		.any_masked_requests(w_any_masked_requests),
		.winner(w_winner),
		.winner_valid(w_winner_valid)
	);
	wire w_ack_received;
	wire w_can_grant;
	wire [CLIENTS - 1:0] w_other_requests;
	generate
		if (WAIT_GNT_ACK == 1) begin : gen_ack_optimized
			assign w_ack_received = r_pending_ack && grant_ack[r_pending_client];
			assign w_other_requests = w_requests_gated & ~(sv2v_cast_6D6F8_signed(1) << r_pending_client);
			assign w_can_grant = !r_pending_ack || w_ack_received;
		end
		else begin : gen_no_ack_optimized
			assign w_ack_received = 1'b0;
			assign w_can_grant = 1'b1;
			assign w_other_requests = 1'sb0;
		end
	endgenerate
	wire w_should_grant;
	reg [CLIENTS - 1:0] w_next_grant;
	reg [N - 1:0] w_next_grant_id;
	wire w_next_grant_valid;
	assign w_should_grant = (w_winner_valid && w_any_requests) && w_can_grant;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_grant = 1'sb0;
		w_next_grant_id = 1'sb0;
		if (w_should_grant) begin
			w_next_grant[w_winner] = 1'b1;
			w_next_grant_id = w_winner;
		end
	end
	assign w_next_grant_valid = w_should_grant;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			grant <= 1'sb0;
			grant_id <= 1'sb0;
			grant_valid <= 1'b0;
			last_grant <= 1'sb0;
			r_last_grant_id <= 1'sb0;
			r_last_valid <= 1'sb0;
			r_pending_ack <= 1'b0;
			r_pending_client <= 1'sb0;
		end
		else begin
			r_last_valid <= grant_valid;
			if (WAIT_GNT_ACK == 0) begin
				grant <= w_next_grant;
				grant_id <= w_next_grant_id;
				grant_valid <= w_next_grant_valid;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
			end
			else if (grant_valid == 1'b0) begin
				grant <= w_next_grant;
				grant_id <= w_next_grant_id;
				grant_valid <= w_next_grant_valid;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
				if (w_next_grant_valid) begin
					r_pending_ack <= 1'b1;
					r_pending_client <= w_next_grant_id;
				end
			end
			else if ((grant_valid == 1'b1) && !w_ack_received)
				;
			else if (((grant_valid == 1'b1) && w_ack_received) && (w_other_requests == {CLIENTS {1'sb0}})) begin
				grant <= 1'sb0;
				grant_id <= 1'sb0;
				grant_valid <= 1'b0;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
				r_pending_ack <= 1'b0;
				r_pending_client <= 1'sb0;
			end
			else if (((grant_valid == 1'b1) && w_ack_received) && (w_other_requests != {CLIENTS {1'sb0}})) begin
				if (w_next_grant_valid) begin
					grant <= w_next_grant;
					grant_id <= w_next_grant_id;
					grant_valid <= w_next_grant_valid;
					last_grant <= grant;
					r_last_grant_id <= grant_id;
					r_pending_ack <= 1'b1;
					r_pending_client <= w_next_grant_id;
				end
				else begin
					grant <= 1'sb0;
					grant_id <= 1'sb0;
					grant_valid <= 1'b0;
					r_pending_ack <= 1'b0;
					r_pending_client <= 1'sb0;
				end
			end
		end
	initial _sv2v_0 = 0;
endmodule
module ioapic_deliv_merge (
	clk,
	rst_n,
	src_valid,
	src_vector,
	src_dest,
	src_dest_mode,
	src_deliv_mode,
	src_ready,
	src_retry,
	m_valid,
	m_vector,
	m_dest,
	m_dest_mode,
	m_deliv_mode,
	m_src_id,
	m_ready,
	m_retry
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_SRC = 2;
	parameter signed [31:0] SRC_IDX_W = (NUM_SRC > 1 ? $clog2(NUM_SRC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [NUM_SRC - 1:0] src_valid;
	input wire [(NUM_SRC * 8) - 1:0] src_vector;
	input wire [(NUM_SRC * 8) - 1:0] src_dest;
	input wire [NUM_SRC - 1:0] src_dest_mode;
	input wire [(NUM_SRC * 3) - 1:0] src_deliv_mode;
	output reg [NUM_SRC - 1:0] src_ready;
	output reg [NUM_SRC - 1:0] src_retry;
	output wire m_valid;
	output wire [7:0] m_vector;
	output wire [7:0] m_dest;
	output wire m_dest_mode;
	output wire [2:0] m_deliv_mode;
	output wire [SRC_IDX_W - 1:0] m_src_id;
	input wire m_ready;
	input wire m_retry;
	wire [NUM_SRC - 1:0] w_grant;
	reg [NUM_SRC - 1:0] w_grant_ack;
	wire [SRC_IDX_W - 1:0] w_grant_id;
	wire w_grant_valid;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NUM_SRC; i = i + 1)
				w_grant_ack[i] = (w_grant[i] && src_valid[i]) && m_ready;
		end
	end
	arbiter_round_robin #(
		.CLIENTS(NUM_SRC),
		.WAIT_GNT_ACK(1)
	) u_arb(
		.clk(clk),
		.rst_n(rst_n),
		.block_arb(1'b0),
		.request(src_valid),
		.grant_ack(w_grant_ack),
		.grant_valid(w_grant_valid),
		.grant(w_grant),
		.grant_id(w_grant_id),
		.last_grant()
	);
	assign m_valid = w_grant_valid;
	assign m_vector = src_vector[((NUM_SRC - 1) - w_grant_id) * 8+:8];
	assign m_dest = src_dest[((NUM_SRC - 1) - w_grant_id) * 8+:8];
	assign m_dest_mode = src_dest_mode[w_grant_id];
	assign m_deliv_mode = src_deliv_mode[((NUM_SRC - 1) - w_grant_id) * 3+:3];
	assign m_src_id = w_grant_id;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < NUM_SRC; i = i + 1)
				begin
					src_ready[i] = w_grant[i] && m_ready;
					src_retry[i] = (w_grant[i] && m_ready) && m_retry;
				end
		end
	end
	initial begin : param_check
		if (NUM_SRC < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.sv:179:13 - ioapic_deliv_merge.param_check.<unnamed_block>\n msg: ", $time, "ioapic_deliv_merge: NUM_SRC must be >= 2 (got %0d); a single IOAPIC needs no merge", NUM_SRC);
		if (NUM_SRC > 16)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.sv:181:13 - ioapic_deliv_merge.param_check.<unnamed_block>\n msg: ", $time, "ioapic_deliv_merge: NUM_SRC must be <= 16 (got %0d)", NUM_SRC);
	end
	initial _sv2v_0 = 0;
endmodule
