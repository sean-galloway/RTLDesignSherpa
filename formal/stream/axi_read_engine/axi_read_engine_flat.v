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
	always @(posedge clk)
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
module axi_read_engine (
	clk,
	rst_n,
	cfg_axi_rd_xfer_beats,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	axi_rd_alloc_req,
	axi_rd_alloc_size,
	axi_rd_alloc_id,
	axi_rd_alloc_space_free,
	axi_rd_sram_valid,
	axi_rd_sram_ready,
	axi_rd_sram_id,
	axi_rd_sram_data,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_rvalid,
	m_axi_rready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	sched_rd_error,
	dbg_rd_all_complete,
	dbg_r_beats_rcvd,
	dbg_sram_writes,
	dbg_arb_request
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] SEG_COUNT_WIDTH = 8;
	parameter signed [31:0] PIPELINE = 0;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] STROBE_EVERY_BEAT = 0;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [NC - 1:0] sched_rd_valid;
	input wire [(NC * AW) - 1:0] sched_rd_addr;
	input wire [(NC * 32) - 1:0] sched_rd_beats;
	output wire [NC - 1:0] sched_rd_done_strobe;
	output wire [(NC * 32) - 1:0] sched_rd_beats_done;
	output wire axi_rd_alloc_req;
	output wire [7:0] axi_rd_alloc_size;
	output wire [IW - 1:0] axi_rd_alloc_id;
	input wire [(NC * SCW) - 1:0] axi_rd_alloc_space_free;
	output wire axi_rd_sram_valid;
	input wire axi_rd_sram_ready;
	output wire [IW - 1:0] axi_rd_sram_id;
	output wire [DW - 1:0] axi_rd_sram_data;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	output wire [NC - 1:0] sched_rd_error;
	output wire [NC - 1:0] dbg_rd_all_complete;
	output wire [31:0] dbg_r_beats_rcvd;
	output wire [31:0] dbg_sram_writes;
	output wire [NC - 1:0] dbg_arb_request;
	localparam signed [31:0] CW = (NC > 1 ? $clog2(NC) : 1);
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] AXSIZE = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] MOW = $clog2(AR_MAX_OUTSTANDING + 1);
	reg [NC - 1:0] r_outstanding_limit;
	reg [(NC * MOW) - 1:0] r_outstanding_count;
	wire [CW - 1:0] w_arb_grant_id;
	function automatic signed [MOW - 1:0] sv2v_cast_04DDF_signed;
		input reg signed [MOW - 1:0] inp;
		sv2v_cast_04DDF_signed = inp;
	endfunction
	generate
		if (PIPELINE == 0) begin : gen_no_pipeline_tracking
			always @(posedge clk)
				if (!rst_n)
					r_outstanding_limit <= 1'sb0;
				else begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						begin
							if ((m_axi_arvalid && m_axi_arready) && (w_arb_grant_id == i[CW - 1:0]))
								r_outstanding_limit[i] <= 1'b1;
							if (((m_axi_rvalid && m_axi_rready) && m_axi_rlast) && (m_axi_rid[CW - 1:0] == i[CW - 1:0]))
								r_outstanding_limit[i] <= 1'b0;
						end
				end
			wire [NC * MOW:1] sv2v_tmp_16AB7;
			assign sv2v_tmp_16AB7 = 1'sb0;
			always @(*) r_outstanding_count = sv2v_tmp_16AB7;
		end
		else begin : gen_pipeline_tracking
			reg [NC - 1:0] w_incr;
			reg [NC - 1:0] w_decr;
			always @(*) begin
				if (_sv2v_0)
					;
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						begin
							w_incr[i] = (m_axi_arvalid && m_axi_arready) && (w_arb_grant_id == i[CW - 1:0]);
							w_decr[i] = ((m_axi_rvalid && m_axi_rready) && m_axi_rlast) && (m_axi_rid[CW - 1:0] == i[CW - 1:0]);
						end
				end
			end
			always @(posedge clk)
				if (!rst_n)
					r_outstanding_count <= 1'sb0;
				else begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						case ({w_incr[i], w_decr[i]})
							2'b10: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW] + 1'b1;
							2'b01: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW] - 1'b1;
							default: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW];
						endcase
				end
			always @(*) begin
				if (_sv2v_0)
					;
				begin : sv2v_autoblock_4
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						r_outstanding_limit[i] = r_outstanding_count[i * MOW+:MOW] >= sv2v_cast_04DDF_signed(AR_MAX_OUTSTANDING);
				end
			end
		end
	endgenerate
	reg [NC - 1:0] r_all_complete;
	reg [NC - 1:0] r_all_complete_prev;
	always @(posedge clk)
		if (!rst_n) begin
			r_all_complete <= 1'sb1;
			r_all_complete_prev <= 1'sb1;
		end
		else begin
			r_all_complete_prev <= r_all_complete;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (r_outstanding_count[i * MOW+:MOW] == {MOW * 1 {1'sb0}})
						r_all_complete[i] <= 1'b1;
					else if (r_all_complete_prev[i] && (r_outstanding_count[i * MOW+:MOW] != {MOW * 1 {1'sb0}}))
						r_all_complete[i] <= 1'b0;
			end
		end
	assign dbg_rd_all_complete = r_all_complete;
	reg [NC - 1:0] w_space_ok;
	reg [NC - 1:0] w_below_outstanding_limit;
	reg [NC - 1:0] w_arb_request;
	reg [(NC * 8) - 1:0] w_transfer_size;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					w_transfer_size[i * 8+:8] = sv2v_cast_8((sched_rd_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_rd_xfer_beats) + 32'd1) ? sched_rd_beats[i * 32+:32] - 32'd1 : sv2v_cast_32(cfg_axi_rd_xfer_beats)));
					w_space_ok[i] = sv2v_cast_14961(axi_rd_alloc_space_free[i * SCW+:SCW]) >= sv2v_cast_14961(w_transfer_size[i * 8+:8] + 8'd1);
					w_below_outstanding_limit[i] = !r_outstanding_limit[i];
					w_arb_request[i] = (sched_rd_valid[i] && w_space_ok[i]) && w_below_outstanding_limit[i];
				end
		end
	end
	wire w_arb_grant_valid;
	wire [NC - 1:0] w_arb_grant;
	wire [NC - 1:0] w_arb_grant_ack;
	generate
		if (NC == 1) begin : gen_single_channel
			assign w_arb_grant_valid = w_arb_request[0];
			assign w_arb_grant = w_arb_request;
			assign w_arb_grant_id = 1'b0;
		end
		else begin : gen_multi_channel
			arbiter_round_robin #(
				.CLIENTS(NC),
				.WAIT_GNT_ACK(1)
			) u_arbiter(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(w_arb_request),
				.grant_ack(w_arb_grant_ack),
				.grant_valid(w_arb_grant_valid),
				.grant(w_arb_grant),
				.grant_id(w_arb_grant_id),
				.last_grant()
			);
		end
	endgenerate
	assign m_axi_arvalid = w_arb_grant_valid;
	assign m_axi_arid = {{IW - CW {1'b0}}, w_arb_grant_id};
	assign m_axi_araddr = sched_rd_addr[w_arb_grant_id * AW+:AW];
	assign m_axi_arlen = w_transfer_size[w_arb_grant_id * 8+:8];
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign m_axi_arsize = sv2v_cast_3_signed(AXSIZE);
	assign m_axi_arburst = 2'b01;
	assign w_arb_grant_ack = w_arb_grant & {NC {m_axi_arvalid && m_axi_arready}};
	reg r_alloc_req;
	reg [7:0] r_alloc_size;
	reg [IW - 1:0] r_alloc_id;
	always @(posedge clk)
		if (!rst_n) begin
			r_alloc_req <= 1'b0;
			r_alloc_size <= 1'sb0;
			r_alloc_id <= 1'sb0;
		end
		else begin
			r_alloc_req <= 1'b0;
			if (m_axi_arvalid && m_axi_arready) begin
				r_alloc_req <= 1'b1;
				r_alloc_size <= w_transfer_size[w_arb_grant_id * 8+:8] + 8'd1;
				r_alloc_id <= {{IW - CW {1'b0}}, w_arb_grant_id};
			end
		end
	assign axi_rd_alloc_req = r_alloc_req;
	assign axi_rd_alloc_size = r_alloc_size;
	assign axi_rd_alloc_id = r_alloc_id;
	assign axi_rd_sram_valid = m_axi_rvalid;
	assign axi_rd_sram_id = m_axi_rid;
	assign axi_rd_sram_data = m_axi_rdata;
	assign m_axi_rready = axi_rd_sram_ready;
	reg [NC - 1:0] r_done_strobe;
	reg [(NC * 32) - 1:0] r_beats_done;
	always @(posedge clk)
		if (!rst_n) begin
			r_done_strobe <= {NC {1'd0}};
			r_beats_done <= {NC {32'd0}};
		end
		else begin
			r_done_strobe <= {NC {1'd0}};
			if (m_axi_arvalid && m_axi_arready) begin
				r_done_strobe[w_arb_grant_id] <= 1'b1;
				r_beats_done[w_arb_grant_id * 32+:32] <= {24'd0, w_transfer_size[w_arb_grant_id * 8+:8] + 8'd1};
			end
		end
	assign sched_rd_done_strobe = r_done_strobe;
	assign sched_rd_beats_done = r_beats_done;
	reg [NC - 1:0] r_rd_error;
	always @(posedge clk)
		if (!rst_n)
			r_rd_error <= 1'sb0;
		else if ((m_axi_rvalid && m_axi_rready) && (m_axi_rresp != 2'b00)) begin : sv2v_autoblock_7
			reg [CW - 1:0] ch_id;
			ch_id = m_axi_rid[CW - 1:0];
			r_rd_error[ch_id] <= 1'b1;
		end
	assign sched_rd_error = r_rd_error;
	reg [31:0] r_r_beats_rcvd;
	reg [31:0] r_sram_writes;
	always @(posedge clk)
		if (!rst_n) begin
			r_r_beats_rcvd <= 1'sb0;
			r_sram_writes <= 1'sb0;
		end
		else begin
			if (m_axi_rvalid && m_axi_rready)
				r_r_beats_rcvd <= r_r_beats_rcvd + 1'b1;
			if (axi_rd_sram_valid && axi_rd_sram_ready)
				r_sram_writes <= r_sram_writes + 1'b1;
		end
	assign dbg_r_beats_rcvd = r_r_beats_rcvd;
	assign dbg_sram_writes = r_sram_writes;
	assign dbg_arb_request = w_arb_request;
	initial _sv2v_0 = 0;
endmodule
