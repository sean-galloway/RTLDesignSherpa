module scheduler_beats (
	clk,
	rst_n,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	scheduler_idle,
	scheduler_state,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_error,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_wr_valid,
	sched_wr_ready,
	sched_wr_addr,
	sched_wr_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_wr_done_strobe,
	sched_wr_beats_done,
	sched_rd_error,
	sched_wr_error,
	sched_error,
	mon_valid,
	mon_ready,
	mon_packet
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter [7:0] MON_AGENT_ID = 8'h40;
	parameter [3:0] MON_UNIT_ID = 4'h1;
	parameter [5:0] MON_CHANNEL_ID = 6'h00;
	parameter signed [31:0] DESC_WIDTH = 256;
	input wire clk;
	input wire rst_n;
	input wire cfg_channel_enable;
	input wire cfg_channel_reset;
	input wire [15:0] cfg_sched_timeout_cycles;
	input wire cfg_sched_timeout_enable;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	input wire descriptor_valid;
	output wire descriptor_ready;
	input wire [DESC_WIDTH - 1:0] descriptor_packet;
	input wire descriptor_error;
	output wire sched_rd_valid;
	output wire [ADDR_WIDTH - 1:0] sched_rd_addr;
	output wire [31:0] sched_rd_beats;
	output wire sched_wr_valid;
	input wire sched_wr_ready;
	output wire [ADDR_WIDTH - 1:0] sched_wr_addr;
	output wire [31:0] sched_wr_beats;
	input wire sched_rd_done_strobe;
	input wire [31:0] sched_rd_beats_done;
	input wire sched_wr_done_strobe;
	input wire [31:0] sched_wr_beats_done;
	input wire sched_rd_error;
	input wire sched_wr_error;
	output wire sched_error;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
	initial if (DESC_WIDTH != 256) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/rapids/rtl/fub_beats/scheduler_beats.sv:137:13 - scheduler_beats.<unnamed_block>.<unnamed_block>\n msg: ", $time, "scheduler (RAPIDS): DESC_WIDTH must be 256, got %0d.", DESC_WIDTH);
		$finish(1);
	end
	localparam signed [31:0] DESC_SRC_ADDR_LO = 0;
	localparam signed [31:0] DESC_SRC_ADDR_HI = 63;
	localparam signed [31:0] DESC_DST_ADDR_LO = 64;
	localparam signed [31:0] DESC_DST_ADDR_HI = 127;
	localparam signed [31:0] DESC_LENGTH_LO = 128;
	localparam signed [31:0] DESC_LENGTH_HI = 159;
	localparam signed [31:0] DESC_NEXT_PTR_LO = 160;
	localparam signed [31:0] DESC_NEXT_PTR_HI = 191;
	localparam signed [31:0] DESC_VALID_BIT = 192;
	localparam signed [31:0] DESC_GEN_IRQ = 193;
	localparam signed [31:0] DESC_LAST = 194;
	wire w_pkt_error;
	reg w_pkt_last;
	reg w_pkt_gen_irq;
	reg w_pkt_valid;
	reg [31:0] w_pkt_next_descriptor_ptr;
	reg [31:0] w_pkt_length;
	reg [63:0] w_pkt_dst_addr;
	reg [63:0] w_pkt_src_addr;
	reg [6:0] r_current_state;
	reg [6:0] w_next_state;
	wire w_state_idle = r_current_state == 7'b0000001;
	wire w_state_fetch_desc = r_current_state == 7'b0000010;
	wire w_state_xfer_data = r_current_state == 7'b0000100;
	wire w_state_complete = r_current_state == 7'b0001000;
	wire w_state_next_desc = r_current_state == 7'b0010000;
	wire w_state_error = r_current_state == 7'b0100000;
	reg r_channel_reset_active;
	reg [271:0] r_descriptor;
	reg r_descriptor_loaded;
	reg [ADDR_WIDTH - 1:0] r_src_addr;
	reg [ADDR_WIDTH - 1:0] r_dst_addr;
	reg [31:0] r_beats_remaining;
	reg [31:0] r_read_beats_remaining;
	reg [31:0] r_write_beats_remaining;
	reg [31:0] r_timeout_counter;
	wire w_timeout_expired;
	reg r_read_error_sticky;
	reg r_write_error_sticky;
	reg r_descriptor_error;
	reg r_mon_valid;
	reg [63:0] r_mon_packet;
	wire w_read_complete;
	wire w_write_complete;
	wire w_transfer_complete;
	always @(posedge clk)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	always @(posedge clk)
		if (!rst_n)
			r_current_state <= 7'b0000001;
		else
			r_current_state <= w_next_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		if (r_channel_reset_active)
			w_next_state = 7'b0000001;
		else if (((((descriptor_error || sched_rd_error) || sched_wr_error) || r_read_error_sticky) || r_write_error_sticky) || w_timeout_expired)
			w_next_state = 7'b0100000;
		else
			case (r_current_state)
				7'b0000001:
					if (descriptor_valid && cfg_channel_enable)
						w_next_state = 7'b0000010;
				7'b0000010:
					if (r_descriptor[192])
						w_next_state = 7'b0000100;
					else
						w_next_state = 7'b0100000;
				7'b0000100:
					if (w_transfer_complete && sched_wr_ready)
						w_next_state = 7'b0001000;
				7'b0001000:
					if ((r_descriptor[191-:32] != 32'h00000000) && !r_descriptor[194])
						w_next_state = 7'b0010000;
					else
						w_next_state = 7'b0000001;
				7'b0010000:
					if (descriptor_valid)
						w_next_state = 7'b0000010;
				7'b0100000: w_next_state = 7'b0100000;
				default: w_next_state = 7'b0100000;
			endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_pkt_last = r_descriptor[194];
		w_pkt_gen_irq = r_descriptor[193];
		w_pkt_valid = r_descriptor[192];
		w_pkt_next_descriptor_ptr = r_descriptor[191-:32];
		w_pkt_length = r_descriptor[159-:32];
		w_pkt_dst_addr = r_descriptor[127-:64];
		w_pkt_src_addr = r_descriptor[63-:64];
	end
	function automatic [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5;
		input reg [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5 = inp;
	endfunction
	always @(posedge clk)
		if (!rst_n) begin
			r_descriptor <= 1'sb0;
			r_descriptor_loaded <= 1'b0;
			r_src_addr <= 64'h0000000000000000;
			r_dst_addr <= 64'h0000000000000000;
			r_beats_remaining <= 32'h00000000;
			r_read_beats_remaining <= 32'h00000000;
			r_write_beats_remaining <= 32'h00000000;
		end
		else begin
			if ((((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) && descriptor_valid) && descriptor_ready) begin
				r_descriptor[63-:64] <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
				r_descriptor[127-:64] <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
				r_descriptor[159-:32] <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor_loaded <= 1'b1;
			end
			case (r_current_state)
				7'b0000010: begin
					r_src_addr <= r_descriptor[63-:64];
					r_dst_addr <= r_descriptor[127-:64];
					r_beats_remaining <= r_descriptor[159-:32];
					r_read_beats_remaining <= r_descriptor[159-:32];
					r_write_beats_remaining <= r_descriptor[159-:32];
				end
				7'b0000100: begin
					if (sched_rd_done_strobe) begin
						r_read_beats_remaining <= (r_read_beats_remaining >= sched_rd_beats_done ? r_read_beats_remaining - sched_rd_beats_done : 32'h00000000);
						r_src_addr <= r_src_addr + (sv2v_cast_A5DC5(sched_rd_beats_done) << $clog2(DATA_WIDTH / 8));
					end
					if (sched_wr_done_strobe) begin
						r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done ? r_write_beats_remaining - sched_wr_beats_done : 32'h00000000);
						r_dst_addr <= r_dst_addr + (sv2v_cast_A5DC5(sched_wr_beats_done) << $clog2(DATA_WIDTH / 8));
					end
				end
				7'b0001000: r_descriptor_loaded <= 1'b0;
				default:
					;
			endcase
			if (r_channel_reset_active) begin
				r_descriptor_loaded <= 1'b0;
				r_read_beats_remaining <= 32'h00000000;
				r_write_beats_remaining <= 32'h00000000;
			end
		end
	assign w_read_complete = r_read_beats_remaining == 32'h00000000;
	assign w_write_complete = r_write_beats_remaining == 32'h00000000;
	assign w_transfer_complete = w_read_complete && w_write_complete;
	wire w_sched_rd_completing_this_cycle;
	wire w_sched_wr_completing_this_cycle;
	assign w_sched_rd_completing_this_cycle = sched_rd_done_strobe && (r_read_beats_remaining <= sched_rd_beats_done);
	assign w_sched_wr_completing_this_cycle = sched_wr_done_strobe && (r_write_beats_remaining <= sched_wr_beats_done);
	assign sched_rd_valid = ((r_current_state == 7'b0000100) && !w_read_complete) && !w_sched_rd_completing_this_cycle;
	assign sched_rd_addr = r_src_addr;
	assign sched_rd_beats = r_read_beats_remaining;
	assign sched_wr_valid = ((r_current_state == 7'b0000100) && !w_write_complete) && !w_sched_wr_completing_this_cycle;
	assign sched_wr_addr = r_dst_addr;
	assign sched_wr_beats = r_write_beats_remaining;
	assign descriptor_ready = (r_current_state == 7'b0000001) || (r_current_state == 7'b0010000);
	always @(posedge clk)
		if (!rst_n) begin
			r_timeout_counter <= 32'h00000000;
			r_read_error_sticky <= 1'b0;
			r_write_error_sticky <= 1'b0;
			r_descriptor_error <= 1'b0;
		end
		else begin
			if (sched_wr_valid && !sched_wr_ready)
				r_timeout_counter <= r_timeout_counter + 1;
			else
				r_timeout_counter <= 32'h00000000;
			if (descriptor_error)
				r_descriptor_error <= 1'b1;
			if (sched_rd_error)
				r_read_error_sticky <= 1'b1;
			if (sched_wr_error)
				r_write_error_sticky <= 1'b1;
			if ((sched_rd_error || sched_wr_error) || w_timeout_expired)
				r_descriptor_error <= 1'b1;
			if (r_current_state == 7'b0000001) begin
				r_read_error_sticky <= 1'b0;
				r_write_error_sticky <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	assign w_timeout_expired = cfg_sched_timeout_enable && (r_timeout_counter >= {16'h0000, cfg_sched_timeout_cycles});
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [63:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [2:0] protocol;
		input reg [3:0] event_code;
		input reg [5:0] channel_id;
		input reg [3:0] unit_id;
		input reg [7:0] agent_id;
		input reg [34:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
	endfunction
	localparam [3:0] rapids_pkg_RAPIDS_EVENT_DESC_COMPLETE = 4'h1;
	localparam [3:0] rapids_pkg_RAPIDS_EVENT_DESC_START = 4'h0;
	localparam [3:0] rapids_pkg_RAPIDS_EVENT_ERROR = 4'hf;
	localparam [3:0] rapids_pkg_RAPIDS_EVENT_IRQ = 4'h7;
	always @(posedge clk)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
			case (r_current_state)
				7'b0000010: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, rapids_pkg_RAPIDS_EVENT_DESC_START, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
				end
				7'b0000100:
					;
				7'b0001000: begin
					r_mon_valid <= 1'b1;
					if (r_descriptor[193])
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, rapids_pkg_RAPIDS_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
					else
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, rapids_pkg_RAPIDS_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
				end
				7'b0100000: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 3'b100, rapids_pkg_RAPIDS_EVENT_ERROR, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {r_write_error_sticky, r_read_error_sticky, 33'h000000000});
				end
				default:
					;
			endcase
		end
	assign scheduler_idle = ((r_current_state == 7'b0000001) || (r_current_state == 7'b0100000)) && !r_channel_reset_active;
	assign scheduler_state = r_current_state;
	assign sched_error = w_state_error;
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	initial _sv2v_0 = 0;
endmodule
