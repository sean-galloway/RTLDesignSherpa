// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for axis_monitor_lite (amba/monitor-lite TASK-003).
// Free stream and monbus inputs; the checks are the block's delivery
// contract and its accounting, the covers prove every packet class it emits
// is reachable (a proof over an unreachable class is vacuous):
//   - monbus hold: a presented packet never changes or withdraws until taken
//   - protocol field is AXIS on every packet
//   - packet_count moves by exactly one, on a TLAST handshake only
//   - clear empties: no open packet, zero counters the cycle after
//   - in_packet tracks the TLAST-delimited run
//   - dropped_count only ever falls to zero (a report or a clear), never
//     partially
//   - covers: Error, Timeout, Completion, Credit, Channel, Stream packets and
//     an EVENT_DROPPED report
`default_nettype none
module formal_axis_monitor_lite (
    input logic clk,
    input logic rst_n
);
    localparam int IW    = 2;
    localparam int DESTW = 2;
    localparam int SW    = 2;      // DATA_WIDTH 16

    (* anyseq *) reg              clear;
    (* anyseq *) reg [63:0]       mon_time;
    (* anyseq *) reg              tvalid, tready, tlast;
    (* anyseq *) reg [IW-1:0]     tid;
    (* anyseq *) reg [DESTW-1:0]  tdest;
    (* anyseq *) reg [SW-1:0]     tstrb;
    (* anyseq *) reg [1:0]        cfg_freq_sel;
    (* anyseq *) reg [15:0]       cfg_timeout_cnt;
    (* anyseq *) reg [31:0]       cfg_stall_threshold;
    (* anyseq *) reg              monbus_ready;

    wire         monbus_valid;
    wire [127:0] monbus_packet;
    wire [63:0]  monbus_timestamp;
    wire         busy, in_packet;
    wire [31:0]  packet_count;
    wire [15:0]  error_count, dropped_count;

    axis_monitor_lite #(
        .DATA_WIDTH           (16),
        .ID_WIDTH             (IW),
        .DEST_WIDTH           (DESTW),
        .OUT_DEPTH            (2),
        .CFI_MIN_FREQ_MHZ     (5),
        .CFI_MAX_FREQ_MHZ     (20),
        .CFI_NUM_FREQ_ENTRIES (4)
    ) dut (
        .aclk (clk), .aresetn (rst_n), .clear (clear), .i_mon_time (mon_time),
        .axis_tvalid (tvalid), .axis_tready (tready), .axis_tlast (tlast),
        .axis_tid (tid), .axis_tdest (tdest), .axis_tstrb (tstrb),
        .cfg_freq_sel (cfg_freq_sel), .cfg_timeout_cnt (cfg_timeout_cnt),
        .cfg_error_enable (1'b1), .cfg_timeout_enable (1'b1), .cfg_compl_enable (1'b1),
        .cfg_credit_enable (1'b1), .cfg_channel_enable (1'b1), .cfg_stream_enable (1'b1),
        .cfg_strb_check_enable (1'b1), .cfg_stall_threshold (cfg_stall_threshold),
        .cfg_axis_pkt_mask (16'h0),
        .monbus_valid (monbus_valid), .monbus_ready (monbus_ready),
        .monbus_packet (monbus_packet), .monbus_timestamp (monbus_timestamp),
        .busy (busy), .in_packet (in_packet), .packet_count (packet_count),
        .error_count (error_count), .dropped_count (dropped_count)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    wire hs = tvalid && tready;

    // monbus hold: presented, not taken -> still presented, unchanged
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n) && $past(monbus_valid) && !$past(monbus_ready)) begin
        ap_hold_valid:  assert (monbus_valid);
        ap_hold_packet: assert (monbus_packet == $past(monbus_packet));
    end

    // every packet is an AXIS packet from this unit/agent
    always @(posedge clk) if (rst_n && monbus_valid) begin
        ap_protocol: assert (monbus_packet[108:105] == 4'h1);
        ap_unit:     assert (monbus_packet[71:64]  == 8'h09);
        ap_agent:    assert (monbus_packet[87:72]  == 16'h0064);
    end

    // packet_count: +1 on a TLAST handshake, else unchanged (or zero after clear)
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n)) begin
        if ($past(clear))
            ap_clear_count: assert (packet_count == 32'd0);
        else if ($past(hs && tlast))
            ap_count_inc:   assert (packet_count == $past(packet_count) + 32'd1);
        else
            ap_count_hold:  assert (packet_count == $past(packet_count));
    end

    // in_packet follows the TLAST-delimited run
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n)) begin
        if ($past(clear))          ap_clear_pkt: assert (!in_packet);
        else if ($past(hs))        ap_inpkt_hs:  assert (in_packet == !$past(tlast));
        else                       ap_inpkt_hold: assert (in_packet == $past(in_packet));
    end

    // clear empties every counter
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n) && $past(clear)) begin
        ap_clear_err:  assert (error_count == 16'd0);
        ap_clear_drop: assert (dropped_count == 16'd0);
    end

    // the drop count never falls except to zero (one report, or a clear)
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n) && (dropped_count < $past(dropped_count)))
        ap_drop_report_zeroes: assert (dropped_count == 16'd0);

    // busy is never low with a packet on the bus or a packet open
    always @(posedge clk) if (rst_n && (monbus_valid || in_packet))
        ap_busy: assert (busy);

    // covers: every packet class the block emits is reachable
    always @(posedge clk) if (rst_n && monbus_valid) begin
        cp_error:   cover (monbus_packet[127:124] == 4'h0 && monbus_packet[104:97] != 8'hE);
        cp_compl:   cover (monbus_packet[127:124] == 4'h1);
        cp_timeout: cover (monbus_packet[127:124] == 4'h3);
        cp_credit:  cover (monbus_packet[127:124] == 4'h5);
        cp_channel: cover (monbus_packet[127:124] == 4'h6);
        cp_stream:  cover (monbus_packet[127:124] == 4'h7);
        cp_dropped: cover (monbus_packet[127:124] == 4'h0 && monbus_packet[104:97] == 8'hE);
    end
endmodule
`default_nettype wire
