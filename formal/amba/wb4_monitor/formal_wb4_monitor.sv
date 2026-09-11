// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_monitor -- monitor bus output and tracking
// properties. The in-RTL `ifdef FORMAL` assertions (queue occupancy bound,
// pop only when open, orphan only when empty) ride along through sv2v
// --define=FORMAL; this file adds the port-level properties and covers.
//
// Properties verified:
//   P1: reset clears monbus_valid (skid buffer output)
//   P2: monbus_packet protocol field is WB (bits [108:105] == 4'h5) when valid
//   P3: monbus_valid held until monbus_ready
//   P4: active_count never exceeds MAX_TRANSACTIONS
//   P5: active_count follows the queue handshakes exactly (+push -pop)
//   P6: transaction_count only moves on a response handshake with something open
//
// Covers: a completion, an error, a timeout packet; two transfers open at once;
// an orphan response; the queue full (TRACK_LOST reachable).

module formal_wb4_monitor (
    input logic clk,
    input logic rst_n
);

    localparam int AW = 12;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int MAX_TRANS = 2;
    localparam int FIFO_DEPTH = 4;
    localparam logic [7:0]  UNIT_ID  = 8'h01;
    localparam logic [15:0] AGENT_ID = 16'h000B;

    (* anyseq *) reg              cmd_valid;
    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              cmd_we;
    (* anyseq *) reg [AW-1:0]     cmd_adr;
    (* anyseq *) reg [DW-1:0]     cmd_dat;
    (* anyseq *) reg [SW-1:0]     cmd_sel;
    (* anyseq *) reg [2:0]        cmd_cti;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg              rsp_ready;
    (* anyseq *) reg [1:0]        rsp_status;
    (* anyseq *) reg [DW-1:0]     rsp_dat;

    (* anyseq *) reg              cfg_error_enable;
    (* anyseq *) reg              cfg_timeout_enable;
    (* anyseq *) reg              cfg_protocol_enable;
    (* anyseq *) reg              cfg_slverr_enable;
    (* anyseq *) reg              cfg_perf_enable;
    (* anyseq *) reg              cfg_latency_enable;
    (* anyseq *) reg              cfg_throughput_enable;
    (* anyseq *) reg              cfg_debug_enable;
    (* anyseq *) reg              cfg_trans_debug_enable;
    (* anyseq *) reg [3:0]        cfg_debug_level;
    (* anyseq *) reg [15:0]       cfg_cmd_timeout_cnt;
    (* anyseq *) reg [15:0]       cfg_rsp_timeout_cnt;
    (* anyseq *) reg [31:0]       cfg_latency_threshold;
    (* anyseq *) reg [15:0]       cfg_throughput_threshold;
    (* anyseq *) reg              monbus_ready;
    (* anyseq *) reg [63:0]       i_mon_time;

    wire              monbus_valid;
    wire [127:0]      monbus_packet;
    wire [63:0]       monbus_timestamp;
    wire [7:0]        active_count;
    wire [15:0]       error_count;
    wire [31:0]       transaction_count;

    wb4_monitor #(
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .UNIT_ID            (UNIT_ID),
        .AGENT_ID           (AGENT_ID),
        .MAX_TRANSACTIONS   (MAX_TRANS),
        .MONITOR_FIFO_DEPTH (FIFO_DEPTH),
        // Proved with the hints ON: the tie-off case is strictly weaker, and
        // an unconstrained cmd_cti exercises every encoding including the
        // reserved ones.
        .USE_BURST_HINTS    (1)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .cmd_valid              (cmd_valid),
        .cmd_ready              (cmd_ready),
        .cmd_we                 (cmd_we),
        .cmd_adr                (cmd_adr),
        .cmd_dat                (cmd_dat),
        .cmd_sel                (cmd_sel),
        .cmd_cti                (cmd_cti),
        .rsp_valid              (rsp_valid),
        .rsp_ready              (rsp_ready),
        .rsp_status             (rsp_status),
        .rsp_dat                (rsp_dat),
        .cfg_error_enable       (cfg_error_enable),
        .cfg_timeout_enable     (cfg_timeout_enable),
        .cfg_protocol_enable    (cfg_protocol_enable),
        .cfg_slverr_enable      (cfg_slverr_enable),
        .cfg_perf_enable        (cfg_perf_enable),
        .cfg_latency_enable     (cfg_latency_enable),
        .cfg_throughput_enable  (cfg_throughput_enable),
        .cfg_debug_enable       (cfg_debug_enable),
        .cfg_trans_debug_enable (cfg_trans_debug_enable),
        .cfg_debug_level        (cfg_debug_level),
        .cfg_cmd_timeout_cnt    (cfg_cmd_timeout_cnt),
        .cfg_rsp_timeout_cnt    (cfg_rsp_timeout_cnt),
        .cfg_latency_threshold  (cfg_latency_threshold),
        .cfg_throughput_threshold(cfg_throughput_threshold),
        .cfg_addr_check_enable  (1'b0),
        .cfg_addr_range_enable  (1'b0),
        .cfg_addr_range_low     ({AW{1'b0}}),
        .cfg_addr_range_high    ({AW{1'b0}}),
        .i_mon_time             (i_mon_time),
        .monbus_valid           (monbus_valid),
        .monbus_ready           (monbus_ready),
        .monbus_packet          (monbus_packet),
        .monbus_timestamp       (monbus_timestamp),
        .active_count           (active_count),
        .error_count            (error_count),
        .transaction_count      (transaction_count)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    wire f_cmd_hs = cmd_valid && cmd_ready;
    wire f_rsp_hs = rsp_valid && rsp_ready;
    wire f_push   = f_cmd_hs && (active_count < MAX_TRANS);
    wire f_pop    = f_rsp_hs && (active_count != 0);

    // P1: reset clears monbus_valid
    always @(posedge clk)
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus_valid: assert (!monbus_valid);

    // P2: protocol field is WB when valid
    always @(posedge clk)
        if (rst_n && monbus_valid)
            ap_protocol_wb: assert (monbus_packet[108:105] == 4'h5);

    // P3: valid held until ready
    always @(posedge clk)
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(monbus_valid) && !$past(monbus_ready))
                ap_valid_held: assert (monbus_valid);

    // P4: occupancy bound
    always @(posedge clk)
        if (rst_n)
            ap_active_bound: assert (active_count <= MAX_TRANS);

    // P5: occupancy follows the handshakes exactly
    always @(posedge clk)
        if (f_past_valid > 1 && rst_n && $past(rst_n))
            ap_active_tracks: assert (active_count == $past(active_count) + $past(f_push) - $past(f_pop));

    // P6: transaction_count moves only on a pop, by one
    always @(posedge clk)
        if (f_past_valid > 1 && rst_n && $past(rst_n))
            ap_tc_on_pop: assert (transaction_count == $past(transaction_count) + $past(f_pop));

    // Covers
    always @(posedge clk) if (rst_n) begin
        cp_completion:  cover (monbus_valid && monbus_packet[127:124] == 4'h1);
        cp_error:       cover (monbus_valid && monbus_packet[127:124] == 4'h0);
        cp_timeout:     cover (monbus_valid && monbus_packet[127:124] == 4'h3);
        cp_two_open:    cover (active_count == MAX_TRANS);
        cp_orphan:      cover (f_rsp_hs && active_count == 0 && cfg_error_enable && cfg_protocol_enable);
        cp_overflow:    cover (f_cmd_hs && active_count == MAX_TRANS);
        cp_drained:     cover (f_past_valid > 8 && transaction_count >= 2 && active_count == 0);
    end

endmodule
