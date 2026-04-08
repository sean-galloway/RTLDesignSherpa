// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_monbus_common (yosys-compatible)
// Focus: reset clears monbus_valid, FIFO count range, basic grant tracking.
// Uses CLIENTS=2, MON_FIFO_DEPTH=4 for tractability.

`timescale 1ns / 1ps

module formal_arbiter_monbus_common #(
    parameter int CLIENTS = 2,
    parameter int MON_FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst_n
);

    localparam int N = $clog2(CLIENTS);
    localparam int MAX_LEVELS = 16;
    localparam int MTW = $clog2(MAX_LEVELS);
    localparam int CXMTW = CLIENTS * MTW;
    localparam int MFCW = $clog2(MON_FIFO_DEPTH + 1);

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 1) assume (rst_n);
    end

    // =========================================================================
    // Free inputs
    // =========================================================================
    logic [CXMTW-1:0]    cfg_max_thresh;
    logic [CLIENTS-1:0]  request;
    logic                grant_valid;
    logic [CLIENTS-1:0]  grant;
    logic [N-1:0]        grant_id;
    logic [CLIENTS-1:0]  grant_ack;
    logic                block_arb;

    logic                cfg_mon_enable;
    logic [15:0]         cfg_mon_pkt_type_enable;
    logic [15:0]         cfg_mon_latency_thresh;
    logic [15:0]         cfg_mon_starvation_thresh;
    logic [15:0]         cfg_mon_fairness_thresh;
    logic [15:0]         cfg_mon_active_thresh;
    logic [15:0]         cfg_mon_ack_timeout_thresh;
    logic [15:0]         cfg_mon_efficiency_thresh;
    logic [7:0]          cfg_mon_sample_period;

    logic                monbus_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    logic                monbus_valid;
    logic [63:0]         monbus_packet;
    logic [$clog2(MON_FIFO_DEPTH):0] debug_fifo_count;
    logic [15:0]         debug_packet_count;
    logic [CLIENTS-1:0]  debug_ack_timeout;
    logic [15:0]         debug_protocol_violations;
    logic [15:0]         debug_grant_efficiency;
    logic [CLIENTS-1:0]  debug_client_starvation;
    logic [15:0]         debug_fairness_deviation;
    logic [2:0]          debug_monitor_state;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    arbiter_monbus_common #(
        .CLIENTS                 (CLIENTS),
        .WAIT_GNT_ACK            (0),
        .WEIGHTED_MODE           (0),
        .MON_AGENT_ID            (8'h10),
        .MON_UNIT_ID             (4'h0),
        .MON_FIFO_DEPTH          (MON_FIFO_DEPTH),
        .MON_FIFO_ALMOST_MARGIN  (1),
        .FAIRNESS_REPORT_CYCLES  (32),
        .MIN_GRANTS_FOR_FAIRNESS (8)
    ) dut (
        .clk                       (clk),
        .rst_n                     (rst_n),
        .cfg_max_thresh            (cfg_max_thresh),
        .request                   (request),
        .grant_valid               (grant_valid),
        .grant                     (grant),
        .grant_id                  (grant_id),
        .grant_ack                 (grant_ack),
        .block_arb                 (block_arb),
        .cfg_mon_enable            (cfg_mon_enable),
        .cfg_mon_pkt_type_enable   (cfg_mon_pkt_type_enable),
        .cfg_mon_latency_thresh    (cfg_mon_latency_thresh),
        .cfg_mon_starvation_thresh (cfg_mon_starvation_thresh),
        .cfg_mon_fairness_thresh   (cfg_mon_fairness_thresh),
        .cfg_mon_active_thresh     (cfg_mon_active_thresh),
        .cfg_mon_ack_timeout_thresh(cfg_mon_ack_timeout_thresh),
        .cfg_mon_efficiency_thresh (cfg_mon_efficiency_thresh),
        .cfg_mon_sample_period     (cfg_mon_sample_period),
        .monbus_valid              (monbus_valid),
        .monbus_ready              (monbus_ready),
        .monbus_packet             (monbus_packet),
        .debug_fifo_count          (debug_fifo_count),
        .debug_packet_count        (debug_packet_count),
        .debug_ack_timeout         (debug_ack_timeout),
        .debug_protocol_violations (debug_protocol_violations),
        .debug_grant_efficiency    (debug_grant_efficiency),
        .debug_client_starvation   (debug_client_starvation),
        .debug_fairness_deviation  (debug_fairness_deviation),
        .debug_monitor_state       (debug_monitor_state)
    );

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Grant must be one-hot or zero
    always @(posedge clk) begin
        if (rst_n) begin
            assume ($countones(grant) <= 1);
            if (grant_valid) assume (|grant);
            if (!grant_valid) assume (grant == '0);
        end
    end

    // grant_id consistent with grant vector
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            assume (grant[grant_id]);
    end

    // Grant only to requesting clients
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            assume ((grant & request) == grant);
    end

    // No grant_ack used (WAIT_GNT_ACK=0)
    always @(posedge clk) begin
        if (rst_n) assume (grant_ack == '0);
    end

    // Keep sample period small for tractability
    always @(posedge clk) begin
        if (rst_n) assume (cfg_mon_sample_period <= 8'd16);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset clears monbus_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus_valid: assert (!monbus_valid);
    end

    // P2: FIFO count in valid range [0, MON_FIFO_DEPTH]
    always @(posedge clk) begin
        if (rst_n)
            ap_fifo_count_range: assert (debug_fifo_count <= MON_FIFO_DEPTH);
    end

    // P3: After reset, FIFO count is 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fifo_empty: assert (debug_fifo_count == 0);
    end

    // P4: Monitor FSM state is valid (not illegal encoding)
    always @(posedge clk) begin
        if (rst_n)
            ap_monitor_state_valid: assert (debug_monitor_state <= 3'b101);
    end

    // P5: After reset, monitor state is MON_IDLE (000)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monitor_idle: assert (debug_monitor_state == 3'b000);
    end

    // P6: FIFO count 0 after reset (empty)
    //     Note: monbus_valid may be asserted with count==0 due to combinational
    //     read path in mux-mode FIFO, so we only check post-reset state.
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fifo_no_valid: assert (!monbus_valid && debug_fifo_count == 0);
    end

    // P7: Packet count monotonically increases (or stays same)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_packet_count_monotonic: assert (debug_packet_count >= $past(debug_packet_count));
    end

    // P8: Grant efficiency in range [0, 100]
    always @(posedge clk) begin
        if (rst_n)
            ap_efficiency_range: assert (debug_grant_efficiency <= 16'd100);
    end

    // P9: After reset, debug_packet_count is 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_packet_count: assert (debug_packet_count == 16'h0);
    end

    // P10: monbus_packet protocol field is always PROTOCOL_ARB (3'b011) when valid
    always @(posedge clk) begin
        if (rst_n && monbus_valid)
            ap_protocol_arb: assert (monbus_packet[59:57] == 3'b011);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: monbus_valid asserted (event generated)
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus_valid: cover (monbus_valid && monbus_ready);
    end

    // C2: FIFO non-empty
    always @(posedge clk) begin
        if (rst_n)
            cp_fifo_nonempty: cover (debug_fifo_count > 0);
    end

    // C3: Monitor in ACTIVE state
    always @(posedge clk) begin
        if (rst_n)
            cp_monitor_active: cover (debug_monitor_state == 3'b001);
    end

    // C4: Grant event detected
    always @(posedge clk) begin
        if (rst_n)
            cp_grant_event: cover (grant_valid && |grant && cfg_mon_enable);
    end

    // C5: Starvation detected
    always @(posedge clk) begin
        if (rst_n)
            cp_starvation: cover (|debug_client_starvation);
    end

endmodule
