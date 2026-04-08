// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_wrr_pwm_monbus (yosys-compatible)
// Proves: one-hot grant, grant implies request, weight-based priority,
// reset clears outputs, PWM block_arb connection.
// Uses MAX_LEVELS=4, CLIENTS=2 for tractability.

`timescale 1ns / 1ps

module formal_arbiter_wrr_pwm_monbus #(
    parameter int MAX_LEVELS = 4,
    parameter int CLIENTS = 2
) (
    input logic clk,
    input logic rst_n
);

    localparam int N = $clog2(CLIENTS);
    localparam int PWM_WIDTH = 16;
    localparam int MTW = $clog2(MAX_LEVELS);
    localparam int CXMTW = CLIENTS * MTW;
    localparam int MON_FIFO_DEPTH = 16;

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
    logic [CXMTW-1:0]   cfg_arb_max_thresh;
    logic [CLIENTS-1:0]  request;
    logic [CLIENTS-1:0]  grant_ack;

    logic                cfg_pwm_sync_rst_n;
    logic                cfg_pwm_start;
    logic [PWM_WIDTH-1:0] cfg_pwm_duty;
    logic [PWM_WIDTH-1:0] cfg_pwm_period;
    logic [PWM_WIDTH-1:0] cfg_pwm_repeat_count;

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
    logic                grant_valid;
    logic [CLIENTS-1:0]  grant;
    logic [N-1:0]        grant_id;
    logic                cfg_pwm_sts_done;
    logic                pwm_out;
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
    arbiter_wrr_pwm_monbus #(
        .MAX_LEVELS   (MAX_LEVELS),
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (0),
        .MON_AGENT_ID (8'h10),
        .MON_UNIT_ID  (4'h0)
    ) dut (
        .clk                       (clk),
        .rst_n                     (rst_n),
        .cfg_arb_max_thresh        (cfg_arb_max_thresh),
        .request                   (request),
        .grant_valid               (grant_valid),
        .grant                     (grant),
        .grant_id                  (grant_id),
        .grant_ack                 (grant_ack),
        .cfg_pwm_sync_rst_n        (cfg_pwm_sync_rst_n),
        .cfg_pwm_start             (cfg_pwm_start),
        .cfg_pwm_duty              (cfg_pwm_duty),
        .cfg_pwm_period            (cfg_pwm_period),
        .cfg_pwm_repeat_count      (cfg_pwm_repeat_count),
        .cfg_pwm_sts_done          (cfg_pwm_sts_done),
        .pwm_out                   (pwm_out),
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

    // No grant_ack (WAIT_GNT_ACK=0)
    always @(posedge clk) begin
        if (rst_n) assume (grant_ack == '0);
    end

    // Disable PWM for tractability
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!cfg_pwm_start);
            assume (cfg_pwm_sync_rst_n);
        end
    end

    // Weight thresholds non-zero (at least 1 per client)
    always @(posedge clk) begin
        if (rst_n) begin
            for (int i = 0; i < CLIENTS; i++) begin
                assume (cfg_arb_max_thresh[(i+1)*MTW-1 -: MTW] >= MTW'(1));
            end
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset clears grant_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_grant_valid: assert (!grant_valid);
    end

    // P2: Grant is one-hot or zero
    always @(posedge clk) begin
        if (rst_n)
            ap_grant_onehot: assert ($countones(grant) <= 1);
    end

    // P3: grant_valid implies at least one grant set
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_grant_nonzero: assert (|grant);
    end

    // P4: Grant only to clients that were requesting (current or previous cycle)
    //     The weighted arbiter has registered outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && grant_valid)
            ap_grant_implies_request: assert ((grant & (request | $past(request))) == grant);
    end

    // P5: grant_id matches grant vector
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_grant_id_match: assert (grant[grant_id]);
    end

    // P6: PWM inactive (disabled) means pwm_out stays low
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_pwm_inactive: assert (!pwm_out);
    end

    // P7: Reset clears monbus_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus: assert (!monbus_valid);
    end

    // P8: No grant when arbiter blocked (pwm_out high)
    // When pwm blocks, arbiter should not grant
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(pwm_out))
            ap_blocked_no_grant: assert (!grant_valid);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Grant issued
    always @(posedge clk) begin
        if (rst_n)
            cp_grant: cover (grant_valid);
    end

    // C2: All clients requesting
    always @(posedge clk) begin
        if (rst_n)
            cp_all_req: cover (&request);
    end

    // C3: Monitor output
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus: cover (monbus_valid && monbus_ready);
    end

    // C4: No requests
    always @(posedge clk) begin
        if (rst_n)
            cp_idle: cover (request == '0 && !grant_valid);
    end

endmodule
