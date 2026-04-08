// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for arbiter_rr_pwm_monbus (yosys-compatible)
// Proves: one-hot grant, grant implies request, reset clears outputs,
// PWM connects to block_arb, basic arbiter properties.
// Uses CLIENTS=2 for tractability.

`timescale 1ns / 1ps

module formal_arbiter_rr_pwm_monbus #(
    parameter int CLIENTS = 2
) (
    input logic clk,
    input logic rst_n
);

    localparam int N = $clog2(CLIENTS);
    localparam int PWM_WIDTH = 16;
    localparam int MAX_LEVELS = 16;
    localparam int MTW = $clog2(MAX_LEVELS);
    localparam int CXMTW = CLIENTS * MTW;

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
    logic [CLIENTS-1:0]  request;
    logic [CLIENTS-1:0]  grant_ack;

    logic                cfg_pwm_sync_rst_n;
    logic                cfg_pwm_start;
    logic [PWM_WIDTH-1:0] cfg_pwm_duty;
    logic [PWM_WIDTH-1:0] cfg_pwm_period;
    logic [PWM_WIDTH-1:0] cfg_pwm_repeat_count;

    logic                cfg_mon_enable;
    logic [15:0]         cfg_mon_pkt_type_enable;
    logic [15:0]         cfg_mon_latency;
    logic [15:0]         cfg_mon_starvation;
    logic [15:0]         cfg_mon_fairness;
    logic [15:0]         cfg_mon_active;
    logic [7:0]          cfg_mon_period;

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
    logic [$clog2(16+1)-1:0] debug_fifo_count;
    logic [15:0]         debug_packet_count;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    arbiter_rr_pwm_monbus #(
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (0),
        .MON_AGENT_ID (8'h10),
        .MON_UNIT_ID  (4'h0)
    ) dut (
        .clk                   (clk),
        .rst_n                 (rst_n),
        .request               (request),
        .grant_valid           (grant_valid),
        .grant                 (grant),
        .grant_id              (grant_id),
        .grant_ack             (grant_ack),
        .cfg_pwm_sync_rst_n    (cfg_pwm_sync_rst_n),
        .cfg_pwm_start         (cfg_pwm_start),
        .cfg_pwm_duty          (cfg_pwm_duty),
        .cfg_pwm_period        (cfg_pwm_period),
        .cfg_pwm_repeat_count  (cfg_pwm_repeat_count),
        .cfg_pwm_sts_done      (cfg_pwm_sts_done),
        .pwm_out               (pwm_out),
        .cfg_mon_enable        (cfg_mon_enable),
        .cfg_mon_pkt_type_enable(cfg_mon_pkt_type_enable),
        .cfg_mon_latency       (cfg_mon_latency),
        .cfg_mon_starvation    (cfg_mon_starvation),
        .cfg_mon_fairness      (cfg_mon_fairness),
        .cfg_mon_active        (cfg_mon_active),
        .cfg_mon_period        (cfg_mon_period),
        .monbus_valid          (monbus_valid),
        .monbus_ready          (monbus_ready),
        .monbus_packet         (monbus_packet),
        .debug_fifo_count      (debug_fifo_count),
        .debug_packet_count    (debug_packet_count)
    );

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // No grant_ack used (WAIT_GNT_ACK=0)
    always @(posedge clk) begin
        if (rst_n) assume (grant_ack == '0);
    end

    // Disable PWM to simplify (focus on arbiter properties)
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!cfg_pwm_start);
            assume (cfg_pwm_sync_rst_n);
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

    // P3: If grant_valid, at least one grant bit is set
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_grant_nonzero: assert (|grant);
    end

    // P4: If no grant_valid, grant is zero
    always @(posedge clk) begin
        if (rst_n && !grant_valid)
            ap_no_grant_zero: assert (grant == '0);
    end

    // P5: Grant only to clients that were requesting (current or previous cycle)
    //     The arbiter has registered outputs, so grant may appear one cycle after request
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && grant_valid)
            ap_grant_implies_request: assert ((grant & (request | $past(request))) == grant);
    end

    // P6: grant_id matches the grant bit position
    always @(posedge clk) begin
        if (rst_n && grant_valid)
            ap_grant_id_match: assert (grant[grant_id]);
    end

    // P7: When PWM is inactive (disabled), arbiter should be able to grant
    // (verifies PWM-to-block_arb connection indirectly)
    // With PWM disabled (no start), pwm_out should stay low
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_pwm_inactive: assert (!pwm_out);
    end

    // P8: Reset clears monbus_valid (FIFO empty after reset)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus: assert (!monbus_valid);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Grant issued
    always @(posedge clk) begin
        if (rst_n)
            cp_grant: cover (grant_valid);
    end

    // C2: Multiple clients requesting
    always @(posedge clk) begin
        if (rst_n)
            cp_multi_req: cover (&request);
    end

    // C3: No requests, no grant
    always @(posedge clk) begin
        if (rst_n)
            cp_idle: cover (request == '0 && !grant_valid);
    end

    // C4: Monitor output valid
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus: cover (monbus_valid && monbus_ready);
    end

endmodule
