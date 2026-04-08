// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible copy of arbiter_rr_pwm_monbus.sv
// Removed: initial assert, verilator pragmas

`timescale 1ns / 1ps

module arbiter_rr_pwm_monbus #(
    parameter int CLIENTS = 4,
    parameter int WAIT_GNT_ACK = 0,
    parameter logic [7:0] MON_AGENT_ID = 8'h10,
    parameter logic [3:0] MON_UNIT_ID = 4'h0,

    localparam int MAX_LEVELS = 16,
    localparam int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS),
    localparam int CXMTW = CLIENTS * MAX_LEVELS_WIDTH,

    localparam int PWM_WIDTH = 16,
    localparam int MON_FIFO_DEPTH = 16,
    localparam int MON_FIFO_ALMOST_MARGIN = 2,
    localparam int FAIRNESS_REPORT_CYCLES = 256,
    localparam int MIN_GRANTS_FOR_FAIRNESS = 64,

    parameter int N = $clog2(CLIENTS)
) (
    input  logic                          clk,
    input  logic                          rst_n,

    input  logic [CLIENTS-1:0]            request,
    output logic                          grant_valid,
    output logic [CLIENTS-1:0]            grant,
    output logic [N-1:0]                  grant_id,
    input  logic [CLIENTS-1:0]            grant_ack,

    input  logic                          cfg_pwm_sync_rst_n,
    input  logic                          cfg_pwm_start,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_duty,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_period,
    input  logic [PWM_WIDTH-1:0]          cfg_pwm_repeat_count,
    output logic                          cfg_pwm_sts_done,
    output logic                          pwm_out,

    input  logic                          cfg_mon_enable,
    input  logic [15:0]                   cfg_mon_pkt_type_enable,
    input  logic [15:0]                   cfg_mon_latency,
    input  logic [15:0]                   cfg_mon_starvation,
    input  logic [15:0]                   cfg_mon_fairness,
    input  logic [15:0]                   cfg_mon_active,
    input  logic [7:0]                    cfg_mon_period,

    output logic                          monbus_valid,
    input  logic                          monbus_ready,
    output logic [63:0]                   monbus_packet,

    output logic [$clog2(MON_FIFO_DEPTH+1)-1:0] debug_fifo_count,
    output logic [15:0]                   debug_packet_count
);

    logic block_arb_internal;
    assign block_arb_internal = pwm_out;

    arbiter_round_robin #(
        .CLIENTS      (CLIENTS),
        .WAIT_GNT_ACK (WAIT_GNT_ACK)
    ) u_arbiter (
        .clk         (clk),
        .rst_n       (rst_n),
        .block_arb   (block_arb_internal),
        .request     (request),
        .grant_ack   (grant_ack),
        .grant_valid (grant_valid),
        .grant       (grant),
        .grant_id    (grant_id),
        .last_grant  ()
    );

    pwm #(
        .WIDTH    (PWM_WIDTH),
        .CHANNELS (1)
    ) u_pwm (
        .clk          (clk),
        .rst_n        (rst_n),
        .sync_rst_n   (cfg_pwm_sync_rst_n),
        .start        (cfg_pwm_start),
        .duty         (cfg_pwm_duty),
        .period       (cfg_pwm_period),
        .repeat_count (cfg_pwm_repeat_count),
        .done         (cfg_pwm_sts_done),
        .pwm_out      (pwm_out)
    );

    arbiter_monbus_common #(
        .CLIENTS                 (CLIENTS),
        .MON_AGENT_ID            (MON_AGENT_ID),
        .MON_UNIT_ID             (MON_UNIT_ID),
        .MON_FIFO_DEPTH          (MON_FIFO_DEPTH),
        .MON_FIFO_ALMOST_MARGIN  (MON_FIFO_ALMOST_MARGIN),
        .FAIRNESS_REPORT_CYCLES  (FAIRNESS_REPORT_CYCLES),
        .MIN_GRANTS_FOR_FAIRNESS (MIN_GRANTS_FOR_FAIRNESS)
    ) u_monitor (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .cfg_max_thresh          ({CLIENTS{MAX_LEVELS_WIDTH'(1)}}),
        .request                 (request),
        .grant_valid             (grant_valid),
        .grant                   (grant),
        .grant_id                (grant_id),
        .grant_ack               (grant_ack),
        .block_arb               (block_arb_internal),
        .cfg_mon_enable          (cfg_mon_enable),
        .cfg_mon_pkt_type_enable (cfg_mon_pkt_type_enable),
        .cfg_mon_latency_thresh  (cfg_mon_latency),
        .cfg_mon_starvation_thresh (cfg_mon_starvation),
        .cfg_mon_fairness_thresh (cfg_mon_fairness),
        .cfg_mon_active_thresh   (cfg_mon_active),
        .cfg_mon_ack_timeout_thresh (16'h40),
        .cfg_mon_efficiency_thresh  (16'h50),
        .cfg_mon_sample_period   (cfg_mon_period),
        .monbus_valid            (monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),
        .debug_fifo_count        (debug_fifo_count),
        .debug_packet_count      (debug_packet_count),
        .debug_ack_timeout       (),
        .debug_protocol_violations (),
        .debug_grant_efficiency  (),
        .debug_client_starvation (),
        .debug_fairness_deviation (),
        .debug_monitor_state     ()
    );

endmodule : arbiter_rr_pwm_monbus
