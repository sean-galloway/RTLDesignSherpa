// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway

`timescale 1ns / 1ps
`include "reset_defs.svh"

module axi4_rd_monfull_snoop
    import ocelus_common_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID = 8'h01,
    parameter logic [15:0] AGENT_ID = 16'h000A,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_ID_WIDTH = 8,
    parameter int MAX_TRANSACTIONS = 16,
    parameter int NUM_BANKS = 1,
    parameter bit ID_FILTER_ENABLE = 1'b0,
    parameter int ID_MATCH_BASE = 0,
    parameter int ID_MATCH_COUNT = 0,
    parameter bit ADDR_FILTER_ENABLE = 1'b0,
    parameter int ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter int ACLK_MHZ = 100,
    parameter int CFI_MIN_FREQ_MHZ = ACLK_MHZ,
    parameter int CFI_MAX_FREQ_MHZ = ACLK_MHZ,
    parameter int N_ADDR_RANGES = 0,
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]
                  ADDR_RANGE_IS_ERROR = '0,
    parameter bit ENABLE_FILTERING = 1'b1,
    parameter bit ADD_PIPELINE_STAGE = 1'b0,
    parameter bit ENABLE_ERROR_LOGIC = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC = 1'b1,
    parameter bit ENABLE_DEBUG_LOGIC = 1'b0
) (
    input  logic                          aclk,
    input  logic                          aresetn,
    input  logic                          cam_clear,

    input  logic [AXI_ID_WIDTH-1:0]       cmd_id,
    input  logic [AXI_ADDR_WIDTH-1:0]     cmd_addr,
    input  logic [7:0]                    cmd_len,
    input  logic [2:0]                    cmd_size,
    input  logic [1:0]                    cmd_burst,
    input  logic                          cmd_valid,
    input  logic                          cmd_ready,

    input  logic [AXI_ID_WIDTH-1:0]       data_id,
    input  logic [1:0]                    data_resp,
    input  logic                          data_last,
    input  logic                          data_valid,
    input  logic                          data_ready,

    input  logic                          cfg_monitor_enable,
    input  logic                          cfg_error_enable,
    input  logic                          cfg_timeout_enable,
    input  logic                          cfg_perf_enable,
    input  logic                          cfg_compl_enable,
    input  logic                          cfg_threshold_enable,
    input  logic                          cfg_debug_enable,
    input  logic [15:0]                   cfg_timeout_cycles,
    input  logic [3:0]                    cfg_freq_sel,
    input  logic [31:0]                   cfg_latency_threshold,
    input  logic [15:0]                   cfg_axi_pkt_mask,
    input  logic [15:0]                   cfg_axi_err_select,
    input  logic [15:0]                   cfg_axi_error_mask,
    input  logic [15:0]                   cfg_axi_timeout_mask,
    input  logic [15:0]                   cfg_axi_compl_mask,
    input  logic [15:0]                   cfg_axi_thresh_mask,
    input  logic [15:0]                   cfg_axi_perf_mask,
    input  logic [15:0]                   cfg_axi_addr_mask,
    input  logic [15:0]                   cfg_axi_debug_mask,
    input  logic                          cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]
                                          cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AXI_ADDR_WIDTH-1:0]
                                          cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AXI_ADDR_WIDTH-1:0]
                                          cfg_addr_range_high,
    input  logic [2:0]                    cfg_start_event_sel,
    input  logic [2:0]                    cfg_end_event_sel,
    input  logic                          cfg_start_trigger,
    input  logic                          cfg_end_trigger,
    input  logic                          cfg_window_force_close,
    input  monbus_timestamp_t             i_mon_time,

    output logic                          monbus_valid,
    input  logic                          monbus_ready,
    output monitor_packet_t               monbus_packet,
    output monbus_timestamp_t             monbus_timestamp,
    output logic                          busy,
    output logic [7:0]                    active_transactions,
    output logic [15:0]                   error_count,
    output logic [31:0]                   transaction_count,
    output logic [15:0]                   dropped_count,
    output logic [15:0]                   refused_count
);

    logic w_clear;
    logic w_cmd_refused;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;
    logic [15:0] r_refused;

    assign w_clear = cam_clear | ~cfg_monitor_enable;
    assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                                                          : cfg_timeout_cycles;

    axi_monitor_filtered #(
        .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID),
        .CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ), .CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS), .NUM_BANKS(NUM_BANKS),
        .ID_FILTER_ENABLE(ID_FILTER_ENABLE), .ID_MATCH_BASE(ID_MATCH_BASE),
        .ID_MATCH_COUNT(ID_MATCH_COUNT), .ADDR_FILTER_ENABLE(ADDR_FILTER_ENABLE),
        .ADDR_WIDTH(AXI_ADDR_WIDTH), .ID_WIDTH(AXI_ID_WIDTH),
        .IS_READ(1'b1), .IS_AXI(1'b1), .ENABLE_PERF_PACKETS(1'b1),
        .ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
        .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE),
        .N_ADDR_RANGES(N_ADDR_RANGES), .ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR)
    ) u_monitor (
        .aclk(aclk), .aresetn(aresetn), .clear(w_clear),
        .cmd_addr(cmd_addr), .cmd_id(cmd_id), .cmd_len(cmd_len),
        .cmd_size(cmd_size), .cmd_burst(cmd_burst),
        .cmd_valid(cmd_valid & cfg_monitor_enable), .cmd_ready(cmd_ready),
        .data_id(data_id), .data_last(data_last), .data_resp(data_resp),
        .data_valid(data_valid & cfg_monitor_enable), .data_ready(data_ready),
        .resp_id(data_id), .resp_code(data_resp),
        .resp_valid(data_valid & data_last & cfg_monitor_enable), .resp_ready(data_ready),
        .cfg_freq_sel(cfg_freq_sel),
        .cfg_addr_cnt(w_timeout_cnt), .cfg_data_cnt(w_timeout_cnt),
        .cfg_resp_cnt(w_timeout_cnt),
        .cfg_error_enable(cfg_error_enable), .cfg_compl_enable(cfg_compl_enable),
        .cfg_threshold_enable(cfg_threshold_enable),
        .cfg_timeout_enable(cfg_timeout_enable), .cfg_perf_enable(cfg_perf_enable),
        .cfg_debug_enable(cfg_debug_enable), .cfg_debug_level(4'h0),
        .cfg_debug_mask(16'h0),
        .cfg_active_trans_threshold(16'(ACTIVE_TRANS_THRESHOLD)),
        .cfg_latency_threshold(cfg_latency_threshold),
        .cfg_axi_pkt_mask(cfg_axi_pkt_mask), .cfg_axi_err_select(cfg_axi_err_select),
        .cfg_axi_error_mask(cfg_axi_error_mask), .cfg_axi_timeout_mask(cfg_axi_timeout_mask),
        .cfg_axi_compl_mask(cfg_axi_compl_mask), .cfg_axi_thresh_mask(cfg_axi_thresh_mask),
        .cfg_axi_perf_mask(cfg_axi_perf_mask), .cfg_axi_addr_mask(cfg_axi_addr_mask),
        .cfg_axi_debug_mask(cfg_axi_debug_mask),
        .cfg_addr_check_enable(cfg_addr_check_enable),
        .cfg_addr_range_enable(cfg_addr_range_enable),
        .cfg_addr_range_low(cfg_addr_range_low), .cfg_addr_range_high(cfg_addr_range_high),
        .cfg_id_filter_enable(1'b0), .cfg_id_match_base(ID_MATCH_BASE),
        .cfg_id_match_count(ID_MATCH_COUNT),
        .cfg_addr_filter_enable(1'b0), .cfg_addr_filter_low('0), .cfg_addr_filter_high('0),
        .cfg_start_event_sel(cfg_start_event_sel), .cfg_end_event_sel(cfg_end_event_sel),
        .cfg_start_trigger(cfg_start_trigger), .cfg_end_trigger(cfg_end_trigger),
        .cfg_window_force_close(cfg_window_force_close), .i_mon_time(i_mon_time),
        .monbus_valid(monbus_valid), .monbus_ready(monbus_ready),
        .monbus_packet(monbus_packet), .monbus_timestamp(monbus_timestamp),
        /* verilator lint_off PINCONNECTEMPTY */
        .block_ready(),
        /* verilator lint_on PINCONNECTEMPTY */
        .busy(busy), .active_count(active_transactions), .cmd_refused(w_cmd_refused),
        /* verilator lint_off PINCONNECTEMPTY */
        .window_active(), .window_cycles(), .perf_prod_cycles(), .perf_bp_cycles(),
        .perf_starv_cycles(), .perf_idle_cycles(), .perf_beat_count(), .perf_byte_count(),
        .perf_burst_count(), .cfg_conflict_error(),
        /* verilator lint_on PINCONNECTEMPTY */
        .perf_completed_count(w_perf_completed_count), .perf_error_count(w_perf_error_count)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_refused <= 16'h0;
        end else if (w_clear) begin
            r_refused <= 16'h0;
        end else if (w_cmd_refused && (r_refused != 16'hFFFF)) begin
            r_refused <= r_refused + 1'b1;
        end
    )

    assign refused_count = r_refused;
    assign dropped_count = 16'h0;
    assign error_count = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

endmodule : axi4_rd_monfull_snoop
