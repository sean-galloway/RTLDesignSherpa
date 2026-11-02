// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_ocelus_plane
// Purpose: The memory controller's Ocelus observability plane: two passive
//          axi_monitor_lite taps on the core's AXI4 slave port (read, write),
//          mc_monlite on the controller's internal events, a 3-client
//          monbus_arbiter, and monbus_axil4_group_1wr writing every packet to
//          memory over one AXI-Lite master port (error window + trace window).
//
// Documentation: projects/components/mem-ctrl-ip/common-ip/docs/common_mas/ch11_ocelus_plane/01_mc_ocelus_plane.md
// Subsystem: mem-ctrl-ip common-ip
//
// Author: sean galloway
// Created: 2026-11-01
//==============================================================================
// Description:
//   Observation only. The AXI taps watch the port's handshakes (the lite
//   ocelus never touches the traffic it watches: an event it cannot deliver
//   is dropped and counted); mc_monlite reads taps the core already has.
//   Nothing here can stall the controller -- the one place backpressure
//   exists is the AXI-Lite master, and a full group FIFO drops at the
//   monitors, not at the port.
//
//   Clients on the arbiter: 0 = read monitor (PROTOCOL_AXI, AGENT_RD),
//   1 = write monitor (PROTOCOL_AXI, AGENT_WR), 2 = mc_monlite
//   (PROTOCOL_CORE, AGENT_CORE). The group's AXI slot takes the AXI
//   packets, its CORE slot mc_monlite's; its AXIS slot is unused and tied to
//   "drop nothing, select nothing". cfg_err_select routes packet types to
//   the error window for both protocols (bit[packet type]).
//
// Parameters:
//   - HAS_MON: 0 = nothing built; every output tied to 0, m_axil idle
//   - AXI_ID_WIDTH / AXI_ADDR_WIDTH: the watched port
//   - MON_ADDR_WIDTH: the AXI-Lite master's address width
//   - ACLK_MHZ: the timeout's microsecond tick (counter_freq_invariant)
//   - UNIT_ID, AGENT_RD / AGENT_WR / AGENT_CORE: packet identity
//   - MAX_TRANSACTIONS: per-direction lite table depth
//   - REF_BACKLOG_MAX: mc_monlite's refresh-backlog trip level
//
// Test:
//   projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/dv/tests/top/test_granite_ocelus.py
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_ocelus_plane
    import mc_common_pkg::*;
    import ocelus_common_pkg::*;
#(
    parameter bit          HAS_MON          = 1'b1,
    parameter int          AXI_ID_WIDTH     = 8,
    parameter int          AXI_ADDR_WIDTH   = 32,
    parameter int          MON_ADDR_WIDTH   = 32,
    parameter int          ACLK_MHZ         = 100,
    parameter logic [7:0]  UNIT_ID          = 8'h20,
    parameter logic [15:0] AGENT_RD         = 16'h0010,
    parameter logic [15:0] AGENT_WR         = 16'h0011,
    parameter logic [15:0] AGENT_CORE       = 16'h0012,
    parameter int          MAX_TRANSACTIONS = 8,
    parameter logic [3:0]  REF_BACKLOG_MAX  = 4'd8,

    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int MAW = MON_ADDR_WIDTH
) (
    input  logic              aclk,
    input  logic              aresetn,

    // ---- AXI4 slave port taps (the core's s_axi_*; observe only) ----
    input  logic [IW-1:0]     tap_arid,
    input  logic [AW-1:0]     tap_araddr,
    input  logic [7:0]        tap_arlen,
    input  logic              tap_arvalid,
    input  logic              tap_arready,
    input  logic [IW-1:0]     tap_rid,
    input  logic [1:0]        tap_rresp,
    input  logic              tap_rlast,
    input  logic              tap_rvalid,
    input  logic              tap_rready,
    input  logic [IW-1:0]     tap_awid,
    input  logic [AW-1:0]     tap_awaddr,
    input  logic [7:0]        tap_awlen,
    input  logic              tap_awvalid,
    input  logic              tap_awready,
    input  logic              tap_wlast,
    input  logic              tap_wvalid,
    input  logic              tap_wready,
    input  logic [IW-1:0]     tap_bid,
    input  logic [1:0]        tap_bresp,
    input  logic              tap_bvalid,
    input  logic              tap_bready,

    // ---- internal-event taps (mc_monlite) ----
    input  logic              ev_cal_err_i,
    input  logic              ev_zq_overdue_i,
    input  logic [3:0]        ev_ref_pending_i,
    input  logic              ev_aw_ragged_i,
    input  logic              ev_rd_beat_lost_i,
    input  logic              ev_ret_orphan_i,
    input  logic              ev_init_done_i,
    input  logic [4:0]        ev_init_state_i,
    input  logic              ev_dir_flip_i,
    input  logic              ev_dir_i,
    input  logic [1:0]        ev_dir_cause_i,
    input  logic [7:0]        ev_dir_batch_i,
    input  logic              ev_cmd_accept_i,
    input  dram_op_e          ev_cmd_accept_op_i,
    input  logic              ev_accept_to_pre_i,
    input  logic              ev_store_wr_full_i,
    input  logic              ev_store_rd_full_i,
    input  logic              ev_ring_full_i,

    // ---- configuration (CSR) ----
    input  logic              cfg_rd_enable,          // read monitor
    input  logic              cfg_wr_enable,          // write monitor
    input  logic              cfg_core_enable,        // mc_monlite
    input  logic              cfg_error_enable,       // AXI monitors: error packets
    input  logic              cfg_compl_enable,       // AXI monitors: completion packets
    input  logic              cfg_timeout_enable,     // AXI monitors: timeout packets
    input  logic              cfg_threshold_enable,   // AXI monitors: threshold packets
    input  logic [15:0]       cfg_timeout_us,         // no progress for this long (us); 0 = never
    input  logic [3:0]        cfg_freq_sel,
    input  logic [15:0]       cfg_active_threshold,   // outstanding transactions above this -> Threshold
    input  logic [31:0]       cfg_latency_threshold,  // completion latency (cycles) above this -> Threshold
    input  logic [15:0]       cfg_axi_pkt_mask,       // bit[packet type] = 1 drops it (AXI monitors)
    input  logic [15:0]       cfg_core_ev_en,         // bit[mc_event_e] (mc_monlite)
    input  logic [15:0]       cfg_err_select,         // bit[packet type] = 1 -> error window
    input  logic [MAW-1:0]    cfg_base_addr,          // trace window
    input  logic [MAW-1:0]    cfg_limit_addr,
    input  logic [15:0]       cfg_flush_watermark,
    input  logic [MAW-1:0]    cfg_err_base_addr,      // error window
    input  logic [MAW-1:0]    cfg_err_limit_addr,
    input  logic [15:0]       cfg_err_flush_watermark,

    // ---- AXI-Lite master write (both windows) ----
    output logic              m_axil_awvalid,
    input  logic              m_axil_awready,
    output logic [MAW-1:0]    m_axil_awaddr,
    output logic [2:0]        m_axil_awprot,
    output logic              m_axil_wvalid,
    input  logic              m_axil_wready,
    output logic [63:0]       m_axil_wdata,
    output logic [7:0]        m_axil_wstrb,
    input  logic              m_axil_bvalid,
    output logic              m_axil_bready,
    input  logic [1:0]        m_axil_bresp,

    // ---- status ----
    output logic              irq_o,                  // one pulse per error record landed
    output logic [15:0]       err_rec_count,          // error records landed (wraps)
    output logic [15:0]       rd_error_count,         // read monitor error + timeout packets
    output logic [15:0]       wr_error_count,
    output logic [15:0]       rd_compl_count,         // read monitor completion packets
    output logic [15:0]       wr_compl_count,
    output logic [15:0]       core_error_count,       // mc_monlite error packets
    output logic [15:0]       dropped_count           // events lost at any of the three sources (saturating sum)
);

    generate if (HAS_MON) begin : g_mon

        // ------------------------------------------------------------------
        // Timestamp: the group's free-running counter, broadcast to sources
        // ------------------------------------------------------------------
        monbus_timestamp_t w_mon_time;

        // timeout of 0 = never: the lite's counter compares against the
        // value, so 0 becomes the largest
        logic [15:0] w_timeout_cnt;
        assign w_timeout_cnt = (cfg_timeout_us == 16'h0) ? 16'hFFFF : cfg_timeout_us;

        logic              mb_valid [3];
        logic              mb_ready [3];
        monitor_packet_t   mb_pkt   [3];
        monbus_timestamp_t mb_ts    [3];
        logic [15:0]       w_drop_rd, w_drop_wr, w_drop_core;

        // ------------------------------------------------------------------
        // Read monitor (AR / R)
        // ------------------------------------------------------------------
        axi_monitor_lite #(
            .UNIT_ID          (UNIT_ID),
            .AGENT_ID         (AGENT_RD),
            .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
            .ADDR_WIDTH       (AW),
            .ID_WIDTH         (IW),
            .IS_READ          (1'b1),
            .IS_AXI           (1'b1),
            .CFI_MIN_FREQ_MHZ (ACLK_MHZ),
            .CFI_MAX_FREQ_MHZ (ACLK_MHZ)
        ) u_rd_mon (
            .aclk                       (aclk),
            .aresetn                    (aresetn),
            .clear                      (!cfg_rd_enable),
            .i_mon_time                 (w_mon_time),
            .cmd_addr                   (tap_araddr),
            .cmd_id                     (tap_arid),
            .cmd_len                    (tap_arlen),
            .cmd_valid                  (tap_arvalid && cfg_rd_enable),
            .cmd_ready                  (tap_arready),
            .data_id                    (tap_rid),
            .data_last                  (tap_rlast),
            .data_resp                  (tap_rresp),
            .data_valid                 (tap_rvalid && cfg_rd_enable),
            .data_ready                 (tap_rready),
            .resp_id                    (tap_rid),
            .resp_code                  (tap_rresp),
            .resp_valid                 (tap_rvalid && tap_rlast && cfg_rd_enable),
            .resp_ready                 (tap_rready),
            .cfg_freq_sel               (cfg_freq_sel),
            .cfg_timeout_cnt            (w_timeout_cnt),
            .cfg_error_enable           (cfg_error_enable),
            .cfg_compl_enable           (cfg_compl_enable),
            .cfg_timeout_enable         (cfg_timeout_enable),
            .cfg_threshold_enable       (cfg_threshold_enable),
            .cfg_active_trans_threshold (cfg_active_threshold),
            .cfg_latency_threshold      (cfg_latency_threshold),
            .cfg_axi_pkt_mask           (cfg_axi_pkt_mask),
            .cfg_addr_check_enable      (1'b0),
            .cfg_addr_match_enable      (1'b0),
            .cfg_addr_range_enable      ('0),
            .cfg_addr_range_low         ('0),
            .cfg_addr_range_high        ('0),
            .monbus_valid               (mb_valid[0]),
            .monbus_ready               (mb_ready[0]),
            .monbus_packet              (mb_pkt[0]),
            .monbus_timestamp           (mb_ts[0]),
            /* verilator lint_off PINCONNECTEMPTY */
            .active_count               (),
            .busy                       (),
            .refused_count              (),
            /* verilator lint_on PINCONNECTEMPTY */
            .perf_completed_count       (rd_compl_count),
            .perf_error_count           (rd_error_count),
            .dropped_count              (w_drop_rd)
        );

        // ------------------------------------------------------------------
        // Write monitor (AW / W / B); W carries no ID, the lite orders it
        // ------------------------------------------------------------------
        axi_monitor_lite #(
            .UNIT_ID          (UNIT_ID),
            .AGENT_ID         (AGENT_WR),
            .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
            .ADDR_WIDTH       (AW),
            .ID_WIDTH         (IW),
            .IS_READ          (1'b0),
            .IS_AXI           (1'b1),
            .CFI_MIN_FREQ_MHZ (ACLK_MHZ),
            .CFI_MAX_FREQ_MHZ (ACLK_MHZ)
        ) u_wr_mon (
            .aclk                       (aclk),
            .aresetn                    (aresetn),
            .clear                      (!cfg_wr_enable),
            .i_mon_time                 (w_mon_time),
            .cmd_addr                   (tap_awaddr),
            .cmd_id                     (tap_awid),
            .cmd_len                    (tap_awlen),
            .cmd_valid                  (tap_awvalid && cfg_wr_enable),
            .cmd_ready                  (tap_awready),
            .data_id                    (tap_awid),
            .data_last                  (tap_wlast),
            .data_resp                  (2'b00),
            .data_valid                 (tap_wvalid && cfg_wr_enable),
            .data_ready                 (tap_wready),
            .resp_id                    (tap_bid),
            .resp_code                  (tap_bresp),
            .resp_valid                 (tap_bvalid && cfg_wr_enable),
            .resp_ready                 (tap_bready),
            .cfg_freq_sel               (cfg_freq_sel),
            .cfg_timeout_cnt            (w_timeout_cnt),
            .cfg_error_enable           (cfg_error_enable),
            .cfg_compl_enable           (cfg_compl_enable),
            .cfg_timeout_enable         (cfg_timeout_enable),
            .cfg_threshold_enable       (cfg_threshold_enable),
            .cfg_active_trans_threshold (cfg_active_threshold),
            .cfg_latency_threshold      (cfg_latency_threshold),
            .cfg_axi_pkt_mask           (cfg_axi_pkt_mask),
            .cfg_addr_check_enable      (1'b0),
            .cfg_addr_match_enable      (1'b0),
            .cfg_addr_range_enable      ('0),
            .cfg_addr_range_low         ('0),
            .cfg_addr_range_high        ('0),
            .monbus_valid               (mb_valid[1]),
            .monbus_ready               (mb_ready[1]),
            .monbus_packet              (mb_pkt[1]),
            .monbus_timestamp           (mb_ts[1]),
            /* verilator lint_off PINCONNECTEMPTY */
            .active_count               (),
            .busy                       (),
            .refused_count              (),
            /* verilator lint_on PINCONNECTEMPTY */
            .perf_completed_count       (wr_compl_count),
            .perf_error_count           (wr_error_count),
            .dropped_count              (w_drop_wr)
        );

        // ------------------------------------------------------------------
        // Internal events
        // ------------------------------------------------------------------
        mc_monlite #(
            .UNIT_ID         (UNIT_ID),
            .AGENT_ID        (AGENT_CORE),
            .REF_BACKLOG_MAX (REF_BACKLOG_MAX)
        ) u_core_mon (
            .aclk             (aclk),
            .aresetn          (aresetn),
            .cfg_enable       (cfg_core_enable),
            .cfg_ev_en        (cfg_core_ev_en),
            .cal_err_i        (ev_cal_err_i),
            .zq_overdue_i     (ev_zq_overdue_i),
            .ref_pending_i    (ev_ref_pending_i),
            .aw_ragged_i      (ev_aw_ragged_i),
            .rd_beat_lost_i   (ev_rd_beat_lost_i),
            .ret_orphan_i     (ev_ret_orphan_i),
            .init_done_i      (ev_init_done_i),
            .init_state_i     (ev_init_state_i),
            .dir_flip_i       (ev_dir_flip_i),
            .dir_i            (ev_dir_i),
            .dir_cause_i      (ev_dir_cause_i),
            .dir_batch_i      (ev_dir_batch_i),
            .cmd_accept_i     (ev_cmd_accept_i),
            .cmd_accept_op_i  (ev_cmd_accept_op_i),
            .accept_to_pre_i  (ev_accept_to_pre_i),
            .store_wr_full_i  (ev_store_wr_full_i),
            .store_rd_full_i  (ev_store_rd_full_i),
            .ring_full_i      (ev_ring_full_i),
            .i_mon_time       (w_mon_time),
            .monbus_valid     (mb_valid[2]),
            .monbus_ready     (mb_ready[2]),
            .monbus_packet    (mb_pkt[2]),
            .monbus_timestamp (mb_ts[2]),
            .error_count      (core_error_count),
            .dropped_count    (w_drop_core)
        );

        // ------------------------------------------------------------------
        // Arbiter -> group
        // ------------------------------------------------------------------
        logic              w_arb_valid, w_arb_ready;
        monitor_packet_t   w_arb_pkt;
        monbus_timestamp_t w_arb_ts;

        monbus_arbiter #(
            .CLIENTS            (3),
            .INPUT_SKID_ENABLE  (0),
            .OUTPUT_SKID_ENABLE (1),
            .OUTPUT_SKID_DEPTH  (2)
        ) u_arb (
            .axi_aclk            (aclk),
            .axi_aresetn         (aresetn),
            .block_arb           (1'b0),
            .monbus_valid_in     (mb_valid),
            .monbus_ready_in     (mb_ready),
            .monbus_packet_in    (mb_pkt),
            .monbus_timestamp_in (mb_ts),
            .monbus_valid        (w_arb_valid),
            .monbus_ready        (w_arb_ready),
            .monbus_packet       (w_arb_pkt),
            .monbus_timestamp    (w_arb_ts),
            /* verilator lint_off PINCONNECTEMPTY */
            .grant_valid         (),
            .grant               (),
            .grant_id            (),
            .last_grant          ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        monbus_axil4_group_1wr #(
            .ADDR_WIDTH      (MAW),
            .NUM_PROTOCOLS   (3),
            .USE_COMPRESSION (0),
            .HALF_BEAT_EN    (0)
        ) u_group (
            .axi_aclk                (aclk),
            .axi_aresetn             (aresetn),
            .cam_clear               (1'b0),
            .monbus_valid            (w_arb_valid),
            .monbus_ready            (w_arb_ready),
            .monbus_packet           (w_arb_pkt),
            .monbus_timestamp        (w_arb_ts),
            .mon_time_out            (w_mon_time),
            .m_axil_awvalid          (m_axil_awvalid),
            .m_axil_awready          (m_axil_awready),
            .m_axil_awaddr           (m_axil_awaddr),
            .m_axil_awprot           (m_axil_awprot),
            .m_axil_wvalid           (m_axil_wvalid),
            .m_axil_wready           (m_axil_wready),
            .m_axil_wdata            (m_axil_wdata),
            .m_axil_wstrb            (m_axil_wstrb),
            .m_axil_bvalid           (m_axil_bvalid),
            .m_axil_bready           (m_axil_bready),
            .m_axil_bresp            (m_axil_bresp),
            .irq_out                 (irq_o),
            .err_rec_count           (err_rec_count),
            .cfg_base_addr           (cfg_base_addr),
            .cfg_limit_addr          (cfg_limit_addr),
            .cfg_flush_watermark     (cfg_flush_watermark),
            .cfg_err_base_addr       (cfg_err_base_addr),
            .cfg_err_limit_addr      (cfg_err_limit_addr),
            .cfg_err_flush_watermark (cfg_err_flush_watermark),
            .cfg_compress_en         (1'b0),
            // AXI slot: the two port monitors filter inside themselves; the
            // group drops nothing more and routes by cfg_err_select
            .cfg_axi_pkt_mask        (16'h0000),
            .cfg_axi_err_select      (cfg_err_select),
            .cfg_axi_error_mask      (16'h0000),
            .cfg_axi_timeout_mask    (16'h0000),
            .cfg_axi_compl_mask      (16'h0000),
            .cfg_axi_thresh_mask     (16'h0000),
            .cfg_axi_perf_mask       (16'h0000),
            .cfg_axi_addr_mask       (16'h0000),
            .cfg_axi_debug_mask      (16'h0000),
            // AXIS slot: no source emits it
            .cfg_axis_pkt_mask       (16'h0000),
            .cfg_axis_err_select     (16'h0000),
            .cfg_axis_error_mask     (16'h0000),
            .cfg_axis_timeout_mask   (16'h0000),
            .cfg_axis_compl_mask     (16'h0000),
            .cfg_axis_credit_mask    (16'h0000),
            .cfg_axis_channel_mask   (16'h0000),
            .cfg_axis_stream_mask    (16'h0000),
            // CORE slot: mc_monlite filters per event (cfg_core_ev_en)
            .cfg_core_pkt_mask       (16'h0000),
            .cfg_core_err_select     (cfg_err_select),
            .cfg_core_error_mask     (16'h0000),
            .cfg_core_timeout_mask   (16'h0000),
            .cfg_core_compl_mask     (16'h0000),
            .cfg_core_thresh_mask    (16'h0000),
            .cfg_core_perf_mask      (16'h0000),
            .cfg_core_debug_mask     (16'h0000),
            /* verilator lint_off PINCONNECTEMPTY */
            .err_fifo_full                     (),
            .write_fifo_full                   (),
            .err_fifo_count                    (),
            .write_fifo_count                  (),
            .mon_compressor_stat_tier1_a       (),
            .mon_compressor_stat_tier1_b       (),
            .mon_compressor_stat_tier1_c       (),
            .mon_compressor_stat_tier0         (),
            .mon_compressor_stat_cam_miss      (),
            .mon_compressor_stat_delta_ts_ovf  (),
            .mon_compressor_stat_event_data_ovf(),
            .mon_compressor_stat_ed_delta_ovf  ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        // the three sources' loss counts, summed and saturated
        logic [17:0] w_drop_sum;
        assign w_drop_sum    = 18'(w_drop_rd) + 18'(w_drop_wr) + 18'(w_drop_core);
        assign dropped_count = (w_drop_sum > 18'hFFFF) ? 16'hFFFF : w_drop_sum[15:0];

    end else begin : g_no_mon
        assign m_axil_awvalid   = 1'b0;
        assign m_axil_awaddr    = '0;
        assign m_axil_awprot    = '0;
        assign m_axil_wvalid    = 1'b0;
        assign m_axil_wdata     = '0;
        assign m_axil_wstrb     = '0;
        assign m_axil_bready    = 1'b1;
        assign irq_o            = 1'b0;
        assign err_rec_count    = '0;
        assign rd_error_count   = '0;
        assign wr_error_count   = '0;
        assign rd_compl_count   = '0;
        assign wr_compl_count   = '0;
        assign core_error_count = '0;
        assign dropped_count    = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire _unused_no_mon = &{1'b0, tap_arid, tap_araddr, tap_arlen, tap_arvalid, tap_arready,
                                tap_rid, tap_rresp, tap_rlast, tap_rvalid, tap_rready,
                                tap_awid, tap_awaddr, tap_awlen, tap_awvalid, tap_awready,
                                tap_wlast, tap_wvalid, tap_wready, tap_bid, tap_bresp,
                                tap_bvalid, tap_bready,
                                ev_cal_err_i, ev_zq_overdue_i, ev_ref_pending_i, ev_aw_ragged_i,
                                ev_rd_beat_lost_i, ev_ret_orphan_i, ev_init_done_i,
                                ev_init_state_i, ev_dir_flip_i, ev_dir_i, ev_dir_cause_i,
                                ev_dir_batch_i, ev_cmd_accept_i, ev_cmd_accept_op_i,
                                ev_accept_to_pre_i, ev_store_wr_full_i, ev_store_rd_full_i,
                                ev_ring_full_i,
                                cfg_rd_enable, cfg_wr_enable, cfg_core_enable,
                                cfg_error_enable, cfg_compl_enable, cfg_timeout_enable,
                                cfg_threshold_enable, cfg_timeout_us, cfg_freq_sel,
                                cfg_active_threshold, cfg_latency_threshold,
                                cfg_axi_pkt_mask, cfg_core_ev_en, cfg_err_select,
                                cfg_base_addr, cfg_limit_addr, cfg_flush_watermark,
                                cfg_err_base_addr, cfg_err_limit_addr,
                                cfg_err_flush_watermark,
                                m_axil_awready, m_axil_wready, m_axil_bvalid, m_axil_bresp};
        /* verilator lint_on UNUSEDSIGNAL */
    end endgenerate

endmodule : mc_ocelus_plane
