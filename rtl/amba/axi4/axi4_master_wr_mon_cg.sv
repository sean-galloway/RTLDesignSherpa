// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_mon_cg
// Purpose: Axi4 Master Wr Mon Cg module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Write with Integrated Filtered Monitoring and Clock Gating
 *
 * This module extends axi4_master_wr_mon with comprehensive clock gating capabilities
 * for power optimization. Features include:
 *
 * - Instantiates axi4_master_wr_mon for core functionality with filtering
 * - Activity-based clock gating for the monitor subsystem
 * - Configurable clock gating policies and thresholds
 * - Independent gating for different monitor functions
 * - Performance monitoring with clock gating statistics
 * - Fine-grained power management controls
 */

`include "reset_defs.svh"
module axi4_master_wr_mon_cg
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (passed through to axi4_master_wr_mon)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor in inner mon; outputs tied
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter bit ADDR_FILTER_ENABLE = 1'b0,  // 0 = address filter inert
    parameter bit ID_FILTER_ENABLE   = 1'b0,  // 0 = ID filter inert
    parameter int ID_MATCH_BASE      = 0,
    parameter int ID_MATCH_COUNT     = 0,     // 0 = all IDs
    parameter logic [7:0]  UNIT_ID  = 8'h01,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h000B,    // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor

    // Filtering parameters
    parameter bit ENABLE_FILTERING  = 1,     // Enable packet filtering
    parameter bit ADD_PIPELINE_STAGE = 0,    // Add register stage for timing closure

    // Reporter sub-block enables (default 1'b1 = legacy behavior). Set to 0
    // to drop the detection cone at synthesis via generate-if.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4,   // Width of the idle countdown

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    input  logic                       cam_clear,  // sync clear of the monitor trans CAM

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_axi_awid,
    input  logic [AW-1:0]              fub_axi_awaddr,
    input  logic [7:0]                 fub_axi_awlen,
    input  logic [2:0]                 fub_axi_awsize,
    input  logic [1:0]                 fub_axi_awburst,
    input  logic                       fub_axi_awlock,
    input  logic [3:0]                 fub_axi_awcache,
    input  logic [2:0]                 fub_axi_awprot,
    input  logic [3:0]                 fub_axi_awqos,
    input  logic [3:0]                 fub_axi_awregion,
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Monitor Configuration
    input  logic                       cfg_monitor_enable,      // Enable monitoring
    input  logic                       cfg_error_enable,        // Enable error detection
    input  logic                       cfg_timeout_enable,      // Enable timeout detection
    input  logic                       cfg_perf_enable,         // Enable performance monitoring
    input  logic                       cfg_compl_enable,     // Enable completion packets
    input  logic                       cfg_threshold_enable, // Enable threshold packets
    input  logic                       cfg_debug_enable,     // Enable debug packets
    input  logic [15:0]                cfg_timeout_cycles,      // Timeout threshold in cycles
    input  logic [3:0]                 cfg_freq_sel,            // counter_freq_invariant LUT index
    input  logic [31:0]                cfg_latency_threshold,   // Latency threshold for alerts

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types (for future routing)
    input  logic [15:0]                cfg_axi_error_mask,      // Individual error event mask
    input  logic [15:0]                cfg_axi_timeout_mask,    // Individual timeout event mask
    input  logic [15:0]                cfg_axi_compl_mask,      // Individual completion event mask
    input  logic [15:0]                cfg_axi_thresh_mask,     // Individual threshold event mask
    input  logic [15:0]                cfg_axi_perf_mask,       // Individual performance event mask
    input  logic [15:0]                cfg_axi_addr_mask,       // Individual address match event mask
    input  logic [15:0]                cfg_axi_debug_mask,      // Individual debug event mask

    // Clock Gating Configuration
    input  logic                           cfg_cg_enable,       // Enable clock gating
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,   // Idle cycles before gating

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Address-range packet filter (active when ADDR_FILTER_ENABLE=1).
    // Inclusive [low, high]; a transaction whose command address falls
    // OUTSIDE the range has its packets suppressed.
    input  logic                                                       cfg_addr_filter_enable,
    input  logic [AW-1:0]                                              cfg_addr_filter_low,
    input  logic [AW-1:0]                                              cfg_addr_filter_high,

    // Runtime ID filter. Overrides ID_MATCH_BASE/COUNT while
    // cfg_id_filter_enable is high; tied low it is bit-identical
    // to the parameter-only build.
    input  logic                                                       cfg_id_filter_enable,
    input  logic [IW-1:0]                                              cfg_id_match_base,
    input  logic [IW:0]                                                cfg_id_match_count,

    // Free-running monitor-time broadcast from the monbus_group family
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Output
    output logic                                    monbus_valid,            // Monitor bus valid
    input  logic                                    monbus_ready,            // Monitor bus ready
    output monitor_common_pkg::monitor_packet_t     monbus_packet,           // Monitor packet (128-bit)
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,        // Side-band sampled time

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Clock gating status
    output logic                       cg_gating,               // Gated clock is stopped
    output logic                       cg_idle,                 // No activity observed

    // Configuration error flags
    output logic                       cfg_conflict_error,       // Configuration conflict detected

    // Performance window control (Stage A) + status (A) + buckets (B).
    input  logic [2:0]                 cfg_start_event_sel,
    input  logic [2:0]                 cfg_end_event_sel,
    input  logic                       cfg_start_trigger,
    input  logic                       cfg_end_trigger,
    input  logic                       cfg_window_force_close,
    output logic                       window_active,
    output logic [31:0]                window_cycles,
    output logic [31:0]                perf_prod_cycles,
    output logic [31:0]                perf_bp_cycles,
    output logic [31:0]                perf_starv_cycles,
    output logic [31:0]                perf_idle_cycles,
    output logic [31:0]                perf_beat_count,
    output logic [63:0]                perf_byte_count,
    output logic [31:0]                perf_burst_count
);


    // =========================================================================
    // Instantiate AXI4 Master Write Monitor with Filtering
    // =========================================================================
    // -------------------------------------------------------------------------
    // Clock gating
    // -------------------------------------------------------------------------
    // Activity is derived from VALID signals and outstanding work ONLY. A peer's
    // READY must never appear in the activity term: a consumer that parks its
    // response-ready high while idle is behaving correctly, and folding that in
    // would pin this block permanently awake and defeat gating entirely.
    //
    // The request-side readys are masked to 0 while gated, so no transfer can be
    // accepted while the clock is stopped.
    //
    // Port valids alone are sufficient to cover a beat held inside the block:
    // the upstream valid covers it until the cycle it is accepted, and the
    // downstream valid covers it from the cycle it is presented, which the skid
    // buffer does on the very next cycle and holds for as long as the consumer
    // back-pressures. There is therefore no window in which a beat is inside the
    // block with every port valid low, so no beat can be stranded by the clock
    // stopping. val/amba/test_mon_cg_gating.py phase 5 asserts this directly.
    logic gated_aclk;
    logic user_valid, axi_valid;
    logic w_monbus_valid;
    logic int_awready, int_wready, int_bready, int_busy;

    assign user_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bvalid || int_busy ||
                        w_monbus_valid || (|active_transactions);
    assign axi_valid  = m_axi_awvalid || m_axi_wvalid || m_axi_bvalid;

    assign fub_axi_awready  = cg_gating ? 1'b0 : int_awready;
    assign fub_axi_wready   = cg_gating ? 1'b0 : int_wready;
    assign m_axi_bready = cg_gating ? 1'b0 : int_bready;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    axi4_master_wr_mon #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH),
        .USE_MONITOR             (USE_MONITOR),
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
        .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
        .ADDR_FILTER_ENABLE      (ADDR_FILTER_ENABLE),
        .ID_FILTER_ENABLE        (ID_FILTER_ENABLE),
        .ID_MATCH_BASE           (ID_MATCH_BASE),
        .ID_MATCH_COUNT          (ID_MATCH_COUNT),
        .N_ADDR_RANGES           (N_ADDR_RANGES)
    ) axi4_master_wr_mon_inst (
        .aclk                    (gated_aclk),
        .aresetn                 (aresetn),
        .cam_clear               (cam_clear),
        .i_mon_time              (i_mon_time),

        // Slave AXI Interface (Input Side)
        .fub_axi_awid            (fub_axi_awid),
        .fub_axi_awaddr          (fub_axi_awaddr),
        .fub_axi_awlen           (fub_axi_awlen),
        .fub_axi_awsize          (fub_axi_awsize),
        .fub_axi_awburst         (fub_axi_awburst),
        .fub_axi_awlock          (fub_axi_awlock),
        .fub_axi_awcache         (fub_axi_awcache),
        .fub_axi_awprot          (fub_axi_awprot),
        .fub_axi_awqos           (fub_axi_awqos),
        .fub_axi_awregion        (fub_axi_awregion),
        .fub_axi_awuser          (fub_axi_awuser),
        .fub_axi_awvalid         (fub_axi_awvalid),
        .fub_axi_awready         (int_awready),

        .fub_axi_wdata           (fub_axi_wdata),
        .fub_axi_wstrb           (fub_axi_wstrb),
        .fub_axi_wlast           (fub_axi_wlast),
        .fub_axi_wuser           (fub_axi_wuser),
        .fub_axi_wvalid          (fub_axi_wvalid),
        .fub_axi_wready          (int_wready),

        .fub_axi_bid             (fub_axi_bid),
        .fub_axi_bresp           (fub_axi_bresp),
        .fub_axi_buser           (fub_axi_buser),
        .fub_axi_bvalid          (fub_axi_bvalid),
        .fub_axi_bready          (fub_axi_bready),

        // Master AXI Interface (Output Side)
        .m_axi_awid              (m_axi_awid),
        .m_axi_awaddr            (m_axi_awaddr),
        .m_axi_awlen             (m_axi_awlen),
        .m_axi_awsize            (m_axi_awsize),
        .m_axi_awburst           (m_axi_awburst),
        .m_axi_awlock            (m_axi_awlock),
        .m_axi_awcache           (m_axi_awcache),
        .m_axi_awprot            (m_axi_awprot),
        .m_axi_awqos             (m_axi_awqos),
        .m_axi_awregion          (m_axi_awregion),
        .m_axi_awuser            (m_axi_awuser),
        .m_axi_awvalid           (m_axi_awvalid),
        .m_axi_awready           (m_axi_awready),

        .m_axi_wdata             (m_axi_wdata),
        .m_axi_wstrb             (m_axi_wstrb),
        .m_axi_wlast             (m_axi_wlast),
        .m_axi_wuser             (m_axi_wuser),
        .m_axi_wvalid            (m_axi_wvalid),
        .m_axi_wready            (m_axi_wready),

        .m_axi_bid               (m_axi_bid),
        .m_axi_bresp             (m_axi_bresp),
        .m_axi_buser             (m_axi_buser),
        .m_axi_bvalid            (m_axi_bvalid),
        .m_axi_bready            (int_bready),

        // Monitor Configuration
        .cfg_monitor_enable      (cfg_monitor_enable),
        .cfg_error_enable        (cfg_error_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_compl_enable         (cfg_compl_enable),
        .cfg_threshold_enable         (cfg_threshold_enable),
        .cfg_debug_enable         (cfg_debug_enable),
        .cfg_timeout_cycles      (cfg_timeout_cycles),
        .cfg_freq_sel            (cfg_freq_sel),
        .cfg_latency_threshold   (cfg_latency_threshold),

        // AXI Protocol Filtering Configuration
        .cfg_axi_pkt_mask        (cfg_axi_pkt_mask),
        .cfg_axi_err_select      (cfg_axi_err_select),
        .cfg_axi_error_mask      (cfg_axi_error_mask),
        .cfg_axi_timeout_mask    (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask      (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask     (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask       (cfg_axi_perf_mask),
        .cfg_axi_addr_mask       (cfg_axi_addr_mask),
        .cfg_axi_debug_mask      (cfg_axi_debug_mask),

        // Address-range checker configuration
        .cfg_addr_check_enable   (cfg_addr_check_enable),
        .cfg_addr_range_enable   (cfg_addr_range_enable),
        .cfg_addr_range_low      (cfg_addr_range_low),
        .cfg_addr_range_high     (cfg_addr_range_high),
        .cfg_addr_filter_enable  (cfg_addr_filter_enable),
        .cfg_addr_filter_low     (cfg_addr_filter_low),
        .cfg_addr_filter_high    (cfg_addr_filter_high),
        .cfg_id_filter_enable    (cfg_id_filter_enable),
        .cfg_id_match_base       (cfg_id_match_base),
        .cfg_id_match_count      (cfg_id_match_count),

        // Monitor Bus Output
        .monbus_valid            (w_monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),
        .monbus_timestamp        (monbus_timestamp),

        // Status outputs
        .busy                    (int_busy),
        .active_transactions     (active_transactions),
        .error_count             (error_count),
        .transaction_count       (transaction_count),

        // Configuration error flags
        .cfg_conflict_error      (cfg_conflict_error),

        // Performance window control + status (Stage A) + buckets (Stage B).
        .cfg_start_event_sel     (cfg_start_event_sel),
        .cfg_end_event_sel       (cfg_end_event_sel),
        .cfg_start_trigger       (cfg_start_trigger),
        .cfg_end_trigger         (cfg_end_trigger),
        .cfg_window_force_close  (cfg_window_force_close),
        .window_active           (window_active),
        .window_cycles           (window_cycles),
        .perf_prod_cycles        (perf_prod_cycles),
        .perf_bp_cycles          (perf_bp_cycles),
        .perf_starv_cycles       (perf_starv_cycles),
        .perf_idle_cycles        (perf_idle_cycles),
        .perf_beat_count         (perf_beat_count),
        .perf_byte_count         (perf_byte_count),
        .perf_burst_count        (perf_burst_count),
        // Observability tap on the inner monitor's backpressure. Connected
        // EXPLICITLY rather than omitted: an omitted pin is PINMISSING,
        // which Verilator escalates to an error, and that is what kept the
        // four axil4 _cg builds from compiling at all. Left empty because
        // the _cg wrapper does not re-export it.
        /* verilator lint_off PINCONNECTEMPTY */
        .debug_block_ready       ()
        /* verilator lint_on PINCONNECTEMPTY */

    );

    // Monitor liveness terms (TASK-070):
    //   w_monbus_valid -- a packet parked on the monitor bus is outstanding
    //     work; it holds the block awake (and re-wakes it) so the reporter
    //     can retire the handshake. Without it the clock stops with valid
    //     frozen high and an ungated consumer re-accepts the SAME packet
    //     every cycle.
    //   |active_transactions -- the monitor CAM's occupancy. An entry stays
    //     valid until its packet is marked into the reporter FIFO, and the
    //     registered count lags one cycle past that, meeting monbus_valid's
    //     assertion; without this term the clock can stop inside the
    //     reporter's emission window (retire -> FIFO -> output register,
    //     ~2-4 cycles) and the packet strands with valid never risen --
    //     nothing left to wake the block until unrelated traffic.
    //   The !cg_gating mask on the external valid covers the one-cycle
    //     overlap where gating asserts on the same edge a packet arrives
    //     (wake takes a cycle): the consumer never sees a valid the stopped
    //     reporter could not retire. The mask only defers valid's rise,
    //     never truncates a visible valid, because once the pending terms
    //     are high gating cannot engage.
    // val/amba/test_mon_cg_gating.py phase 6 asserts exactly-once delivery
    // of exactly the packets generated -- no duplicates, no stranding.
    assign monbus_valid = w_monbus_valid && !cg_gating;

    assign busy = int_busy;

endmodule : axi4_master_wr_mon_cg
