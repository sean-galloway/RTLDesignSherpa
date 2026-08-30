// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_mon
// Purpose: Axi4 Master Wr Mon module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Write with Integrated Filtered Monitoring
 *
 * This module combines the standard axi4_master_wr module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring with configurable packet filtering.
 *
 * Features:
 * - Instantiates axi4_master_wr for core AXI4 functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - 3-level filtering hierarchy: packet type, error routing, individual event masking
 * - Monitor bus output for system-level monitoring
 * - Configurable monitoring and filtering parameters
 * - Error detection and timeout monitoring
 * - Performance metrics collection
 * - Configuration validation with error flagging
 * - USE_MONITOR: synthesis-time enable. When 0, the monitor is omitted and
 *   its outputs are tied to safe non-blocking defaults so the wrapped
 *   axi4_master_wr core runs unencumbered (for FPGA / production / PPA
 *   characterization). Upstream macro wrappers may OR a force-on signal.
 */
module axi4_master_wr_mon
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (passed through to axi4_master_wr)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Monitor parameters (literals sized to 32 bits for Verilator int-parameter width check)
    // aclk frequency in MHz -- picks the counter_freq_invariant LUT entry that
    // yields a ~1 us tick, which is the unit monitor timeouts are expressed in.
    // Was hardwired to index 1 (19 MHz) with the comment "use aclk frequency";
    // on a 100 MHz design that made every timeout ~5x shorter than requested.
    parameter int ACLK_MHZ          = 100,
    // CFI LUT bounds. The default MIN==MAX==ACLK_MHZ makes every entry equal
    // ACLK_MHZ, so the 1 us tick is exact for ANY cfg_freq_sel index. Give
    // these a real MIN..MAX range to make cfg_freq_sel actually select.
    parameter int CFI_MIN_FREQ_MHZ  = ACLK_MHZ,
    parameter int CFI_MAX_FREQ_MHZ  = ACLK_MHZ,
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,  // per-range flavor: 0=debug/match, 1=error/allowlist-miss
    parameter logic [7:0]  UNIT_ID  = 8'h01,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h000B,  // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 16,    // Maximum outstanding transactions to monitor
    // ID-range filter, passed through to axi_monitor_base. Default OFF ->
    // bit-identical to before. See axi_monitor_base for why this exists:
    // several monitors snooping one ID-multiplexed bus, each owning a slice,
    // so no single transaction table has to hold the whole concurrency.
    // Transaction-table shaping, forwarded to axi_monitor_trans_mgr.
    // Defaults reproduce today's behaviour exactly; see that module for the
    // AW-order queue and the bank sizing rule.
    parameter bit USE_WDATA_ORDER_Q      = 1'b0,
    parameter int NUM_BANKS              = 1,
    parameter bit ID_FILTER_ENABLE       = 1'b0,

    // Address-range packet filter (TASK-015). Default 0 -> inert and the
    // build is bit-identical. See axi_monitor_trans_mgr for why this filters
    // at REPORT time rather than at admission.
    parameter bit ADDR_FILTER_ENABLE     = 1'b0,
    parameter int ID_MATCH_BASE          = 0,
    parameter int ID_MATCH_COUNT         = 0,
    // Active-transaction threshold packet trip point (used when
    // cfg_threshold_enable=1). Previously hardwired, which either spammed
    // threshold packets (table larger than the hardwire) or made the feature
    // unreachable (table smaller). Scales with the table by default.
    parameter int ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,

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

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,


    // Address-range packet filter configuration (active when
    // ADDR_FILTER_ENABLE=1). Inclusive [low, high]; a transaction whose
    // command address falls OUTSIDE the range has its packets suppressed.

    // Runtime ID filter (TASK-015). Overrides ID_MATCH_BASE/COUNT while
    // cfg_id_filter_enable is high; tied low it is bit-identical to the
    // parameter-only behaviour.
    input  logic                                                   cfg_id_filter_enable,
    input  logic [IW-1:0]                                          cfg_id_match_base,
    input  logic [IW:0]                                            cfg_id_match_count,
    input  logic                                                   cfg_addr_filter_enable,
    input  logic [AW-1:0]                                          cfg_addr_filter_low,
    input  logic [AW-1:0]                                          cfg_addr_filter_high,
    // Performance window control (Stage A of perfmon RFC). Wire to the
    // integrating block's perfmon CSR; tie 3'b111 + 1'b0 if perfmon is
    // unused at this instance.
    input  logic [2:0]                              cfg_start_event_sel,
    input  logic [2:0]                              cfg_end_event_sel,
    input  logic                                    cfg_start_trigger,
    input  logic                                    cfg_end_trigger,
    input  logic                                    cfg_window_force_close,

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
    output logic [15:0]                error_count,             // Total error count (not available from base monitor)
    output logic [31:0]                transaction_count,       // Total transaction count (not available from base monitor)
    // Monitor backpressure, brought out for observability. This is the SAME
    // net that gates the upstream command handshake below -- not a copy, not a
    // re-derivation. It is a port and not an internal signal because a
    // hierarchical reference to it is not reliably observable: the sby harness
    // saw `dut.w_block_ready` elaborate as an implicitly-declared FREE wire,
    // which made the gating properties VACUOUS, and a cocotb probe of a
    // hierarchy path that does not resolve returns None and passes
    // unconditionally. Both failure modes are silent, and both hide the defect
    // the check exists to catch. A validated contract needs an observable
    // signal. Drives nothing internally; leave unconnected if unused.
    output logic                       debug_block_ready,

    // Performance window status (Stage A of perfmon RFC). Reflects the
    // internal axi_monitor_base state machine.
    output logic                       window_active,
    output logic [31:0]                window_cycles,

    // Performance cycle buckets + counters (Stage B of perfmon RFC).
    // Sample at WIN_CLOSING (drive cfg_end_trigger or wait for the
    // configured end event, then read on the cycle window_active=0).
    output logic [31:0]                perf_prod_cycles,
    output logic [31:0]                perf_bp_cycles,
    output logic [31:0]                perf_starv_cycles,
    output logic [31:0]                perf_idle_cycles,
    output logic [31:0]                perf_beat_count,
    output logic [63:0]                perf_byte_count,
    output logic [31:0]                perf_burst_count,

    // Configuration error flags
    output logic                       cfg_conflict_error       // Configuration conflict detected
);

    // -------------------------------------------------------------------------
    // Monitor backpressure plumbing (see master_rd_mon for full rationale)
    // -------------------------------------------------------------------------
    logic w_core_fub_axi_awready;
    logic w_block_ready;

    // BOTH ENDS OF THE HANDSHAKE, GATED BY THE SAME TERM.
    // Masking only the outward ready let the core keep seeing an
    // ungated valid: it accepted the command while the master was
    // told "not ready", the master held the same command on the bus,
    // and the core accepted it AGAIN every cycle until the table
    // drained. Backpressure became replay -- measured 49 commands in
    // and 367 accepted on the Genesys 2 STREAM build, and caught by
    // val/amba/test_axi_mon_block_ready.py once it was bound to the
    // slave wrappers. Gating the valid too makes a full table stall
    // the bus, which is the documented contract.
    logic w_gated_awvalid;
    assign w_gated_awvalid = fub_axi_awvalid & (w_block_ready | ~cfg_monitor_enable);

    // Observability tap for block_ready (see the port comment). Held to the
    // internal gating net so a testbench watching the port sees exactly what
    // the AR/AW gate sees.
    assign debug_block_ready = w_block_ready;

    // -------------------------------------------------------------------------
    // Instantiate AXI4 Master Write Core
    // -------------------------------------------------------------------------
    axi4_master_wr #(
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH)
    ) axi4_master_wr_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

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
        .fub_axi_awvalid         (w_gated_awvalid),
        .fub_axi_awready         (w_core_fub_axi_awready),  // gated below

        .fub_axi_wdata           (fub_axi_wdata),
        .fub_axi_wstrb           (fub_axi_wstrb),
        .fub_axi_wlast           (fub_axi_wlast),
        .fub_axi_wuser           (fub_axi_wuser),
        .fub_axi_wvalid          (fub_axi_wvalid),
        .fub_axi_wready          (fub_axi_wready),

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
        .m_axi_bready            (m_axi_bready),

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Monitor with Filtering (optional, USE_MONITOR)
    // -------------------------------------------------------------------------
    // -------------------------------------------------------------------------
    // cfg_monitor_enable -- master runtime gate.
    // When 0 the monitor is inert: command/data/response valids are gated off
    // (no allocation, no perf windows), the transaction CAM is held cleared
    // through the cam_clear path (so a re-enable starts from an empty table),
    // and block_ready is forced high at the wrapper gate below so a disabled
    // monitor can never stall the datapath. When 1: normal operation.
    //
    // cfg_timeout_cycles -- unified coarse timeout control: a MICROSECOND
    // count passed through at FULL 16-bit width (see the assign below and
    // its comment). The 4-bit saturating encoding this block once described
    // is retired -- deleted here so the docs cannot be re-corrupted from it
    // (axi4/axi5 qc round_20, RTL item C).
    // -------------------------------------------------------------------------
    logic        w_mon_cmd_valid;
    logic        w_mon_data_valid;
    logic        w_mon_resp_valid;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;

    assign w_mon_cmd_valid  = m_axi_awvalid & cfg_monitor_enable;
    assign w_mon_data_valid = m_axi_wvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = m_axi_bvalid & cfg_monitor_enable;
    // cfg_timeout_cycles is a MICROSECOND count (timer_tick = 1 us from
    // counter_freq_invariant), passed through at full width. It used to be
    // squashed into 4 bits here:
    //     (|cfg_timeout_cycles[15:4]) ? 4'hF : cfg_timeout_cycles[3:0]
    // which silently saturated every value >= 16 to 15 us, so the host's
    // range collapsed and two very different requests produced identical
    // hardware. 16 bits => 65535 us ~= 65 ms.
    // 0 means "effectively never" (max), NOT "time out immediately" -- an
    // unconfigured register must not fire timeouts on every transaction. That
    // special case was in the original expression and is kept; what is gone is
    // the saturation of everything else down to 4 bits.
    assign w_timeout_cnt    = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF
                            : cfg_timeout_cycles;

    if (USE_MONITOR) begin : gen_monitor
        axi_monitor_filtered #(
            .CFI_MIN_FREQ_MHZ        (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ        (CFI_MAX_FREQ_MHZ),
            .UNIT_ID                 (UNIT_ID),
            .AGENT_ID                (AGENT_ID),
            .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
            .USE_WDATA_ORDER_Q       (USE_WDATA_ORDER_Q),
            .NUM_BANKS               (NUM_BANKS),
            .ID_FILTER_ENABLE        (ID_FILTER_ENABLE),
            .ADDR_FILTER_ENABLE      (ADDR_FILTER_ENABLE),
            .ID_MATCH_BASE           (ID_MATCH_BASE),
            .ID_MATCH_COUNT          (ID_MATCH_COUNT),
            .ADDR_WIDTH              (AW),
            .ID_WIDTH                (IW),
            .IS_READ                 (1'b0),             // This is a write monitor
            .IS_AXI                  (1'b1),             // AXI4 protocol
            .ENABLE_PERF_PACKETS     (1'b1),
            .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
            .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
            .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
            .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
            .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
            .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
            .ENABLE_DEBUG_MODULE     (1'b0),
            .ENABLE_FILTERING        (ENABLE_FILTERING),
            .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES           (N_ADDR_RANGES),
            .ADDR_RANGE_IS_ERROR     (ADDR_RANGE_IS_ERROR)
        ) axi_monitor_inst (
            .aclk                    (aclk),
            .aresetn                 (aresetn),
            .clear                   (cam_clear | ~cfg_monitor_enable),
            .i_mon_time              (i_mon_time),

            // Command interface (AW channel)
            .cmd_addr                (m_axi_awaddr),
            .cmd_id                  (m_axi_awid),
            .cmd_len                 (m_axi_awlen),
            .cmd_size                (m_axi_awsize),
            .cmd_burst               (m_axi_awburst),
            .cmd_valid               (w_mon_cmd_valid),
            .cmd_ready               (m_axi_awready),

            // Data interface (W channel)
            .data_id                 (m_axi_awid),       // Use AW ID for write data
            .data_last               (m_axi_wlast),
            .data_resp               (2'b00),            // No response in W channel
            .data_valid              (w_mon_data_valid),
            .data_ready              (m_axi_wready),

            // Response interface (B channel)
            .resp_id                 (m_axi_bid),
            .resp_code               (m_axi_bresp),
            .resp_valid              (w_mon_resp_valid),
            .resp_ready              (m_axi_bready),

            // Configuration
            // cfg_freq_sel selects the counter_freq_invariant LUT entry. With the
            // default CFI_MIN==CFI_MAX==ACLK_MHZ every entry equals ACLK_MHZ, so any
            // index gives an exact 1 us tick; give the CFI a real MIN..MAX range for
            // this input to actually select a frequency.
            .cfg_freq_sel            (cfg_freq_sel),
            .cfg_addr_cnt            (w_timeout_cnt),
            .cfg_data_cnt            (w_timeout_cnt),
            .cfg_resp_cnt            (w_timeout_cnt),
            .cfg_error_enable        (cfg_error_enable),
            .cfg_compl_enable        (cfg_compl_enable),
            .cfg_threshold_enable    (cfg_threshold_enable),
            .cfg_timeout_enable      (cfg_timeout_enable),
            .cfg_perf_enable         (cfg_perf_enable),
            .cfg_debug_enable        (cfg_debug_enable),
            .cfg_debug_level         (4'h0),
            .cfg_debug_mask          (16'h0),
            .cfg_active_trans_threshold(16'(ACTIVE_TRANS_THRESHOLD)),
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

            .cfg_id_filter_enable    (cfg_id_filter_enable),

            .cfg_id_match_base       (cfg_id_match_base),

            .cfg_id_match_count      (cfg_id_match_count),

            .cfg_addr_filter_enable  (cfg_addr_filter_enable),
            .cfg_addr_filter_low     (cfg_addr_filter_low),
            .cfg_addr_filter_high    (cfg_addr_filter_high),
            // Performance window control (Stage A of perfmon RFC).
            // Wrapper-level ports pass straight through; the integrating
            // block ties them off (3'b111 + 0s) when perfmon is unused.
            .cfg_start_event_sel     (cfg_start_event_sel),
            .cfg_end_event_sel       (cfg_end_event_sel),
            .cfg_start_trigger       (cfg_start_trigger),
            .cfg_end_trigger         (cfg_end_trigger),
            .cfg_window_force_close  (cfg_window_force_close),

            // Monitor bus output
            .monbus_valid            (monbus_valid),
            .monbus_ready            (monbus_ready),
            .monbus_packet           (monbus_packet),
            .monbus_timestamp        (monbus_timestamp),

            // Status outputs
            // block_ready stalls new AWs at fub_axi_awready when the monitor
            // FIFO is full (wire ANDed into the wrapper output below).
            .block_ready             (w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy                    (),                    // Unused (using master busy)
            /* verilator lint_on PINCONNECTEMPTY */
            .window_active           (window_active),
            .window_cycles           (window_cycles),
            .perf_prod_cycles        (perf_prod_cycles),
            .perf_bp_cycles          (perf_bp_cycles),
            .perf_starv_cycles       (perf_starv_cycles),
            .perf_idle_cycles        (perf_idle_cycles),
            .perf_beat_count         (perf_beat_count),
            .perf_byte_count         (perf_byte_count),
            .perf_burst_count        (perf_burst_count),
            .perf_completed_count    (w_perf_completed_count),
            .perf_error_count        (w_perf_error_count),
            .active_count            (active_transactions),

            // Configuration error flags
            .cfg_conflict_error      (cfg_conflict_error)
        );
    end else begin : gen_no_monitor
        assign monbus_valid        = 1'b0;
        assign monbus_packet       = '0;
        assign monbus_timestamp    = '0;
        assign active_transactions = 8'h0;
        assign cfg_conflict_error  = 1'b0;
        assign w_block_ready       = 1'b1;
        assign w_perf_completed_count = 16'h0;
        assign w_perf_error_count     = 16'h0;
        // Perfmon disabled when ENABLE_MONITOR=0.
        assign window_active       = 1'b0;
        assign window_cycles       = 32'h0;
        assign perf_prod_cycles    = 32'h0;
        assign perf_bp_cycles      = 32'h0;
        assign perf_starv_cycles   = 32'h0;
        assign perf_idle_cycles    = 32'h0;
        assign perf_beat_count     = 32'h0;
        assign perf_byte_count     = 64'h0;
        assign perf_burst_count    = 32'h0;
    end

    // Gate the upstream AW handshake on monitor block_ready.
    assign fub_axi_awready = w_core_fub_axi_awready &
           (w_block_ready | ~cfg_monitor_enable);  // disabled monitor never stalls

    // error_count / transaction_count: driven from the base monitor's
    // lifetime reporter counters (axi_monitor_reporter_perf). They count
    // packets actually EMITTED (marked into the reporter FIFO): error_count
    // covers error+timeout packets, transaction_count covers completion
    // packets. Zero when USE_MONITOR=0 or ENABLE_PERF_LOGIC=0.
    assign error_count       = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

`ifdef FORMAL
    // ------------------------------------------------------------------------
    // Wrapper gating contract (in-RTL formal properties, flattened into the
    // proof by sv2v --define=FORMAL). These live HERE and not in the sby
    // harness because a plain-Verilog harness cannot form hierarchical
    // references: `dut.w_block_ready` elaborated as an implicitly-declared
    // FREE wire, which made the old harness-side P6/P7 gating properties
    // vacuous (guard over a free variable). In-module, the real nets are
    // visible and the contract is enforceable:
    //   * enabled + blocked -> upstream ready is forced low
    //   * disabled          -> the wrapper is transparent (a disabled
    //                          monitor must never stall the datapath)
    // ------------------------------------------------------------------------
    always @(*) begin
        if (aresetn && cfg_monitor_enable && !w_block_ready)
            ap_block_ready_gating: assert (!fub_axi_awready);
        if (aresetn && !cfg_monitor_enable)
            ap_disabled_never_stalls: assert (fub_axi_awready == w_core_fub_axi_awready);
    end
`endif

endmodule : axi4_master_wr_mon

