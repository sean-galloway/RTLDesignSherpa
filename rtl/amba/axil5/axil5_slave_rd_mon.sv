// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_rd_mon
// Purpose: Axil4 Slave Rd Mon module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXIL4 Slave Read with Integrated Filtered Monitoring
 *
 * This module combines the standard axil5_slave_rd module with an axi_monitor_filtered
 * to provide comprehensive transaction monitoring for AXI4-Lite slave read operations.
 *
 * Features:
 * - Instantiates axil5_slave_rd for core AXIL4 slave functionality
 * - Instantiates axi_monitor_filtered for transaction monitoring with filtering
 * - Simplified monitoring for AXI4-Lite (single-beat, no burst, no ID reordering)
 * - Ocelus bus output for system-level monitoring
 * - Error detection and timeout monitoring
 * - Configuration validation with error flagging
 *
 * Key Simplifications vs AXI4:
 * - No burst support (all transactions are single-beat)
 * - Ocelus sees the AXI5-Lite ID (same-ID responses in order, other IDs may reorder)
 * - Reduced MAX_TRANSACTIONS (typically 4-8 vs 16-32)
 * - No ARLEN, ARSIZE, ARBURST, RLAST signals
 *
 * AXI5-Lite variant. Derived from the AXI4-Lite wrapper of the same name: the
 * ocelus plumbing is identical. What this wrapper adds is the AXI5-Lite
 * transaction ID (ID_WIDTH) and the optional-signal pass-through (USER, TRACE,
 * POISON, each behind its own ENABLE_* parameter) to the inner transport
 * module. AxLOCK, AxMPAM, AxMECID, AxNSAID and xLOOP are not present on
 * AXI5-Lite (IHI 0022L Table B2.2) and are not carried.
 *
 * The ocelus sees handshakes, addresses, responses and timing, and -- since
 * amba #104 -- the AXI5-Lite ID: AxID/BID/RID drive its command and response
 * IDs, so a Subordinate that reorders responses across IDs (permitted on
 * AXI5-Lite, IHI 0022L B2.1.5) has each response paired with its own
 * transaction. W carries no ID and is attributed in AW order (A5.5). It
 * does not validate POISON.
 *
 * Port names match the AXI4-Lite wrapper exactly, including the `_axil_`
 * infix, so the AXIL5 BFMs -- which are the AXIL4 BFMs with the component
 * factories swapped -- resolve the same signal names against either family.
 */
module axil5_slave_rd_mon
    import ocelus_pkg::*;
#(
    // AXIL4 Slave parameters (passed through to axil5_slave_rd)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXIL_ADDR_WIDTH   = 32,
    parameter int AXIL_DATA_WIDTH   = 32,

    // Ocelus parameters (literals sized to 32 bits for Verilator int-parameter width check)
    // aclk frequency in MHz -- picks the counter_freq_invariant LUT entry that
    // yields a ~1 us tick, which is the unit ocelus timeouts are expressed in.
    // Was hardwired to index 1 (19 MHz) with the comment "use aclk frequency";
    // on a 100 MHz design that made every timeout ~5x shorter than requested.
    parameter int ACLK_MHZ          = 100,
    // CFI LUT bounds. The default MIN==MAX==ACLK_MHZ makes every entry equal
    // ACLK_MHZ, so the 1 us tick is exact for ANY cfg_freq_sel index. Give
    // these a real MIN..MAX range to make cfg_freq_sel actually select.
    parameter int CFI_MIN_FREQ_MHZ  = ACLK_MHZ,
    parameter int CFI_MAX_FREQ_MHZ  = ACLK_MHZ,
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit ocelus, tie outputs
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter logic [7:0]  UNIT_ID  = 8'h02,     // 8-bit Unit ID for ocelus packets
    parameter logic [15:0] AGENT_ID = 16'h0014,    // 16-bit Agent ID for ocelus packets
    parameter int MAX_TRANSACTIONS  = 8,     // Maximum outstanding transactions (reduced for AXIL)
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

    // AXI5-Lite ID and optional signal widths
    // AWID/BID and ARID/RID width (IHI 0022L Table A5.2: 0..32).
    // This is a Subordinate-side interface, where Table B2.2 makes the ID
    // mandatory (code YS), so the legal range here is 1..32.
    parameter int ID_WIDTH           = 4,
    parameter int USER_WIDTH         = 4,

    // AXI5-Lite optional signal groups. Passed straight through to the inner
    // transport module; the ocelus never sees these signals.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_POISON      = 1,

    // Short params
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    // ID port width: ID_WIDTH, or a 1-bit placeholder when ID_WIDTH = 0
    parameter int IW       = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int UW       = USER_WIDTH,
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    input  logic                       cam_clear,  // sync clear of the ocelus trans CAM

    // Slave AXIL Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]              s_axil_arid,
    input  logic [AW-1:0]              s_axil_araddr,
    input  logic [2:0]                 s_axil_arprot,
    input  logic [UW-1:0]           s_axil_aruser,
    input  logic                    s_axil_artrace,
    input  logic                       s_axil_arvalid,
    output logic                       s_axil_arready,

    // Read data channel (R)
    output logic [IW-1:0]              s_axil_rid,
    output logic [DW-1:0]              s_axil_rdata,
    output logic [1:0]                 s_axil_rresp,
    output logic [UW-1:0]           s_axil_ruser,
    output logic                    s_axil_rtrace,
    output logic [PW-1:0]           s_axil_rpoison,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    // Master AXIL Interface (Output Side to backend/memory)
    // Read address channel (AR)
    output logic [IW-1:0]              fub_axil_arid,
    output logic [AW-1:0]              fub_axil_araddr,
    output logic [2:0]                 fub_axil_arprot,
    output logic [UW-1:0]           fub_axil_aruser,
    output logic                    fub_axil_artrace,
    output logic                       fub_axil_arvalid,
    input  logic                       fub_axil_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              fub_axil_rid,
    input  logic [DW-1:0]              fub_axil_rdata,
    input  logic [1:0]                 fub_axil_rresp,
    input  logic [UW-1:0]           fub_axil_ruser,
    input  logic                    fub_axil_rtrace,
    input  logic [PW-1:0]           fub_axil_rpoison,
    input  logic                       fub_axil_rvalid,
    output logic                       fub_axil_rready,

    // Ocelus Configuration
    input  logic                       cfg_monitor_enable,      // Enable monitoring
    input  logic                       cfg_error_enable,        // Enable error detection
    input  logic                       cfg_timeout_enable,      // Enable timeout detection
    input  logic                       cfg_perf_enable,         // Enable performance monitoring
    input  logic                       cfg_compl_enable,     // Enable completion packets
    input  logic                       cfg_threshold_enable, // Enable threshold packets
    input  logic                       cfg_debug_enable,     // Enable debug packets
    input  logic [15:0]                cfg_timeout_cycles,      // Timeout threshold in MICROSECONDS (1 us tick), despite the name
    input  logic [3:0]                 cfg_freq_sel,            // counter_freq_invariant LUT index
    input  logic [31:0]                cfg_latency_threshold,   // Latency threshold for alerts

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types
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
    input  logic                                                   cfg_addr_filter_enable,
    input  logic [AW-1:0]                                          cfg_addr_filter_low,
    input  logic [AW-1:0]                                          cfg_addr_filter_high,
    // Free-running ocelus-time broadcast from the monbus_group family
    input  ocelus_common_pkg::monbus_timestamp_t   i_mon_time,

    // Ocelus Bus Output
    output logic                                    monbus_valid,            // Ocelus bus valid
    input  logic                                    monbus_ready,            // Ocelus bus ready
    output ocelus_common_pkg::monitor_packet_t     monbus_packet,           // Ocelus packet (128-bit)
    output ocelus_common_pkg::monbus_timestamp_t   monbus_timestamp,        // Side-band sampled time

    // Status outputs for clock gating and monitoring
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count
    // Ocelus backpressure, brought out for observability. This is the SAME
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

    // Configuration error flags
    output logic                       cfg_conflict_error,       // Configuration conflict detected

    // Performance window control (Stage A of perfmon RFC). Wrapper-level
    // ports pass straight through; the integrating block ties them off
    // (3'b111 + 0s) when perfmon is unused.
    input  logic [2:0]                 cfg_start_event_sel,
    input  logic [2:0]                 cfg_end_event_sel,
    input  logic                       cfg_start_trigger,
    input  logic                       cfg_end_trigger,
    input  logic                       cfg_window_force_close,

    // Performance window status (Stage A) + cycle buckets + counters (Stage B).
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

    // ---------------------------------------------------------------------
    // Elaboration-time parameter guard (the one sanctioned in-RTL check; see
    // vault/handbook/design/no-assertions-in-rtl.md). Checks nothing at run
    // time.
    //   AXIL_DATA_WIDTH: AXI5-Lite takes any AXI DATA_WIDTH -- 8, 16, 32, 64,
    //     128, 256, 512 or 1024 (IHI 0022L Table A3.19; Table B2.4 adds no
    //     AXI5-Lite constraint, unlike AXI4-Lite's 32/64 of IHI 0022H B1.1.2).
    //   ID_WIDTH: 1..32 (Table A5.2). Subordinate-side: the ID is mandatory (Table B2.2, YS).
    // ---------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (!(AXIL_DATA_WIDTH == 8   || AXIL_DATA_WIDTH == 16  ||
              AXIL_DATA_WIDTH == 32  || AXIL_DATA_WIDTH == 64  ||
              AXIL_DATA_WIDTH == 128 || AXIL_DATA_WIDTH == 256 ||
              AXIL_DATA_WIDTH == 512 || AXIL_DATA_WIDTH == 1024))
            $fatal(1, "axil5_slave_rd_mon: AXIL_DATA_WIDTH=%0d is not a legal AXI5-Lite data width (8..1024, power of 2; IHI 0022L A3.2)",
                   AXIL_DATA_WIDTH);
        if (ID_WIDTH < 1 || ID_WIDTH > 32)
            $fatal(1, "axil5_slave_rd_mon: ID_WIDTH=%0d out of range 1..32 (IHI 0022L Table A5.2; a Subordinate must carry the ID)",
                   ID_WIDTH);
        // The full ocelus keys its table on at most 8 ID bits
        // (axi_monitor_trans_mgr); since amba #104 it sees the real ID.
        if (USE_MONITOR && ID_WIDTH > 8)
            $fatal(1, "axil5_slave_rd_mon: ID_WIDTH=%0d -- the full ocelus tracks at most 8 ID bits (axi_monitor_trans_mgr); use ID_WIDTH <= 8, or the _monlite wrapper",
                   ID_WIDTH);
    end
`endif

    // -------------------------------------------------------------------------
    // Ocelus backpressure plumbing (see axi4_master_rd_mon for full rationale)
    // -------------------------------------------------------------------------
    logic w_core_s_axil_arready;
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
    logic w_gated_arvalid;
    assign w_gated_arvalid = s_axil_arvalid & (w_block_ready | ~cfg_monitor_enable);

    // Observability tap for block_ready (see the port comment). Held to the
    // internal gating net so a testbench watching the port sees exactly what
    // the AR/AW gate sees.
    assign debug_block_ready = w_block_ready;

    // -------------------------------------------------------------------------
    // Instantiate AXIL4 Slave Read Core
    // -------------------------------------------------------------------------
    axil5_slave_rd #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXIL_ADDR_WIDTH         (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH         (AXIL_DATA_WIDTH),
        .ID_WIDTH           (ID_WIDTH),
        .USER_WIDTH         (USER_WIDTH),
        .ENABLE_USER        (ENABLE_USER),
        .ENABLE_TRACE       (ENABLE_TRACE),
        .ENABLE_POISON      (ENABLE_POISON)
    ) axil5_slave_rd_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Slave AXIL Interface (Input Side)
        .s_axil_arid             (s_axil_arid),
        .s_axil_araddr           (s_axil_araddr),
        .s_axil_arprot           (s_axil_arprot),
        .s_axil_aruser          (s_axil_aruser),
        .s_axil_artrace         (s_axil_artrace),
        .s_axil_arvalid          (w_gated_arvalid),
        .s_axil_arready          (w_core_s_axil_arready),    // gated below

        .s_axil_rid               (s_axil_rid),
        .s_axil_rdata            (s_axil_rdata),
        .s_axil_rresp            (s_axil_rresp),
        .s_axil_ruser           (s_axil_ruser),
        .s_axil_rtrace          (s_axil_rtrace),
        .s_axil_rpoison         (s_axil_rpoison),
        .s_axil_rvalid           (s_axil_rvalid),
        .s_axil_rready           (s_axil_rready),

        // Master AXIL Interface (Output Side)
        .fub_arid                (fub_axil_arid),
        .fub_araddr              (fub_axil_araddr),
        .fub_arprot              (fub_axil_arprot),
        .fub_aruser             (fub_axil_aruser),
        .fub_artrace            (fub_axil_artrace),
        .fub_arvalid             (fub_axil_arvalid),
        .fub_arready             (fub_axil_arready),

        .fub_rid                  (fub_axil_rid),
        .fub_rdata               (fub_axil_rdata),
        .fub_rresp               (fub_axil_rresp),
        .fub_ruser              (fub_axil_ruser),
        .fub_rtrace             (fub_axil_rtrace),
        .fub_rpoison            (fub_axil_rpoison),
        .fub_rvalid              (fub_axil_rvalid),
        .fub_rready              (fub_axil_rready),

        .busy                    (busy)
    );

    // -------------------------------------------------------------------------
    // Instantiate AXI Ocelus with Filtering (Monitoring slave side, optional)
    // -------------------------------------------------------------------------
    // -------------------------------------------------------------------------
    // cfg_monitor_enable -- master runtime gate.
    // When 0 the ocelus is inert: command/data/response valids are gated off
    // (no allocation, no perf windows), the transaction CAM is held cleared
    // through the cam_clear path (so a re-enable starts from an empty table),
    // and block_ready is forced high at the wrapper gate below so a disabled
    // ocelus can never stall the datapath. When 1: normal operation.
    //
    // cfg_timeout_cycles -- unified coarse timeout control.
    // The base ocelus's real knobs are 4-bit per-phase TICK counts
    // (cfg_addr/data/resp_cnt) measured in cfg_freq_sel-scaled timer ticks,
    // not raw cycles. Chosen encoding:
    //     16'h0     -> 4'hF   (legacy full-scale default, so integrations
    //                          that tie this port low keep old behavior)
    //     1..15     -> that many timer ticks per phase
    //     >15       -> saturates at 4'hF
    // All three phases share the value. This wrapper has no per-phase cnt
    // ports; if per-phase ports are ever added they take precedence over
    // this coarse control.
    // -------------------------------------------------------------------------
    logic        w_mon_cmd_valid;
    logic        w_mon_data_valid;
    logic        w_mon_resp_valid;
    logic [15:0] w_timeout_cnt;
    logic [15:0] w_perf_completed_count;
    logic [15:0] w_perf_error_count;
    // Monitor tap: the FUB-side (backend) handshake (owner rule: monitors always
    // tap the FUB side, for timing -- same as axi5_slave_rd_mon). block_ready
    // still gates the upstream bus handshake, so a full table stalls the bus;
    // the watchpoint trails the gate by the skid depth, which the monitor's
    // CMD_ENTRY_RESERVE admission margin covers.

    assign w_mon_cmd_valid  = fub_axil_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = fub_axil_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = fub_axil_rvalid & cfg_monitor_enable;
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
    // AXI5-Lite IDs to the ocelus (amba #104). ARID/RID exist on AXI5-Lite
    // and a Subordinate may return read data out of order across IDs (IHI
    // 0022L B2.1.5), so the ocelus matches each R to the oldest command of
    // the SAME ID, as on AXI4 -- with the ID tied 0 it paired every R with the
    // oldest command outstanding, whichever one the R answered.
    // The full ocelus keys on at most 8 ID bits: wider builds are rejected by
    // param_check above, and the clamp only lets elaboration reach that guard.
    localparam int MON_IW = (IW > 8) ? 8 : IW;
    logic [MON_IW-1:0] w_mon_cmd_id, w_mon_data_id;
    assign w_mon_cmd_id  = MON_IW'(fub_axil_arid);
    assign w_mon_data_id = MON_IW'(fub_axil_rid);

    if (USE_MONITOR) begin : gen_monitor
        axi_monitor_filtered #(
            .CFI_MIN_FREQ_MHZ        (CFI_MIN_FREQ_MHZ),
            .CFI_MAX_FREQ_MHZ        (CFI_MAX_FREQ_MHZ),
            .UNIT_ID                 (UNIT_ID),
            .AGENT_ID                (AGENT_ID),
            .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
            .USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q), .NUM_BANKS(NUM_BANKS),
            .ID_FILTER_ENABLE        (ID_FILTER_ENABLE),
            .ADDR_FILTER_ENABLE      (ADDR_FILTER_ENABLE),
            .ID_MATCH_BASE           (ID_MATCH_BASE),
            .ID_MATCH_COUNT          (ID_MATCH_COUNT),
            .ADDR_WIDTH              (AW),
            .ID_WIDTH                (MON_IW),
            .IS_READ                 (1'b1),             // This is a read ocelus
            .IS_AXI                  (1'b1),             // AXI protocol (AXIL is subset)
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
            .N_ADDR_RANGES           (N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk                    (aclk),
            .aresetn                 (aresetn),
            .clear                   (cam_clear | ~cfg_monitor_enable),
            .i_mon_time              (i_mon_time),

            // Command interface (AR channel - monitoring slave side) - AXIL simplified
            .cmd_addr                (fub_axil_araddr),
            .cmd_id                  (w_mon_cmd_id),
            .cmd_len                 (8'h00),            // Single-beat: len=0
            // AxSIZE for the single Lite beat, DERIVED from the bus width.
            // This was hardwired 3'b010 (4 bytes). axi_monitor_base computes
            // perf_byte_count as (1 << cmd_size) per beat, so on a 64-bit
            // AXI4-Lite bus every beat moved 8 bytes and was counted as 4 --
            // byte counts read exactly half, silently. AXI4-Lite permits 32
            // and 64. At DW=32 this evaluates to 3'b010, unchanged.
            .cmd_size                (3'($clog2(AXIL_DATA_WIDTH/8))),
            .cmd_burst               (2'b01),            // INCR burst type
            .cmd_valid               (w_mon_cmd_valid),
            .cmd_ready               (fub_axil_arready),

            // Data interface (R channel - monitoring slave side) - AXIL simplified
            .data_id                 (w_mon_data_id),
            .data_last               (1'b1),             // Always last for AXIL
            .data_resp               (fub_axil_rresp),
            .data_valid              (w_mon_data_valid),
            .data_ready              (fub_axil_rready),

            // Response interface (same as data for AXIL reads)
            .resp_id                 (w_mon_data_id),
            .resp_code               (fub_axil_rresp),
            .resp_valid              (w_mon_resp_valid),    // Every data is also completion for AXIL
            .resp_ready              (fub_axil_rready),

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

            // The runtime ID filter is not exposed on the AXI-Lite wrappers; tied off.

            .cfg_id_filter_enable    (1'b0),

            .cfg_id_match_base       ('0),

            .cfg_id_match_count      ('0),

            .cfg_addr_filter_enable  (cfg_addr_filter_enable),
            .cfg_addr_filter_low     (cfg_addr_filter_low),
            .cfg_addr_filter_high    (cfg_addr_filter_high),
            // Ocelus bus output
            .monbus_valid            (monbus_valid),
            .monbus_ready            (monbus_ready),
            .monbus_packet           (monbus_packet),
            .monbus_timestamp        (monbus_timestamp),

            // Status outputs
            // block_ready stalls new ARs at fub_axil_arready when the ocelus
            // FIFO is full (wire ANDed into the wrapper output below).
            .block_ready             (w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy                    (),                 // Unused (using slave busy)
            /* verilator lint_on PINCONNECTEMPTY */
            .active_count            (active_transactions),

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
            .perf_completed_count(w_perf_completed_count),
            .perf_error_count    (w_perf_error_count)

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

        // Stage A/B perfmon outputs — tied to 0 when ocelus disabled.
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

    // Gate the upstream AR handshake on ocelus block_ready.
    assign s_axil_arready = w_core_s_axil_arready &
           (w_block_ready | ~cfg_monitor_enable);  // disabled ocelus never stalls

    // error_count / transaction_count: driven from the base ocelus's
    // lifetime reporter counters (axi_monitor_reporter_perf). They count
    // packets actually EMITTED (marked into the reporter FIFO): error_count
    // covers error+timeout packets, transaction_count covers completion
    // packets. Zero when USE_MONITOR=0 or ENABLE_PERF_LOGIC=0.
    assign error_count       = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

endmodule : axil5_slave_rd_mon
