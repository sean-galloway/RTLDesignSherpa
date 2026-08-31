// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_base
// Purpose: Axi Monitor Base module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
/**
 * AXI Monitor Bus Base Module - Updated for Generic Monitor Package
 *
 * This module provides a robust implementation for tracking AXI/AXI-Lite
 * transactions and reporting events and errors through the monitor bus.
 * Updated to work with the enhanced monitor_pkg that supports multiple protocols.
 *
 * Features:
 * - Transaction-based tracking for both AXI and AXI-Lite
 * - Proper handling of out-of-order transactions
 * - Support for data arriving before address
 * - Complete protocol compliance
 * - Consolidated 64-bit event packet output for system event bus
 * - Optional performance metrics tracking
 * - Updated for multi-protocol monitor package
 */
module axi_monitor_base
    import monitor_common_pkg::*;
#(
    // Error Packet Identifiers (widened with 128-bit packet)
    parameter logic [7:0]  UNIT_ID    = 8'h09,    // 8-bit Unit ID
    parameter logic [15:0] AGENT_ID   = 16'h0063, // 16-bit Agent ID

    // ---- ID-range filter: track a SUBSET of the IDs on a shared bus --------
    // Default OFF, so every existing instantiation is bit-identical.
    //
    // When several monitors snoop one bus that carries many channels
    // multiplexed by AXI ID, each one otherwise allocates a table entry for
    // EVERY transaction -- so N monitors each need the full concurrency and N
    // instances buy nothing. Filtering allocation by ID lets each instance own
    // a slice: 8 channels x 8 outstanding needs a 72-entry table in one
    // monitor, which does not close timing here (measured 16 entries at
    // WNS +1.018 ns, 40 entries at WNS -25.183 ns), while four monitors of two
    // channels each need 16 -- the size that is known to close.
    //
    // This gates the MONITOR's observation inputs only. cmd_valid/data_valid/
    // resp_valid here are observation feeds, separate from the datapath the
    // wrapper's core drives, so filtering changes what is TRACKED and never
    // what flows. A filtered instance is transparent on the bus, which is what
    // makes parallel snooping possible.
    //
    // All three channels are filtered on the same range. Filtering the command
    // alone would leave data/resp for other IDs arriving unmatched, and the
    // unmatched path allocates orphan entries -- the table would fill with
    // other channels' traffic, which is the problem this exists to avoid.
    // Transaction-table shaping, forwarded to axi_monitor_trans_mgr.
    // Defaults reproduce today's behaviour exactly; see that module for the
    // AW-order queue and the bank sizing rule.
    parameter bit USE_WDATA_ORDER_Q      = 1'b0,
    parameter int NUM_BANKS              = 1,
    parameter bit ID_FILTER_ENABLE     = 1'b0,
    parameter int ID_MATCH_BASE        = 0,      // first ID owned by this instance
    parameter int ID_MATCH_COUNT       = 0,      // how many; 0 = all (no filter)

    // Address-range packet filter (TASK-015). Default 0 -> filtered_mask is
    // always 0 and the build is bit-identical. See axi_monitor_trans_mgr for
    // why this filters at REPORT time rather than at admission.
    parameter bit ADDR_FILTER_ENABLE   = 1'b0,

    // General parameters
    // ---- Timer LUT sizing (counter_freq_invariant) -------------------------
    // The divisor IS the frequency in MHz, so a table built for THIS design's
    // clock gives an exact 1 us tick -- which is the unit monitor timeouts are
    // expressed in. Defaults below set every entry to ACLK_MHZ, so the tick is
    // exact regardless of cfg_freq_sel. Override to a real MIN..MAX range only
    // if the design switches aclk at runtime.
    parameter int CFI_MIN_FREQ_MHZ     = 100,
    parameter int CFI_MAX_FREQ_MHZ     = 100,
    parameter int CFI_NUM_FREQ_ENTRIES = 16,
    parameter int CFI_FREQ_STRATEGY    = 0,
    parameter int MAX_TRANSACTIONS    = 16,    // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,    // Width of address bus
    parameter int ID_WIDTH            = 8,     // Width of ID bus (0 for AXIL)
    parameter int ADDR_BITS_IN_PKT    = 38,    // Number of address bits to include in error packet

    // Configuration options
    // These are boolean flags, so they're declared as `bit` (1-bit)
    // to match the internal sub-modules (trans_mgr, timeout, reporter,
    // filtered). Previously they were `int` which caused Verilator width
    // warnings at every level of the hierarchy.
    parameter bit IS_READ             = 1'b1, // 1 for read, 0 for write
    parameter bit IS_AXI              = 1'b1, // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 1'b0, // Enable performance metrics tracking
    parameter bit ENABLE_DEBUG_MODULE = 1'b0, // Enable debug tracking module

    // Reporter sub-block enables — gate the LOGIC, not just packet emission.
    // Default 1 preserves legacy behavior; integrators set 0 to synthesize
    // away unused detection cones. ENABLE_TIMEOUT_LOGIC also drops the
    // axi_monitor_timeout instance. ENABLE_PERF_LOGIC defaults to
    // ENABLE_PERF_PACKETS for back-compat with the older switch.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = ENABLE_PERF_PACKETS,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

    // FIFO depths
    parameter int INTR_FIFO_DEPTH     = 8,     // Interrupt FIFO depth
    parameter int DEBUG_FIFO_DEPTH    = 8,     // Debug FIFO depth

    // Address-range check
    // N_ADDR_RANGES = 0 disables the address-range checker entirely (zero area).
    parameter int N_ADDR_RANGES       = 0,
    // Per-range flavor: 0 = DEBUG (hit -> AddrMatch), 1 = ERROR (allowlist miss
    // -> Error/ADDR_RANGE). Default all-0 keeps the ERROR/miss path inert.
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,

    // Short params
    parameter int AW                 = ADDR_WIDTH,
    parameter int IW                 = ID_WIDTH,

    // Verify address bits parameter
    parameter int ADDR_BITS          = (ADDR_BITS_IN_PKT > AW) ? AW : ADDR_BITS_IN_PKT
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,
    input  logic                     clear,   // sync clear: empty the trans CAM + active_count

    // Address-range packet filter configuration (active when
    // ADDR_FILTER_ENABLE=1). Inclusive [low, high]; a transaction whose
    // command address falls OUTSIDE the range has its packets suppressed.
    // Runtime ID filter (TASK-015 "runtime filter updates"). The ID filter
    // was compile-time only: ID_MATCH_BASE/COUNT are elaboration constants,
    // so an integrator could not retarget which master is watched without a
    // rebuild. These take over WHEN cfg_id_filter_enable is high; with it low
    // the parameter behaviour is used unchanged, so existing consumers that
    // set the params and leave this tied off are bit-identical.
    input  logic                     cfg_id_filter_enable,
    input  logic [ID_WIDTH-1:0]      cfg_id_match_base,
    input  logic [ID_WIDTH:0]        cfg_id_match_count,   // 0 = all (no filter)

    input  logic                     cfg_addr_filter_enable,
    input  logic [ADDR_WIDTH-1:0]    cfg_addr_filter_low,
    input  logic [ADDR_WIDTH-1:0]    cfg_addr_filter_high,

    // Command phase (AW/AR)
    input  logic [AW-1:0]            cmd_addr,    // Address value
    input  logic [IW-1:0]            cmd_id,      // Transaction ID
    input  logic [7:0]               cmd_len,     // Burst length (AXI only)
    input  logic [2:0]               cmd_size,    // Burst size (AXI only)
    input  logic [1:0]               cmd_burst,   // Burst type (AXI only)
    input  logic                     cmd_valid,   // Command valid
    input  logic                     cmd_ready,   // Command ready

    // Data channel (W/R)
    input  logic [IW-1:0]            data_id,      // Data ID (read only)
    input  logic                     data_last,    // Last data flag
    input  logic [1:0]               data_resp,    // Response code (read only)
    input  logic                     data_valid,   // Data valid
    input  logic                     data_ready,   // Data ready

    // Response channel (B)
    input  logic [IW-1:0]            resp_id,      // Response ID (write only)
    input  logic [1:0]               resp_code,    // Response code
    input  logic                     resp_valid,   // Response valid
    input  logic                     resp_ready,   // Response ready

    // Timer configs
    input  logic [3:0]               cfg_freq_sel, // Frequency selection (configurable)
    input  logic [15:0]              cfg_addr_cnt, // ADDR match for a timeout
    input  logic [15:0]              cfg_data_cnt, // DATA match for a timeout
    input  logic [15:0]              cfg_resp_cnt, // RESP match for a timeout

    // Packet type enables
    input  logic                     cfg_error_enable,    // Enable error event packets
    input  logic                     cfg_compl_enable,    // Enable transaction completion packets
    input  logic                     cfg_threshold_enable,// Enable threshold crossed packets
    input  logic                     cfg_timeout_enable,  // Enable timeout event packets
    input  logic                     cfg_perf_enable,     // Enable performance metric packets
    input  logic                     cfg_debug_enable,    // Enable debug/trace packets

    // Debug configuration -- DEAD. Both are declared here and referenced by no
    // logic in this module or below it; they were the interface to the debug
    // sub-module that does not exist (see the tie-off comment further down).
    // Kept only because the wrapper family plumbs them. Real debug packets come
    // from the reporter's state-change emitter via cfg_debug_enable.
    input  logic [3:0]               cfg_debug_level, // (inert)
    input  logic [15:0]              cfg_debug_mask,  // (inert)

    // Threshold configuration
    input  logic [15:0]              cfg_active_trans_threshold, // Active transaction threshold
    input  logic [31:0]              cfg_latency_threshold,      // Latency threshold

    // Address-range checker (active when N_ADDR_RANGES > 0)
    input  logic                                                cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]  cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Performance window control (Stage A of perfmon RFC).
    //   See docs/markdown/rtl-amba/index.md for the full
    //   start/end-event encoding. Stage B will wire the four cycle bucket
    //   counters to gate on window_active; Stage D wires the latency
    //   histograms. Stage A only manages the lifecycle.
    //
    //   start_event_sel / end_event_sel encoding:
    //     3'b000  software trigger (cfg_*_trigger pulse)
    //     3'b001  first cmd handshake (start) / last data_last|resp (end)
    //     3'b010  cfg_perf_enable edge (rising/falling)
    //     3'b011  first productive beat (start) / counter saturate (end)
    //     3'b100  external trigger (same path as 3'b000 today)
    //     others  reserved (treated as never-fires)
    input  logic [2:0]               cfg_start_event_sel,
    input  logic [2:0]               cfg_end_event_sel,
    input  logic                     cfg_start_trigger,   // pulse from engine/CSR
    input  logic                     cfg_end_trigger,
    input  logic                     cfg_window_force_close, // software override

    // Free-running monitor-time counter, broadcast from the monbus_group family
    input  monbus_timestamp_t        i_mon_time,

    // Consolidated 128-bit event packet interface (monitor bus)
    output logic                     monbus_valid,      // Interrupt valid
    input  logic                     monbus_ready,      // Interrupt ready
    output monitor_packet_t          monbus_packet,     // Consolidated interrupt packet
    output monbus_timestamp_t        monbus_timestamp,  // Side-band sampled time

    // Flow control and status
    output logic                     block_ready,    // Flow control signal
    output logic                     busy,           // Monitor is busy
    output logic [7:0]               active_count,   // Number of active transactions

    // Performance window status (Stage A of perfmon RFC).
    //   window_active: high while a measurement window is open. Stage B
    //                  counters gate on this. Stage E integration can
    //                  drive software-visible CSR status from this.
    //   window_cycles: free-running counter of cycles elapsed inside the
    //                  current window. Sampled by reporter at window
    //                  close into the WIN_END PerfWin packet (Stage B).
    output logic                     window_active,
    output logic [31:0]              window_cycles,

    // Performance window cycle buckets (Stage B of perfmon RFC).
    //
    //   All counters are accumulators that run while window_active=1
    //   and reset on window-start. Sampled at WIN_CLOSING by the
    //   integrating block (or future reporter; see RFC Stage B/F).
    //
    //   Per DMA_UTILIZATION_MEASUREMENT.md Section 3 four-bucket model,
    //   counted on the DATA bus (R for read monitors, W for write
    //   monitors). The cmd-bus burst handshake count is also exposed
    //   separately (perf_burst_count) so the integrator can compute
    //   burst_count and bytes-per-burst.
    //
    //   perf_byte_count uses cmd_size (AXSIZE) captured at the most
    //   recent address-phase handshake; assumes axsize is constant
    //   within a burst (AXI4 mandate). 64-bit width prevents wrap on
    //   long windows at wide buses.
    //
    //   Stage C will replicate these per-channel for id-aware monitors.
    output logic [31:0]              perf_prod_cycles,   // data valid && ready
    output logic [31:0]              perf_bp_cycles,     // data valid && !ready (back-pressure)
    output logic [31:0]              perf_starv_cycles,  // !data valid && ready (starvation)
    output logic [31:0]              perf_idle_cycles,   // !data valid && !ready
    output logic [31:0]              perf_beat_count,    // = perf_prod_cycles (1 beat/cycle)
    output logic [63:0]              perf_byte_count,    // beats x (1<<axsize_latched)
    output logic [31:0]              perf_burst_count,   // AR/AW handshake count

    // Lifetime reporter counters (axi_monitor_reporter_perf). These count
    // packets actually EMITTED (marked into the reporter FIFO): completions
    // when compl packets are enabled, errors/timeouts when their classes
    // are. Tied to 0 when ENABLE_PERF_LOGIC=0 (the counters live in the
    // perf sub-block). Exposed so wrappers can drive their error_count /
    // transaction_count status outputs from the truth instead of 0.
    output logic [15:0]              perf_completed_count,
    output logic [15:0]              perf_error_count
);

    // Import standard monitor types and constants
    // (monitor_common_pkg already imported at module-header level for the typedefs
    // used in the port list)
    import monitor_amba4_pkg::*;
    // NOTE: `import monitor_pkg::*;` intentionally omitted -- its helper
    // functions (get_packet_type etc.) duplicate monitor_common_pkg's, and
    // Vivado flags the duplicates as ambiguous under wildcard imports.

    // Transaction tracking table - Fixed: Use unpacked array consistently
    bus_transaction_t w_trans_table[MAX_TRANSACTIONS];

    // FIX-001: Event reported feedback from reporter to trans_mgr
    logic [MAX_TRANSACTIONS-1:0] w_event_reported_flags;

    // Transaction statistics (combinational)
    logic [7:0]  w_active_count;
    logic [15:0] w_event_count;
    logic [15:0] w_debug_count;

    // Timer tick from the frequency invariant timer (combinational)
    logic w_timer_tick;

    // Timestamp counter for transaction timing (flopped)
    logic [31:0] r_timestamp;

    // Per-slot verdicts from the transaction manager (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_filtered_mask;
    logic [MAX_TRANSACTIONS-1:0] w_timeout_detected;

    // Interrupt outputs from different modules (combinational)
    logic                     w_reporter_monbus_valid;
    monitor_packet_t          w_reporter_monbus_packet;
    logic                     w_debug_monbus_valid;
    monitor_packet_t          w_debug_monbus_packet;
    // addr_check owns the monbus mux once it has been presented and
    // stalled; see the selection-hold comment at the mux below.
    logic                     r_addr_hold;
    logic                     w_addr_pkt_valid;
    monitor_packet_t          w_addr_pkt_data;
    monbus_timestamp_t        w_addr_pkt_timestamp;
    logic                     w_addr_pkt_ready;

    // The debug-trace monbus source is TIED OFF UNCONDITIONALLY, because the
    // debug sub-module it was meant to feed does not exist in this design.
    //
    // This tie-off used to be guarded by `if (!ENABLE_DEBUG_MODULE)`, with no
    // matching gen_debug branch to instantiate anything -- so setting
    // ENABLE_DEBUG_MODULE=1 removed the only driver of these two nets and left
    // the monbus arbiter below evaluating an undriven `w_debug_monbus_valid`
    // on every cycle the reporter was idle: X-propagation in simulation, an
    // arbitrary tie in synthesis (qc round_24). Every instantiation in the
    // repo passes 0, so the trap was latent rather than live, but a parameter
    // whose only effect is to break the design is worse than one that does
    // nothing.
    //
    // ENABLE_DEBUG_MODULE is therefore INERT and reserved: it is kept on the
    // port list because 12 wrappers plumb it through, and removing it (along
    // with the equally dead DEBUG_FIFO_DEPTH / cfg_debug_level /
    // cfg_debug_mask) is an API change across the whole wrapper family rather
    // than a fix. The LIVE debug path is the reporter's state-change emitter,
    // gated by ENABLE_DEBUG_LOGIC + cfg_debug_enable.
    assign w_debug_monbus_valid  = 1'b0;
    assign w_debug_monbus_packet = '0;

    // -------------------------------------------------------------------------
    // Module Instantiations
    // -------------------------------------------------------------------------

    // ---- ID-range filter (see the parameter block) --------------------------
    // Combinational match per channel. ID_MATCH_COUNT=0 or ID_FILTER_ENABLE=0
    // leaves every valid untouched, so the default build is unchanged.
    function automatic logic id_owned(input logic [IW-1:0] id);
        if (cfg_id_filter_enable) begin
            // Runtime window. count==0 means "all", matching the parameter
            // rule, so a zeroed CSR block does not silently filter everything.
            if (cfg_id_match_count == 0) id_owned = 1'b1;
            else id_owned = (int'(id) >= int'(cfg_id_match_base)) &&
                            (int'(id) <  int'(cfg_id_match_base) + int'(cfg_id_match_count));
        end else if (!ID_FILTER_ENABLE || (ID_MATCH_COUNT == 0)) begin
            id_owned = 1'b1;
        end else begin
            id_owned = (int'(id) >= ID_MATCH_BASE) &&
                       (int'(id) <  ID_MATCH_BASE + ID_MATCH_COUNT);
        end
    endfunction

    logic w_cmd_valid_f, w_data_valid_f, w_resp_valid_f;
    assign w_cmd_valid_f  = cmd_valid  && id_owned(cmd_id);
    assign w_data_valid_f = data_valid && id_owned(data_id);
    assign w_resp_valid_f = resp_valid && id_owned(resp_id);

    // Transaction Table Manager
    axi_monitor_trans_mgr #(
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .ID_WIDTH           (ID_WIDTH),
        .IS_READ            (IS_READ),
        .IS_AXI             (IS_AXI),
        .USE_WDATA_ORDER_Q       (USE_WDATA_ORDER_Q),
        .NUM_BANKS               (NUM_BANKS),
        .ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
        .ADDR_FILTER_ENABLE (ADDR_FILTER_ENABLE)
    ) trans_mgr(
        .aclk               (aclk),
        .aresetn            (aresetn),
        .clear              (clear),
        .cmd_valid          (w_cmd_valid_f),
        .cmd_ready          (cmd_ready),
        .cmd_id             (cmd_id),
        .cmd_addr           (cmd_addr),
        .cmd_len            (cmd_len),
        .cmd_size           (cmd_size),
        .cmd_burst          (cmd_burst),
        .data_valid         (w_data_valid_f),
        .data_ready         (data_ready),
        .data_id            (data_id),
        .data_last          (data_last),
        .data_resp          (data_resp),
        .resp_valid         (w_resp_valid_f),
        .resp_ready         (resp_ready),
        .resp_id            (resp_id),
        .resp_code          (resp_code),
        .timestamp          (r_timestamp),
        .i_event_reported_flags(w_event_reported_flags),  // FIX-001: Feedback from reporter
        .i_timeout_detected (w_timeout_detected),         // ISSUE #41: timeout -> terminal state
        .trans_table        (w_trans_table),
        .active_count       (w_active_count),
        .cfg_addr_filter_enable(cfg_addr_filter_enable),
        .cfg_addr_filter_low   (cfg_addr_filter_low),
        .cfg_addr_filter_high  (cfg_addr_filter_high),
        .filtered_mask         (w_filtered_mask)
    );

    // Invariant Timer using counter_freq_invariant
    axi_monitor_timer #(
        .CFI_MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ),
        .CFI_NUM_FREQ_ENTRIES (CFI_NUM_FREQ_ENTRIES),
        .CFI_FREQ_STRATEGY    (CFI_FREQ_STRATEGY)
    ) timer (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .cfg_freq_sel(cfg_freq_sel),
        .timer_tick    (w_timer_tick),
        .timestamp     (r_timestamp)
    );

    // Timeout Detector — drops entirely when ENABLE_TIMEOUT_LOGIC=0.
    if (ENABLE_TIMEOUT_LOGIC) begin : gen_timeout
        axi_monitor_timeout #(
            .MAX_TRANSACTIONS    (MAX_TRANSACTIONS),
            .ADDR_WIDTH          (ADDR_WIDTH),
            .IS_READ             (IS_READ)
        ) timeout(
            .aclk                (aclk),
            .aresetn             (aresetn),
            .trans_table         (w_trans_table),
            .timer_tick          (w_timer_tick),
            .cfg_addr_cnt        (cfg_addr_cnt),
            .cfg_data_cnt        (cfg_data_cnt),
            .cfg_resp_cnt        (cfg_resp_cnt),
            .cfg_timeout_enable  (cfg_timeout_enable),
            .timeout_detected    (w_timeout_detected)
        );
    end else begin : gen_no_timeout
        assign w_timeout_detected = '0;
    end

    // Interrupt Reporter with gaxi_fifo_sync
    axi_monitor_reporter #(
        .MAX_TRANSACTIONS      (MAX_TRANSACTIONS),
        .ADDR_WIDTH            (ADDR_WIDTH),
        .UNIT_ID               (UNIT_ID),
        .AGENT_ID              (AGENT_ID),
        .IS_READ               (IS_READ),
        .ENABLE_PERF_PACKETS   (ENABLE_PERF_PACKETS),
        .INTR_FIFO_DEPTH       (INTR_FIFO_DEPTH),
        .ENABLE_ERROR_LOGIC    (ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC  (ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC    (ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC     (ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC    (ENABLE_DEBUG_LOGIC)
    ) reporter(
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .trans_table           (w_trans_table),
        .filtered_mask         (w_filtered_mask),
        .timeout_detected      (w_timeout_detected),  // Pass timeout flags
        .cfg_error_enable      (cfg_error_enable),
        .cfg_compl_enable      (cfg_compl_enable),
        .cfg_threshold_enable  (cfg_threshold_enable),
        .cfg_timeout_enable    (cfg_timeout_enable),
        .cfg_perf_enable       (cfg_perf_enable),
        .cfg_debug_enable      (cfg_debug_enable),
        // NOT monbus_ready directly: while addr_check holds the bus the mux
        // presents ITS packet, so an unqualified ready here would look like
        // an accept of the reporter's packet and silently drop it.
        .monbus_ready          (monbus_ready && !r_addr_hold),
        .monbus_valid          (w_reporter_monbus_valid),
        .monbus_packet         (w_reporter_monbus_packet),
        .event_count           (w_event_count),
        .perf_completed_count  (perf_completed_count),
        .perf_error_count      (perf_error_count),
        .active_trans_threshold(cfg_active_trans_threshold),
        .latency_threshold     (cfg_latency_threshold),
        .event_reported_flags  (w_event_reported_flags)  // TASK-001: Feedback to trans_mgr
    );

    // -------------------------------------------------------------------------
    // Address-range checker (optional, gated by N_ADDR_RANGES)
    // -------------------------------------------------------------------------
    // When N_ADDR_RANGES > 0 we instantiate the comparator; otherwise tie its
    // output stream to 0 so the arbiter sees nothing.
    if (N_ADDR_RANGES > 0) begin : gen_addr_check
        axi_monitor_addr_check #(
            .N_ADDR_RANGES (N_ADDR_RANGES),
            .ADDR_WIDTH    (ADDR_WIDTH),
            .ID_WIDTH      (ID_WIDTH > 0 ? ID_WIDTH : 1),
            .UNIT_ID       (UNIT_ID),
            .AGENT_ID      (AGENT_ID),
            .IS_READ       (IS_READ),
            .ADDR_RANGE_IS_ERROR (ADDR_RANGE_IS_ERROR)
        ) addr_check (
            .clk                   (aclk),
            .aresetn               (aresetn),
            .i_mon_time            (i_mon_time),
            .cmd_addr              (cmd_addr),
            .cmd_id                (cmd_id),
            .cmd_valid             (w_cmd_valid_f),
            .cmd_ready             (cmd_ready),
            .cfg_addr_check_enable (cfg_addr_check_enable),
            .cfg_debug_enable      (cfg_debug_enable),
            .cfg_error_enable      (cfg_error_enable),
            .cfg_addr_range_enable (cfg_addr_range_enable),
            .cfg_addr_range_low    (cfg_addr_range_low),
            .cfg_addr_range_high   (cfg_addr_range_high),
            .addr_pkt_valid        (w_addr_pkt_valid),
            .addr_pkt_ready        (w_addr_pkt_ready),
            .addr_pkt_data         (w_addr_pkt_data),
            .addr_pkt_timestamp    (w_addr_pkt_timestamp)
        );
    end else begin : gen_no_addr_check
        assign w_addr_pkt_valid     = 1'b0;
        assign w_addr_pkt_data      = '0;
        assign w_addr_pkt_timestamp = '0;
    end

    // -------------------------------------------------------------------------
    // Monitor Bus Arbitration
    // -------------------------------------------------------------------------

    // Priority: reporter > debug > addr_check.
    // Reporter handles existing error/timeout/compl/perf events; debug is for
    // trace; addr_check is a slow-rate violation stream that can wait.
    // All branches sample the same broadcast i_mon_time on emission cycle.
    // Selection hold. The mux below is a combinational priority select, so
    // without this an addr_check packet presented while monbus_ready is low
    // would be REPLACED by the reporter's the moment the reporter's
    // (registered) valid rises -- monbus_packet changing while monbus_valid
    // is high and monbus_ready is still low. Nothing is lost, because
    // addr_check holds its pending slot until its own accept and a sink that
    // samples on valid && ready never sees it; but it violates the
    // valid/ready payload-stability rule this bus otherwise keeps, and a sink
    // that latches on valid alone would capture a torn packet.
    //
    // So once addr_check has been presented and stalled, it OWNS the bus
    // until its beat is accepted. addr_check is the only source that can be
    // displaced: the reporter already has top priority, and the debug source
    // is tied off above.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_addr_hold <= 1'b0;
        end else if (!r_addr_hold) begin
            // Latch ownership only when the beat is actually stalled; an
            // addr packet accepted in its first cycle never needs the hold.
            r_addr_hold <= w_addr_pkt_valid && !w_reporter_monbus_valid
                           && !w_debug_monbus_valid && !monbus_ready;
        end else if (monbus_ready) begin
            r_addr_hold <= 1'b0;
        end
    )

    always_comb begin
        if (r_addr_hold) begin
            monbus_valid     = w_addr_pkt_valid;
            monbus_packet    = w_addr_pkt_data;
            monbus_timestamp = w_addr_pkt_timestamp;
        end else if (w_reporter_monbus_valid) begin
            monbus_valid     = w_reporter_monbus_valid;
            monbus_packet    = w_reporter_monbus_packet;
            monbus_timestamp = i_mon_time;
        end else if (w_debug_monbus_valid) begin
            monbus_valid     = w_debug_monbus_valid;
            monbus_packet    = w_debug_monbus_packet;
            monbus_timestamp = i_mon_time;
        end else if (w_addr_pkt_valid) begin
            monbus_valid     = w_addr_pkt_valid;
            monbus_packet    = w_addr_pkt_data;
            monbus_timestamp = w_addr_pkt_timestamp;
        end else begin
            monbus_valid     = 1'b0;
            monbus_packet    = '0;
            monbus_timestamp = '0;
        end
    end

    // Back-pressure into addr_check: only accept when reporter/debug are quiet
    // AND the downstream consumer is ready.
    // While addr_check owns the bus its ready must NOT stay gated on the
    // reporter, or the held beat could never be accepted and the bus would
    // deadlock the moment the reporter went permanently busy.
    assign w_addr_pkt_ready = monbus_ready &&
                              (r_addr_hold ||
                               (!w_reporter_monbus_valid && !w_debug_monbus_valid));

    // -------------------------------------------------------------------------
    // Flow Control Logic
    // -------------------------------------------------------------------------

    // Flow control: positive-enable, 1 = upstream may proceed, 0 = stall.
    // Polarity must match the wrapper gating
    //   <port>_ready = w_core_<port>_ready & w_block_ready;
    // (the no-monitor branches tie w_block_ready=1'b1 to allow). The
    // pre-fix expression set block_ready=1 only when the transaction
    // table was nearly full, which inverted the polarity and stalled
    // every upstream handshake immediately after reset (count=0,
    // block_ready=0, ready=0, count never increments -> deadlock).
    // The bridge monitored-mode smoke test caught this; formal P6/P7
    // missed it because the assertion was tautological vs. the assign.
    // The trans CAM is ALWAYS pipelined (one extra cycle of active_count
    // latency), so block_ready keeps a margin below MAX_TRANSACTIONS.
    //
    // SATURATION-RECOVERY CONTRACT (keep in sync with CMD_ENTRY_RESERVE in
    // axi_monitor_trans_mgr.sv): the trans_mgr caps COMMAND-originated
    // entries at MAX - CMD_ENTRY_RESERVE slots. This margin is
    // CMD_ENTRY_RESERVE - 1, so block_ready re-asserts at
    // active_count < MAX - (CMD_ENTRY_RESERVE - 1) -- STRICTLY ABOVE the
    // command cap. Therefore even a table whose command entries are all
    // permanently in flight recovers block_ready as soon as the ungated
    // data/resp (orphan) entries drain -- orphans always drain via error
    // reporting, so only command entries can be durable occupants. With the
    // old flat MAX-3 margin equal to the effective command occupancy at
    // saturation, the table parked exactly AT the threshold and block_ready
    // never re-asserted: the monitor stalled the monitored command channel
    // for ever (stream_core multi-channel wedge; reproduced by
    // val/amba/test_axi_monitor_trans_mgr.py phase_saturation_recovers).
    //
    // Overshoot past MAX is impossible regardless of this margin: the CAM
    // allocates from its exact combinational free vector, so the table can
    // never hold more than MAX entries. Commands that handshake while the
    // cap is reached (count register lag + skid drain) are simply not
    // tracked -- lossy-but-honest degrade instead of a permanent stall.
    // Tables without the cap (MAX < 16) keep the legacy flat margin of 3 --
    // their behavior is exactly pre-fix, cap included (CMD_ENTRY_RESERVE=0
    // in trans_mgr).
    localparam int unsigned CMD_ENTRY_RESERVE =
        unsigned'(cmd_entry_reserve(MAX_TRANSACTIONS));
    // BLOCK_MARGIN must cover every allocation that can happen while
    // active_count is stale, NOT just the command one.
    //
    // active_count is a REGISTERED pop-count and lags true occupancy by one
    // cycle (axi_monitor_trans_mgr.sv -- deliberate: the old accumulator could
    // underflow to 0xFF). In that one cycle THREE independent allocators can
    // fire, each with its own one-hot out of monitor_trans_cam:
    //
    //     addr_wants_alloc    data_wants_alloc    resp_wants_alloc
    //
    // The margin has to satisfy TWO constraints at once:
    //   (a) >= 3, because three allocators (addr/data/resp_wants_alloc) can
    //       fire in the single stale cycle of the registered w_active_count;
    //   (b) <= CMD_ENTRY_RESERVE - 1, or block_ready can never RE-ASSERT
    //       after saturation (recovery contract above).
    // Both hold because cmd_entry_reserve() returns 4 on tables >= 16, making
    // the derived margin exactly 3. That reserve value is NOT free -- it costs
    // 4 slots of command capacity per table -- and it is the ONLY value that
    // satisfies both constraints with this derivation, so neither side may be
    // changed alone:
    //
    //   * With the old reserve of 2 the margin derived to 1, and a command
    //     could be ADMITTED against stale occupancy and then find no free
    //     slot. Its data beats arrived with nothing to match, and data/resp
    //     allocation cannot be backpressured (a monitor must never stall
    //     returning data), so those beats were silently discarded. Measured:
    //     obs_equiv observer 4096 vs in-core 3073, identical at 2,000 and
    //     200,000 clocks of drain (loss, not backlog).
    //   * Raising the MARGIN alone to 3 while the reserve stayed 2 was tried
    //     (2026-08-17) and breaks (b): on a 16-slot table block_ready needs
    //     active_count < 13 while the reserve only guarantees 2 free slots,
    //     so occupancy parks at 14 and the gate never recovers -- the
    //     permanent wedge the reserve exists to prevent, worse than the loss.
    //
    // History and measurements in vault/Tasks/amba (AMBA-BLOCKMARGIN, closed).
    // Enforced: val/amba/test_axi_mon_block_ready.py asserts no command is
    // admitted without an allocation (assert_no_untracked_admissions) and
    // that occupancy never exceeds the table depth, on every wrapper; the
    // trans_mgr FORMAL block's ap_cmd_entry_cap proves the command cap.
    localparam int unsigned BLOCK_MARGIN =
        (CMD_ENTRY_RESERVE > 0) ? (CMD_ENTRY_RESERVE - 1) : 3;
    assign block_ready = (MAX_TRANSACTIONS > BLOCK_MARGIN)
                       ? ({24'h0, w_active_count} < (MAX_TRANSACTIONS - BLOCK_MARGIN))
                       : 1'b1;

    // Busy signal
    assign busy = (w_active_count > 0);

    // Active transaction count
    assign active_count = w_active_count;

    // =========================================================================
    // Performance window state machine (Stage A of perfmon RFC)
    //
    // Drives window_active / window_cycles based on the start/end-event
    // selector inputs. Stage B will gate the four cycle bucket counters
    // (productive/bp/starv/idle) on window_active. Stage D wires the
    // latency-histogram bucket counters the same way. Stage A only
    // manages the lifecycle so the rest of the perfmon work has a
    // stable window framework to hang off of.
    //
    // States:
    //   WIN_IDLE    : waiting for start event. window_active=0.
    //   WIN_ACTIVE  : window open. window_cycles ticking. counters (Stage B+)
    //                 gate on window_active.
    //   WIN_CLOSING : one-cycle hold before re-arming. In Stage A this is
    //                 just a transition state; Stage B holds it long
    //                 enough for the reporter to drain WIN_END + counter
    //                 packets without losing them to a re-open.
    // =========================================================================
    typedef enum logic [1:0] {
        WIN_IDLE_S    = 2'b00,
        WIN_ACTIVE_S  = 2'b01,
        WIN_CLOSING_S = 2'b10
    } win_state_e;

    win_state_e  r_win_state;
    logic [31:0] r_window_cycles;
    logic        r_perf_enable_d1;
    logic        w_perf_enable_rising;
    logic        w_perf_enable_falling;
    logic        w_cmd_handshake;
    logic        w_data_handshake;
    logic        w_resp_handshake;
    logic        w_window_saturate;
    logic        w_start_event;
    logic        w_end_event;

    assign w_cmd_handshake  = cmd_valid  && cmd_ready;
    assign w_data_handshake = data_valid && data_ready;
    assign w_resp_handshake = resp_valid && resp_ready;
    // Saturate one cycle before max so the bump-by-1 below doesn't wrap
    // through 0 and confuse the reporter on the same cycle.
    assign w_window_saturate = (r_window_cycles == 32'hFFFF_FFFE);

    // Edge detect on cfg_perf_enable for sel modes 010/011
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) r_perf_enable_d1 <= 1'b0;
        else          r_perf_enable_d1 <= cfg_perf_enable;
    end
    assign w_perf_enable_rising  =  cfg_perf_enable && !r_perf_enable_d1;
    assign w_perf_enable_falling = !cfg_perf_enable &&  r_perf_enable_d1;

    // Start-event mux. Codes 3'b000 and 3'b100 both map to the trigger
    // input for now -- one is software-CSR, the other is the external
    // trigger pin convention; the integrating block can choose to mux
    // an external pin into cfg_start_trigger.
    always_comb begin
        case (cfg_start_event_sel)
            3'b000:  w_start_event = cfg_start_trigger;
            3'b001:  w_start_event = w_cmd_handshake;
            3'b010:  w_start_event = w_perf_enable_rising;
            3'b011:  w_start_event = w_data_handshake;
            3'b100:  w_start_event = cfg_start_trigger;
            default: w_start_event = 1'b0;
        endcase
    end

    // End-event mux. For mode 3'b001 the "last data" semantic differs by
    // direction: reads end at RLAST handshake, writes end at B handshake.
    //
    // ISSUE #41: 3'b010 and 3'b011 used to be TRANSPOSED with respect to
    // both the port-declaration header above and the start-event mux
    // (which has always had 3'b010 = perf-enable edge, 3'b011 = the
    // "productive" event). These selectors are software-programmed CSR
    // fields, so an integrator following the documented encoding got the
    // wrong window-close event. The header is authoritative -- it is the
    // published contract and the start mux already agreed with it -- so
    // the END mux is corrected to match rather than the other way round.
    always_comb begin
        case (cfg_end_event_sel)
            3'b000:  w_end_event = cfg_end_trigger;
            3'b001:  w_end_event = IS_READ ? (w_data_handshake && data_last)
                                           :  w_resp_handshake;
            3'b010:  w_end_event = w_perf_enable_falling;  // perf-enable edge
            3'b011:  w_end_event = w_window_saturate;      // counter saturate
            3'b100:  w_end_event = cfg_end_trigger;
            default: w_end_event = 1'b0;
        endcase
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_win_state     <= WIN_IDLE_S;
            r_window_cycles <= 32'h0;
        end else begin
            unique case (r_win_state)
                WIN_IDLE_S: begin
                    if (w_start_event) begin
                        r_win_state     <= WIN_ACTIVE_S;
                        // Start at 1 so the WIN_END packet's window_cycles
                        // value counts inclusive of the first cycle.
                        r_window_cycles <= 32'h0000_0001;
                    end
                end
                WIN_ACTIVE_S: begin
                    // ISSUE #41: saturate UNCONDITIONALLY. w_window_saturate
                    // used to be consumed only by cfg_end_event_sel==3'b010,
                    // so under every other selector this counter incremented
                    // regardless and wrapped through 0 at 2^32 -- silently
                    // restarting the window measurement on any long window.
                    if (!w_window_saturate) begin
                        r_window_cycles <= r_window_cycles + 32'h1;
                    end
                    if (w_end_event || cfg_window_force_close) begin
                        r_win_state <= WIN_CLOSING_S;
                    end
                end
                WIN_CLOSING_S: begin
                    // Stage A: immediate transition. Stage B will hold here
                    // until the reporter ACKs draining the window packets.
                    //
                    // ISSUE #41: r_window_cycles is NOT zeroed here. It used
                    // to be, which left it readable for exactly the one
                    // WIN_CLOSING cycle while the bucket counters held --
                    // contradicting the "all counters hold into WIN_IDLE"
                    // contract documented at the bucket block below. It is
                    // re-initialised at the next window start instead.
                    r_win_state <= WIN_IDLE_S;
                end
                default: begin
                    r_win_state <= WIN_IDLE_S;
                end
            endcase
        end
    end

    assign window_active = (r_win_state == WIN_ACTIVE_S);
    assign window_cycles = r_window_cycles;

    // =========================================================================
    // Performance cycle bucket + beat/byte/burst counters (Stage B)
    //
    //   Per RFC Stage B and DMA_UTILIZATION_MEASUREMENT.md Section 3,
    //   the cycle-bucket counters classify every cycle of the data bus
    //   into one of four mutually-exclusive buckets, then accumulate
    //   the bytes-moved tally separately. All counters reset on
    //   window-start and are stable from WIN_CLOSING -> WIN_IDLE so
    //   the integrating block can sample them.
    //
    //   Byte counter uses the latched axsize from the most recent
    //   address-phase handshake. This is correct for AXI/AXI-Lite
    //   where axsize is fixed for the lifetime of a burst.
    //
    //   Stage C will gate each counter by id-decoded channel for
    //   per-channel buckets; for Stage B we keep aggregate-only.
    // =========================================================================
    logic [31:0] r_prod_cycles;
    logic [31:0] r_bp_cycles;
    logic [31:0] r_starv_cycles;
    logic [31:0] r_idle_cycles;
    logic [31:0] r_burst_count;
    logic [63:0] r_byte_count;
    logic [2:0]  r_axsize_latched;
    logic        w_window_starting;

    assign w_window_starting = (r_win_state == WIN_IDLE_S) && w_start_event;

    // Latch axsize on every command handshake while the window is open;
    // outside the window we still track it so it's stable at window-open
    // time. Defaults to 3'h0 (1 byte / beat) before any AR/AW.
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_axsize_latched <= 3'h0;
        end else if (w_cmd_handshake) begin
            r_axsize_latched <= cmd_size;
        end
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_prod_cycles  <= 32'h0;
            r_bp_cycles    <= 32'h0;
            r_starv_cycles <= 32'h0;
            r_idle_cycles  <= 32'h0;
            r_burst_count  <= 32'h0;
            r_byte_count   <= 64'h0;
        end else if (w_window_starting) begin
            // Reset all accumulators at window start (synchronous with
            // r_window_cycles going to 1).
            r_prod_cycles  <= 32'h0;
            r_bp_cycles    <= 32'h0;
            r_starv_cycles <= 32'h0;
            r_idle_cycles  <= 32'h0;
            r_burst_count  <= 32'h0;
            r_byte_count   <= 64'h0;
        end else if (r_win_state == WIN_ACTIVE_S) begin
            // Four mutually-exclusive cycle buckets on the data bus.
            //
            // Sum of the four equals window_cycles MINUS ONE by construction
            // (the start cycle seeds window_cycles to 1 while the buckets
            // reset to 0 -- doc identity corrected, qc round_20), UNTIL a
            // counter saturates. ISSUE #41: none of these counters used to
            // saturate at all, so on a long window they wrapped at 2^32
            // independently of r_window_cycles and the invariant broke
            // silently. They now stick at max; a reader seeing 32'hFFFF_FFFF
            // (or a sum below window_cycles) knows the window overflowed
            // rather than being handed a wrapped value that looks plausible.
            if (data_valid && data_ready) begin
                if (r_prod_cycles != 32'hFFFF_FFFF)
                    r_prod_cycles <= r_prod_cycles + 32'h1;
                // Byte count: one beat moves (1<<axsize) bytes. Explicit
                // parens — verilog + has higher precedence than <<.
                if (r_byte_count < (64'hFFFF_FFFF_FFFF_FFFF - (64'h1 << r_axsize_latched)))
                    r_byte_count <= r_byte_count + (64'h1 << r_axsize_latched);
                else
                    r_byte_count <= 64'hFFFF_FFFF_FFFF_FFFF;
            end else if (data_valid && !data_ready) begin
                if (r_bp_cycles != 32'hFFFF_FFFF)
                    r_bp_cycles <= r_bp_cycles + 32'h1;
            end else if (!data_valid && data_ready) begin
                if (r_starv_cycles != 32'hFFFF_FFFF)
                    r_starv_cycles <= r_starv_cycles + 32'h1;
            end else begin
                if (r_idle_cycles != 32'hFFFF_FFFF)
                    r_idle_cycles <= r_idle_cycles + 32'h1;
            end

            // Burst count = address-phase handshakes inside the window.
            if (w_cmd_handshake && (r_burst_count != 32'hFFFF_FFFF)) begin
                r_burst_count <= r_burst_count + 32'h1;
            end
        end
        // In WIN_CLOSING and WIN_IDLE the counters hold their values so
        // the integrating block can sample them after seeing
        // window_active deassert. As of the issue #41 fix this is true of
        // r_window_cycles as well (it used to be zeroed in WIN_CLOSING,
        // leaving it readable for a single cycle while these held), so the
        // whole counter set stays coherent until the next window opens.
    end

    assign perf_prod_cycles  = r_prod_cycles;
    assign perf_bp_cycles    = r_bp_cycles;
    assign perf_starv_cycles = r_starv_cycles;
    assign perf_idle_cycles  = r_idle_cycles;
    assign perf_beat_count   = r_prod_cycles; // one beat per productive cycle
    assign perf_byte_count   = r_byte_count;
    assign perf_burst_count  = r_burst_count;

endmodule : axi_monitor_base
