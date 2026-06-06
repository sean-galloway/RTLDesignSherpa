// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_base
// Purpose: Axi Monitor Base module
//
// Documentation: rtl/amba/PRD.md
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

    // General parameters
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
    input  logic [3:0]               cfg_addr_cnt, // ADDR match for a timeout
    input  logic [3:0]               cfg_data_cnt, // DATA match for a timeout
    input  logic [3:0]               cfg_resp_cnt, // RESP match for a timeout

    // Packet type enables
    input  logic                     cfg_error_enable,    // Enable error event packets
    input  logic                     cfg_compl_enable,    // Enable transaction completion packets
    input  logic                     cfg_threshold_enable,// Enable threshold crossed packets
    input  logic                     cfg_timeout_enable,  // Enable timeout event packets
    input  logic                     cfg_perf_enable,     // Enable performance metric packets
    input  logic                     cfg_debug_enable,    // Enable debug/trace packets

    // Debug configuration (only used when ENABLE_DEBUG_MODULE=1)
    input  logic [3:0]               cfg_debug_level, // Debug verbosity level
    input  logic [15:0]              cfg_debug_mask,  // Event type mask

    // Threshold configuration
    input  logic [15:0]              cfg_active_trans_threshold, // Active transaction threshold
    input  logic [31:0]              cfg_latency_threshold,      // Latency threshold

    // Address-range checker (active when N_ADDR_RANGES > 0)
    input  logic                                                cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]  cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Performance window control (Stage A of perfmon RFC).
    //   See rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md for the full
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

    // Free-running monitor-time counter, broadcast from monbus_axil_group
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
    output logic [31:0]              perf_burst_count    // AR/AW handshake count
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

    // State change detection for debug module (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_state_change_detected;
    logic [MAX_TRANSACTIONS-1:0] w_timeout_detected;

    // Interrupt outputs from different modules (combinational)
    logic                     w_reporter_monbus_valid;
    monitor_packet_t          w_reporter_monbus_packet;
    logic                     w_debug_monbus_valid;
    monitor_packet_t          w_debug_monbus_packet;
    logic                     w_addr_pkt_valid;
    monitor_packet_t          w_addr_pkt_data;
    monbus_timestamp_t        w_addr_pkt_timestamp;
    logic                     w_addr_pkt_ready;

    // Default: debug monbus disabled when ENABLE_DEBUG_MODULE=0.
    // Without this, the wires are undriven and formal tools see undefined values.
    if (!ENABLE_DEBUG_MODULE) begin : gen_no_debug
        assign w_debug_monbus_valid  = 1'b0;
        assign w_debug_monbus_packet = '0;
    end

    // Performance metrics registers (only used when ENABLE_PERF_PACKETS=1) (flopped)
    logic [15:0] r_perf_completed_count;
    logic [15:0] r_perf_error_count;

    // -------------------------------------------------------------------------
    // Module Instantiations
    // -------------------------------------------------------------------------

    // Transaction Table Manager
    axi_monitor_trans_mgr #(
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .ID_WIDTH           (ID_WIDTH),
        .IS_READ            (IS_READ),
        .IS_AXI             (IS_AXI),
        .ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS)
    ) trans_mgr(
        .aclk               (aclk),
        .aresetn            (aresetn),
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_id             (cmd_id),
        .cmd_addr           (cmd_addr),
        .cmd_len            (cmd_len),
        .cmd_size           (cmd_size),
        .cmd_burst          (cmd_burst),
        .data_valid         (data_valid),
        .data_ready         (data_ready),
        .data_id            (data_id),
        .data_last          (data_last),
        .data_resp          (data_resp),
        .resp_valid         (resp_valid),
        .resp_ready         (resp_ready),
        .resp_id            (resp_id),
        .resp_code          (resp_code),
        .timestamp          (r_timestamp),
        .i_event_reported_flags(w_event_reported_flags),  // FIX-001: Feedback from reporter
        .trans_table        (w_trans_table),
        .active_count       (w_active_count),
        .state_change       (w_state_change_detected)
    );

    // Invariant Timer using counter_freq_invariant
    axi_monitor_timer timer (
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
        .timeout_detected      (w_timeout_detected),  // Pass timeout flags
        .cfg_error_enable      (cfg_error_enable),
        .cfg_compl_enable      (cfg_compl_enable),
        .cfg_threshold_enable  (cfg_threshold_enable),
        .cfg_timeout_enable    (cfg_timeout_enable),
        .cfg_perf_enable       (cfg_perf_enable),
        .cfg_debug_enable      (cfg_debug_enable),
        .monbus_ready          (monbus_ready),
        .monbus_valid          (w_reporter_monbus_valid),
        .monbus_packet         (w_reporter_monbus_packet),
        .event_count           (w_event_count),
        .perf_completed_count  (r_perf_completed_count),
        .perf_error_count      (r_perf_error_count),
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
            .IS_READ       (IS_READ)
        ) addr_check (
            .clk                   (aclk),
            .aresetn               (aresetn),
            .i_mon_time            (i_mon_time),
            .cmd_addr              (cmd_addr),
            .cmd_id                (cmd_id),
            .cmd_valid             (cmd_valid),
            .cmd_ready             (cmd_ready),
            .cfg_addr_check_enable (cfg_addr_check_enable),
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
    always_comb begin
        if (w_reporter_monbus_valid) begin
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
    assign w_addr_pkt_ready = monbus_ready && !w_reporter_monbus_valid && !w_debug_monbus_valid;

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
    assign block_ready = (MAX_TRANSACTIONS > 2) ? ({24'h0, w_active_count} < (MAX_TRANSACTIONS - 2)) : 1'b1;

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
    always_comb begin
        case (cfg_end_event_sel)
            3'b000:  w_end_event = cfg_end_trigger;
            3'b001:  w_end_event = IS_READ ? (w_data_handshake && data_last)
                                           :  w_resp_handshake;
            3'b010:  w_end_event = w_window_saturate;
            3'b011:  w_end_event = w_perf_enable_falling;
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
                    r_window_cycles <= r_window_cycles + 32'h1;
                    if (w_end_event || cfg_window_force_close) begin
                        r_win_state <= WIN_CLOSING_S;
                    end
                end
                WIN_CLOSING_S: begin
                    // Stage A: immediate transition. Stage B will hold here
                    // until the reporter ACKs draining the window packets.
                    r_win_state     <= WIN_IDLE_S;
                    r_window_cycles <= 32'h0;
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
            // Sum of the four equals window_cycles by construction.
            if (data_valid && data_ready) begin
                r_prod_cycles <= r_prod_cycles + 32'h1;
                // Byte count: one beat moves (1<<axsize) bytes. Explicit
                // parens — verilog + has higher precedence than <<.
                r_byte_count  <= r_byte_count + (64'h1 << r_axsize_latched);
            end else if (data_valid && !data_ready) begin
                r_bp_cycles    <= r_bp_cycles    + 32'h1;
            end else if (!data_valid && data_ready) begin
                r_starv_cycles <= r_starv_cycles + 32'h1;
            end else begin
                r_idle_cycles  <= r_idle_cycles  + 32'h1;
            end

            // Burst count = address-phase handshakes inside the window.
            if (w_cmd_handshake) begin
                r_burst_count <= r_burst_count + 32'h1;
            end
        end
        // In WIN_CLOSING and WIN_IDLE the counters hold their values so
        // the integrating block can sample them after seeing
        // window_active deassert.
    end

    assign perf_prod_cycles  = r_prod_cycles;
    assign perf_bp_cycles    = r_bp_cycles;
    assign perf_starv_cycles = r_starv_cycles;
    assign perf_idle_cycles  = r_idle_cycles;
    assign perf_beat_count   = r_prod_cycles; // one beat per productive cycle
    assign perf_byte_count   = r_byte_count;
    assign perf_burst_count  = r_burst_count;

endmodule : axi_monitor_base
