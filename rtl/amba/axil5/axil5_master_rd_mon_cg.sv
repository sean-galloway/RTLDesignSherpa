// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_rd_mon_cg
// Purpose: Axil4 Master Rd Mon Cg module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXIL4 Master Read with Integrated Filtered Monitoring and Clock Gating
 *
 * This module extends axil5_master_rd_mon with comprehensive clock gating capabilities
 * for power optimization: an ICG stops the monitor clock after a configurable
 * idle period and the request-side readys are masked while gated.
 *
 * Features:
 * - Instantiates axil5_master_rd_mon for core functionality with filtering
 * - Activity-based clock gating for the monitor subsystem
 * - Simplified for AXIL4-Lite (lower activity than full AXI4)
 * - Fine-grained power management controls
 */

`include "reset_defs.svh"
module axil5_master_rd_mon_cg
    import monitor_pkg::*;
#(
    // AXIL4 Master parameters (passed through to axil5_master_rd_mon)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXIL_ADDR_WIDTH   = 32,
    parameter int AXIL_DATA_WIDTH   = 32,

    // Monitor parameters
    parameter bit USE_MONITOR       = 1'b1,  // 0 = omit monitor in inner mon; outputs tied
    parameter int N_ADDR_RANGES     = 0,         // 0 = address-range checker disabled
    parameter bit ADDR_FILTER_ENABLE = 1'b0,  // 0 = address filter inert
    // Timer calibration, forwarded to the inner monitor. These were MISSING on
    // every _cg wrapper: not merely unforwarded but undeclared, so a clock-gated
    // build had no way to state its clock frequency and the inner
    // counter_freq_invariant LUT was always built at the 100 MHz default. Every
    // microsecond-denominated timeout was therefore miscalibrated on any board
    // not running at 100 MHz, silently. Found by qc round_29 on one wrapper;
    // it was all twelve.
    parameter int ACLK_MHZ           = 100,
    parameter int CFI_MIN_FREQ_MHZ   = ACLK_MHZ,
    parameter int CFI_MAX_FREQ_MHZ   = ACLK_MHZ,
    // Write-monitor table shaping. NUM_BANKS > 1 on a write monitor REQUIRES
    // USE_WDATA_ORDER_Q=1 (the inner module fails elaboration otherwise), so a
    // banked write monitor was simply not buildable through a _cg wrapper.
    parameter bit USE_WDATA_ORDER_Q  = 1'b0,
    parameter int NUM_BANKS          = 1,
    parameter logic [7:0]  UNIT_ID  = 8'h01,     // 8-bit Unit ID for monitor packets
    parameter logic [15:0] AGENT_ID = 16'h000A,    // 16-bit Agent ID for monitor packets
    parameter int MAX_TRANSACTIONS  = 8,     // Maximum outstanding transactions (reduced for AXIL)

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

    // Clock gating parameters (for AXIL)
    parameter int CG_IDLE_COUNT_WIDTH = 4,   // Width of the idle countdown

    // AXI5-Lite optional signal widths
    parameter int USER_WIDTH         = 4,
    parameter int LOOP_WIDTH         = 3,
    parameter int MPAM_WIDTH         = 11,
    parameter int MECID_WIDTH        = 16,
    parameter int NSAID_WIDTH        = 4,

    // AXI5-Lite optional signal groups. Passed straight through to the inner
    // transport module; the monitor never sees these signals.
    parameter bit ENABLE_USER        = 1,
    parameter bit ENABLE_TRACE       = 1,
    parameter bit ENABLE_LOOP        = 1,
    parameter bit ENABLE_MPAM        = 1,
    parameter bit ENABLE_MECID       = 1,
    parameter bit ENABLE_NSAID       = 1,
    parameter bit ENABLE_POISON      = 1,
    parameter bit ENABLE_LOCK        = 1,

    // Short params
    parameter int AW       = AXIL_ADDR_WIDTH,
    parameter int DW       = AXIL_DATA_WIDTH,
    parameter int UW       = USER_WIDTH,
    parameter int LW       = LOOP_WIDTH,
    parameter int MW       = MPAM_WIDTH,
    parameter int EW       = MECID_WIDTH,
    parameter int NW       = NSAID_WIDTH,
    parameter int PW       = (DW / 64) > 0 ? (DW / 64) : 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,
    input  logic                       cam_clear,  // sync clear of the monitor trans CAM

    // Slave AXIL Interface (Input Side)
    // Read address channel (AR)
    input  logic [AW-1:0]              fub_axil_araddr,
    input  logic [2:0]                 fub_axil_arprot,
    input  logic                    fub_axil_arlock,
    input  logic [UW-1:0]           fub_axil_aruser,
    input  logic                    fub_axil_artrace,
    input  logic [LW-1:0]           fub_axil_arloop,
    input  logic [MW-1:0]           fub_axil_armpam,
    input  logic [EW-1:0]           fub_axil_armecid,
    input  logic [NW-1:0]           fub_axil_arnsaid,
    input  logic                       fub_axil_arvalid,
    output logic                       fub_axil_arready,

    // Read data channel (R)
    output logic [DW-1:0]              fub_axil_rdata,
    output logic [1:0]                 fub_axil_rresp,
    output logic [UW-1:0]           fub_axil_ruser,
    output logic                    fub_axil_rtrace,
    output logic [LW-1:0]           fub_axil_rloop,
    output logic [PW-1:0]           fub_axil_rpoison,
    output logic                       fub_axil_rvalid,
    input  logic                       fub_axil_rready,

    // Master AXIL Interface (Output Side)
    // Read address channel (AR)
    output logic [AW-1:0]              m_axil_araddr,
    output logic [2:0]                 m_axil_arprot,
    output logic                    m_axil_arlock,
    output logic [UW-1:0]           m_axil_aruser,
    output logic                    m_axil_artrace,
    output logic [LW-1:0]           m_axil_arloop,
    output logic [MW-1:0]           m_axil_armpam,
    output logic [EW-1:0]           m_axil_armecid,
    output logic [NW-1:0]           m_axil_arnsaid,
    output logic                       m_axil_arvalid,
    input  logic                       m_axil_arready,

    // Read data channel (R)
    input  logic [DW-1:0]              m_axil_rdata,
    input  logic [1:0]                 m_axil_rresp,
    input  logic [UW-1:0]           m_axil_ruser,
    input  logic                    m_axil_rtrace,
    input  logic [LW-1:0]           m_axil_rloop,
    input  logic [PW-1:0]           m_axil_rpoison,
    input  logic                       m_axil_rvalid,
    output logic                       m_axil_rready,

    // Monitor Configuration
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
    logic int_arready, int_rready, int_busy;

    assign user_valid = fub_axil_arvalid || fub_axil_rvalid || int_busy ||
                        w_monbus_valid || (|active_transactions);
    assign axi_valid  = m_axil_arvalid || m_axil_rvalid;

    assign fub_axil_arready  = cg_gating ? 1'b0 : int_arready;
    assign m_axil_rready = cg_gating ? 1'b0 : int_rready;

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

    // -------------------------------------------------------------------------
    // Instantiate the monitor, clocked from the gated clock
    // -------------------------------------------------------------------------
    axil5_master_rd_mon #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXIL_ADDR_WIDTH         (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH         (AXIL_DATA_WIDTH),
        .USER_WIDTH         (USER_WIDTH),
        .LOOP_WIDTH         (LOOP_WIDTH),
        .MPAM_WIDTH         (MPAM_WIDTH),
        .MECID_WIDTH        (MECID_WIDTH),
        .NSAID_WIDTH        (NSAID_WIDTH),
        .ENABLE_USER        (ENABLE_USER),
        .ENABLE_TRACE       (ENABLE_TRACE),
        .ENABLE_LOOP        (ENABLE_LOOP),
        .ENABLE_MPAM        (ENABLE_MPAM),
        .ENABLE_MECID       (ENABLE_MECID),
        .ENABLE_NSAID       (ENABLE_NSAID),
        .ENABLE_POISON      (ENABLE_POISON),
        .ENABLE_LOCK        (ENABLE_LOCK),
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
        .ACLK_MHZ                (ACLK_MHZ),
        .CFI_MIN_FREQ_MHZ        (CFI_MIN_FREQ_MHZ),
        .CFI_MAX_FREQ_MHZ        (CFI_MAX_FREQ_MHZ),
        .USE_WDATA_ORDER_Q       (USE_WDATA_ORDER_Q),
        .NUM_BANKS               (NUM_BANKS),
        .N_ADDR_RANGES           (N_ADDR_RANGES)
    ) axil5_master_rd_mon_inst (
        .aclk                    (gated_aclk),
        .aresetn                 (aresetn),
        .cam_clear               (cam_clear),
        .i_mon_time              (i_mon_time),

        // Slave AXIL Interface
        .fub_axil_araddr         (fub_axil_araddr),
        .fub_axil_arprot         (fub_axil_arprot),
        .fub_axil_arlock        (fub_axil_arlock),
        .fub_axil_aruser        (fub_axil_aruser),
        .fub_axil_artrace       (fub_axil_artrace),
        .fub_axil_arloop        (fub_axil_arloop),
        .fub_axil_armpam        (fub_axil_armpam),
        .fub_axil_armecid       (fub_axil_armecid),
        .fub_axil_arnsaid       (fub_axil_arnsaid),
        .fub_axil_arvalid        (fub_axil_arvalid),
        .fub_axil_arready        (int_arready),

        .fub_axil_rdata          (fub_axil_rdata),
        .fub_axil_rresp          (fub_axil_rresp),
        .fub_axil_ruser         (fub_axil_ruser),
        .fub_axil_rtrace        (fub_axil_rtrace),
        .fub_axil_rloop         (fub_axil_rloop),
        .fub_axil_rpoison       (fub_axil_rpoison),
        .fub_axil_rvalid         (fub_axil_rvalid),
        .fub_axil_rready         (fub_axil_rready),

        // Master AXIL Interface
        .m_axil_araddr           (m_axil_araddr),
        .m_axil_arprot           (m_axil_arprot),
        .m_axil_arlock          (m_axil_arlock),
        .m_axil_aruser          (m_axil_aruser),
        .m_axil_artrace         (m_axil_artrace),
        .m_axil_arloop          (m_axil_arloop),
        .m_axil_armpam          (m_axil_armpam),
        .m_axil_armecid         (m_axil_armecid),
        .m_axil_arnsaid         (m_axil_arnsaid),
        .m_axil_arvalid          (m_axil_arvalid),
        .m_axil_arready          (m_axil_arready),

        .m_axil_rdata            (m_axil_rdata),
        .m_axil_rresp            (m_axil_rresp),
        .m_axil_ruser           (m_axil_ruser),
        .m_axil_rtrace          (m_axil_rtrace),
        .m_axil_rloop           (m_axil_rloop),
        .m_axil_rpoison         (m_axil_rpoison),
        .m_axil_rvalid           (m_axil_rvalid),
        .m_axil_rready           (int_rready),

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

        // Filtering Configuration
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

        // Monitor Bus
        .monbus_valid            (w_monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),
        .monbus_timestamp        (monbus_timestamp),

        // Status
        .busy                    (int_busy),
        .active_transactions     (active_transactions),
        .error_count             (error_count),
        .transaction_count       (transaction_count),
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
        // four axil5 _cg builds from compiling at all. Left empty because
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

endmodule : axil5_master_rd_mon_cg
