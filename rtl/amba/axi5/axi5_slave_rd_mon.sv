// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_rd_mon
// Purpose: AXI5 Slave Read with Integrated Filtered Monitoring
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_rd_mon
    import monitor_pkg::*;
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,
    parameter int AXI_CHUNKNUM_WIDTH = 4,

    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

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
    parameter logic [7:0]  UNIT_ID  = 8'h01,
    parameter logic [15:0] AGENT_ID = 16'h000C,
    parameter int MAX_TRANSACTIONS  = 16,
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
    parameter int ID_MATCH_BASE          = 0,
    parameter int ID_MATCH_COUNT         = 0,
    // Active-transaction threshold packet trip point (used when
    // cfg_threshold_enable=1). Previously hardwired, which either spammed
    // threshold packets (table larger than the hardwire) or made the feature
    // unreachable (table smaller). Scales with the table by default.
    parameter int ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2,
    parameter bit ENABLE_FILTERING  = 1,
    parameter bit ADD_PIPELINE_STAGE = 0,

    // Reporter sub-block enables (default 1'b1 = legacy behavior).
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1
)
(
    input  logic aclk,
    input  logic aresetn,
    input  logic cam_clear,  // sync clear of the monitor trans CAM

    // Slave interface signals (all AXI5 AR and R channel signals)
    input  logic [IW-1:0]                s_axi_arid,
    input  logic [AW-1:0]                s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [UW-1:0]                s_axi_aruser,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,
    input  logic [AXI_NSAID_WIDTH-1:0]   s_axi_arnsaid,
    input  logic                         s_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]    s_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0]   s_axi_armecid,
    input  logic                         s_axi_arunique,
    input  logic                         s_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0]   s_axi_artagop,

    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,
    output logic                         s_axi_rtrace,
    output logic                         s_axi_rpoison,
    output logic                         s_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] s_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0]  s_axi_rchunkstrb,
    output logic [TW-1:0]                s_axi_rtag,
    output logic                         s_axi_rtagmatch,

    // FUB interface signals (all AXI5 AR and R channel signals)
    output logic [IW-1:0]                fub_axi_arid,
    output logic [AW-1:0]                fub_axi_araddr,
    output logic [7:0]                   fub_axi_arlen,
    output logic [2:0]                   fub_axi_arsize,
    output logic [1:0]                   fub_axi_arburst,
    output logic                         fub_axi_arlock,
    output logic [3:0]                   fub_axi_arcache,
    output logic [2:0]                   fub_axi_arprot,
    output logic [3:0]                   fub_axi_arqos,
    output logic [UW-1:0]                fub_axi_aruser,
    output logic                         fub_axi_arvalid,
    input  logic                         fub_axi_arready,
    output logic [AXI_NSAID_WIDTH-1:0]   fub_axi_arnsaid,
    output logic                         fub_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]    fub_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0]   fub_axi_armecid,
    output logic                         fub_axi_arunique,
    output logic                         fub_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0]   fub_axi_artagop,

    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,
    input  logic                         fub_axi_rtrace,
    input  logic                         fub_axi_rpoison,
    input  logic                         fub_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0]  fub_axi_rchunkstrb,
    input  logic [TW-1:0]                fub_axi_rtag,
    input  logic                         fub_axi_rtagmatch,

    // Monitor configuration and output
    input  logic                       cfg_monitor_enable,
    input  logic                       cfg_error_enable,
    input  logic                       cfg_timeout_enable,
    input  logic                       cfg_perf_enable,
    input  logic                       cfg_compl_enable,     // Enable completion packets
    input  logic                       cfg_threshold_enable, // Enable threshold packets
    input  logic                       cfg_debug_enable,     // Enable debug packets
    input  logic [15:0]                cfg_timeout_cycles,
    input  logic [3:0]                 cfg_freq_sel,            // counter_freq_invariant LUT index
    input  logic [31:0]                cfg_latency_threshold,
    input  logic [15:0]                cfg_axi_pkt_mask,
    input  logic [15:0]                cfg_axi_err_select,
    input  logic [15:0]                cfg_axi_error_mask,
    input  logic [15:0]                cfg_axi_timeout_mask,
    input  logic [15:0]                cfg_axi_compl_mask,
    input  logic [15:0]                cfg_axi_thresh_mask,
    input  logic [15:0]                cfg_axi_perf_mask,
    input  logic [15:0]                cfg_axi_addr_mask,
    input  logic [15:0]                cfg_axi_debug_mask,

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                       cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]         cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0] cfg_addr_range_high,

    // Free-running monitor-time broadcast from the monbus_group family
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor Bus Output
    output logic                                    monbus_valid,            // Monitor bus valid
    input  logic                                    monbus_ready,            // Monitor bus ready
    output monitor_common_pkg::monitor_packet_t     monbus_packet,           // Monitor packet (128-bit)
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,        // Side-band sampled time
    output logic                       busy,
    output logic [7:0]                 active_transactions,
    output logic [15:0]                error_count,
    output logic [31:0]                transaction_count,
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
    output logic                       cfg_conflict_error,

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

    // Monitor backpressure plumbing (see axi4_master_rd_mon for full rationale)
    logic w_core_s_axi_arready;
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
    assign w_gated_arvalid = s_axi_arvalid & (w_block_ready | ~cfg_monitor_enable);

    // Observability tap for block_ready (see the port comment). Held to the
    // internal gating net so a testbench watching the port sees exactly what
    // the AR/AW gate sees.
    assign debug_block_ready = w_block_ready;

    axi5_slave_rd #(
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_NSAID_WIDTH(AXI_NSAID_WIDTH), .AXI_MPAM_WIDTH(AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH(AXI_MECID_WIDTH), .AXI_TAG_WIDTH(AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH(AXI_TAGOP_WIDTH), .AXI_CHUNKNUM_WIDTH(AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID(ENABLE_NSAID), .ENABLE_TRACE(ENABLE_TRACE),
        .ENABLE_MPAM(ENABLE_MPAM), .ENABLE_MECID(ENABLE_MECID),
        .ENABLE_UNIQUE(ENABLE_UNIQUE), .ENABLE_CHUNKING(ENABLE_CHUNKING),
        .ENABLE_MTE(ENABLE_MTE), .ENABLE_POISON(ENABLE_POISON)
    ) axi5_slave_rd_inst (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr), .s_axi_arlen(s_axi_arlen),
        .s_axi_arsize(s_axi_arsize), .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot), .s_axi_arqos(s_axi_arqos),
        .s_axi_aruser(s_axi_aruser), .s_axi_arvalid(w_gated_arvalid), .s_axi_arready(w_core_s_axi_arready),  // gated below
        .s_axi_arnsaid(s_axi_arnsaid), .s_axi_artrace(s_axi_artrace), .s_axi_armpam(s_axi_armpam),
        .s_axi_armecid(s_axi_armecid), .s_axi_arunique(s_axi_arunique),
        .s_axi_archunken(s_axi_archunken), .s_axi_artagop(s_axi_artagop),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata), .s_axi_rresp(s_axi_rresp),
        .s_axi_rlast(s_axi_rlast), .s_axi_ruser(s_axi_ruser), .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready), .s_axi_rtrace(s_axi_rtrace), .s_axi_rpoison(s_axi_rpoison),
        .s_axi_rchunkv(s_axi_rchunkv), .s_axi_rchunknum(s_axi_rchunknum),
        .s_axi_rchunkstrb(s_axi_rchunkstrb), .s_axi_rtag(s_axi_rtag), .s_axi_rtagmatch(s_axi_rtagmatch),
        .fub_axi_arid(fub_axi_arid), .fub_axi_araddr(fub_axi_araddr), .fub_axi_arlen(fub_axi_arlen),
        .fub_axi_arsize(fub_axi_arsize), .fub_axi_arburst(fub_axi_arburst), .fub_axi_arlock(fub_axi_arlock),
        .fub_axi_arcache(fub_axi_arcache), .fub_axi_arprot(fub_axi_arprot), .fub_axi_arqos(fub_axi_arqos),
        .fub_axi_aruser(fub_axi_aruser), .fub_axi_arvalid(fub_axi_arvalid), .fub_axi_arready(fub_axi_arready),
        .fub_axi_arnsaid(fub_axi_arnsaid), .fub_axi_artrace(fub_axi_artrace), .fub_axi_armpam(fub_axi_armpam),
        .fub_axi_armecid(fub_axi_armecid), .fub_axi_arunique(fub_axi_arunique),
        .fub_axi_archunken(fub_axi_archunken), .fub_axi_artagop(fub_axi_artagop),
        .fub_axi_rid(fub_axi_rid), .fub_axi_rdata(fub_axi_rdata), .fub_axi_rresp(fub_axi_rresp),
        .fub_axi_rlast(fub_axi_rlast), .fub_axi_ruser(fub_axi_ruser), .fub_axi_rvalid(fub_axi_rvalid),
        .fub_axi_rready(fub_axi_rready), .fub_axi_rtrace(fub_axi_rtrace), .fub_axi_rpoison(fub_axi_rpoison),
        .fub_axi_rchunkv(fub_axi_rchunkv), .fub_axi_rchunknum(fub_axi_rchunknum),
        .fub_axi_rchunkstrb(fub_axi_rchunkstrb), .fub_axi_rtag(fub_axi_rtag), .fub_axi_rtagmatch(fub_axi_rtagmatch),
        .busy(busy)
    );

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

    assign w_mon_cmd_valid  = fub_axi_arvalid & cfg_monitor_enable;
    assign w_mon_data_valid = fub_axi_rvalid & cfg_monitor_enable;
    assign w_mon_resp_valid = (fub_axi_rvalid && fub_axi_rlast) & cfg_monitor_enable;
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
            .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID), .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
            .USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q), .NUM_BANKS(NUM_BANKS),
            .ID_FILTER_ENABLE(ID_FILTER_ENABLE), .ID_MATCH_BASE(ID_MATCH_BASE), .ID_MATCH_COUNT(ID_MATCH_COUNT),
            .ADDR_WIDTH(AW), .ID_WIDTH(IW), .IS_READ(1), .IS_AXI(1),
            .ENABLE_PERF_PACKETS(1), .ENABLE_DEBUG_MODULE(0),
            .ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
            .ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
            .ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
            .ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
            .ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
            .ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
            .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE),
            .N_ADDR_RANGES(N_ADDR_RANGES)
        ) axi_monitor_inst (
            .aclk(aclk), .aresetn(aresetn),
            .clear(cam_clear | ~cfg_monitor_enable),
            .i_mon_time(i_mon_time),
            .cmd_addr(fub_axi_araddr), .cmd_id(fub_axi_arid), .cmd_len(fub_axi_arlen),
            .cmd_size(fub_axi_arsize), .cmd_burst(fub_axi_arburst),
            .cmd_valid(w_mon_cmd_valid), .cmd_ready(fub_axi_arready),
            .data_id(fub_axi_rid), .data_last(fub_axi_rlast), .data_resp(fub_axi_rresp),
            .data_valid(w_mon_data_valid), .data_ready(fub_axi_rready),
            .resp_id(fub_axi_rid), .resp_code(fub_axi_rresp),
            .resp_valid(w_mon_resp_valid), .resp_ready(fub_axi_rready),
            // cfg_freq_sel selects the counter_freq_invariant LUT entry. With the
            // default CFI_MIN==CFI_MAX==ACLK_MHZ every entry equals ACLK_MHZ, so any
            // index gives an exact 1 us tick; give the CFI a real MIN..MAX range for
            // this input to actually select a frequency.
            .cfg_freq_sel(cfg_freq_sel),
            .cfg_addr_cnt(w_timeout_cnt), .cfg_data_cnt(w_timeout_cnt), .cfg_resp_cnt(w_timeout_cnt),
            .cfg_error_enable(cfg_error_enable), .cfg_compl_enable        (cfg_compl_enable),
            .cfg_threshold_enable    (cfg_threshold_enable), .cfg_timeout_enable(cfg_timeout_enable),
            .cfg_perf_enable(cfg_perf_enable), .cfg_debug_enable        (cfg_debug_enable),
            .cfg_debug_level(4'h0), .cfg_debug_mask(16'h0),
            .cfg_active_trans_threshold(16'(ACTIVE_TRANS_THRESHOLD)), .cfg_latency_threshold(cfg_latency_threshold),
            .cfg_axi_pkt_mask(cfg_axi_pkt_mask), .cfg_axi_err_select(cfg_axi_err_select),
            .cfg_axi_error_mask(cfg_axi_error_mask), .cfg_axi_timeout_mask(cfg_axi_timeout_mask),
            .cfg_axi_compl_mask(cfg_axi_compl_mask), .cfg_axi_thresh_mask(cfg_axi_thresh_mask),
            .cfg_axi_perf_mask(cfg_axi_perf_mask), .cfg_axi_addr_mask(cfg_axi_addr_mask),
            .cfg_axi_debug_mask(cfg_axi_debug_mask),
            // Address-range checker configuration
            .cfg_addr_check_enable(cfg_addr_check_enable),
            .cfg_addr_range_enable(cfg_addr_range_enable),
            .cfg_addr_range_low(cfg_addr_range_low),
            .cfg_addr_range_high(cfg_addr_range_high),
            .monbus_valid(monbus_valid), .monbus_ready(monbus_ready), .monbus_packet(monbus_packet),
            .monbus_timestamp(monbus_timestamp),
            // block_ready stalls new ARs at s_axi_arready when monitor FIFO is
            // full. Note: monitor here watches the FUB-side handshake, so the
            // gating point and watchpoint are separated by the slave_rd core's
            // pipeline (SKID_DEPTH_AR beats of lag).
            .block_ready(w_block_ready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy(),
            /* verilator lint_on PINCONNECTEMPTY */
            .active_count(active_transactions), .cfg_conflict_error(cfg_conflict_error),

            // Performance window control + status (Stage A) + buckets (Stage B).
            .cfg_start_event_sel (cfg_start_event_sel),
            .cfg_end_event_sel   (cfg_end_event_sel),
            .cfg_start_trigger   (cfg_start_trigger),
            .cfg_end_trigger     (cfg_end_trigger),
            .cfg_window_force_close (cfg_window_force_close),
            .window_active       (window_active),
            .window_cycles       (window_cycles),
            .perf_prod_cycles    (perf_prod_cycles),
            .perf_bp_cycles      (perf_bp_cycles),
            .perf_starv_cycles   (perf_starv_cycles),
            .perf_idle_cycles    (perf_idle_cycles),
            .perf_beat_count     (perf_beat_count),
            .perf_byte_count     (perf_byte_count),
            .perf_burst_count    (perf_burst_count),
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

        // Stage A/B perfmon outputs — tied to 0 when monitor disabled.
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

    // Gate the upstream AR handshake on monitor block_ready.
    assign s_axi_arready = w_core_s_axi_arready &
           (w_block_ready | ~cfg_monitor_enable);  // disabled monitor never stalls

    // error_count / transaction_count: driven from the base monitor's
    // lifetime reporter counters (axi_monitor_reporter_perf). They count
    // packets actually EMITTED (marked into the reporter FIFO): error_count
    // covers error+timeout packets, transaction_count covers completion
    // packets. Zero when USE_MONITOR=0 or ENABLE_PERF_LOGIC=0.
    assign error_count       = w_perf_error_count;
    assign transaction_count = {16'h0, w_perf_completed_count};

endmodule : axi5_slave_rd_mon
