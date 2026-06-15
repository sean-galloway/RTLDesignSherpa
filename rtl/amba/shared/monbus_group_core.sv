// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_group_core
// Purpose: Protocol-agnostic monitor-bus capture core.
//
//   Receives a single monbus stream + side-band timestamp, applies
//   per-protocol filter masks, and routes accepted packets to either:
//
//     (a) Error / interrupt FIFO  -- drained over an AXI4-shaped slave
//         read FUB (supports burst AR). Stored 192 bits per record
//         (one packet + one timestamp). The CPU IRQ handler walks
//         records as 3 x 64-bit beats; arlen may request multiple
//         records per burst.
//
//     (b) Master-write FIFO       -- beat-granular (one queue entry =
//         one 64-bit beat). Drained over an AXI4-shaped master-write
//         FUB with watermark + timeout flush and bursts as big as
//         FIFO contents / MAX_BURST_BEATS / 4KB boundary / address
//         window wrap permit. Raw-mode bursts emit complete 24-byte
//         (3-beat) records; compressed-mode bursts emit any number of
//         self-tagged 8-byte slots.
//
//   FUB shape on both sides is AXI4: id / awlen / awsize / awburst /
//   wlast / arlen / rlast / etc. Wrappers (monbus_<p1>_<p2>_group.sv)
//   bridge the FUB into protocol-specific leaf skids: pass through for
//   AXI4 sides, supply single-beat defaults (len=0, size=$clog2(8),
//   burst=INCR, id=0) and parameter MAX_BURST_BEATS=1 on AXIL sides.
//
//   This file is the single source of truth for filtering, FIFO
//   management, compression, and the burst writer / slicer state
//   machines. The wrappers are pure structural adapters.
//
// Beat layout (raw mode, USE_COMPRESSION == 0):
//   beat 0 = {tag[3:0]=4'h0, source_ts[59:0]}
//   beat 1 = packet[127:64]
//   beat 2 = packet[63:0]
// Beat layout (compressed mode, USE_COMPRESSION == 1):
//   beat n = monbus_compressor slot; tag in bits [63:60].
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_group_core
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR        = 64,      // entries (192-bit records)
    parameter int FIFO_DEPTH_WRITE      = 96,      // beats (64-bit each) -- beat-granular
    parameter int ADDR_WIDTH            = 32,
    parameter int AXI_ID_WIDTH_M        = 1,       // master-write id (1 in AXIL builds)
    parameter int AXI_ID_WIDTH_S        = 1,       // slave-read   id (1 in AXIL builds)
    parameter int MAX_BURST_BEATS       = 1,       // master-write max beats/burst
                                                   //   AXIL builds: 1, AXI4 builds: up to 256
    parameter int FLUSH_TIMEOUT_CYCLES  = 1024,    // cycles since last beat to force flush
    parameter int NUM_PROTOCOLS         = 3,       // informational
    parameter int USE_COMPRESSION       = 0,       // 0 = raw 3-beat records, 1 = compressor
    parameter int HALF_BEAT_EN          = 0        // 1 = pack two 30-bit slots/beat
                                                   //     (requires USE_COMPRESSION==1)
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    // ------------------------------------------------------------------
    // Monitor-bus input (single stream; upstream arbitration if any)
    // ------------------------------------------------------------------
    input  logic                          monbus_valid,
    output logic                          monbus_ready,
    input  monitor_packet_t               monbus_packet,
    input  monbus_timestamp_t             monbus_timestamp,

    // Free-running timestamp out (drive to every wrapper's i_mon_time)
    output monbus_timestamp_t             mon_time_out,

    // ------------------------------------------------------------------
    // Status / IRQ / debug
    // ------------------------------------------------------------------
    output logic                          irq_out,
    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [15:0]                   err_fifo_count,    // records
    output logic [15:0]                   write_fifo_count,  // beats

    // ------------------------------------------------------------------
    // Address window + flush thresholds for master writes
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark, // beats

    // Runtime compression enable. Only meaningful when USE_COMPRESSION==1
    // (the compressor hardware is present). 1 = compress, 0 = raw 3-beat
    // records. MUST be held stable while the monitor write path is active:
    // switching it mid-stream would mix formats in the write FIFO and
    // change the burst record size (BEATS_PER_UNIT) mid-burst. Program it
    // once before monitoring starts. Tied to a constant (or unused) in
    // raw-only builds where USE_COMPRESSION==0.
    input  logic                          cfg_compress_en,

    // ------------------------------------------------------------------
    // Per-protocol filter masks (same shape as legacy monbus_axil_group)
    // ------------------------------------------------------------------
    // AXI (protocol 0)
    input  logic [15:0]                   cfg_axi_pkt_mask,
    input  logic [15:0]                   cfg_axi_err_select,
    input  logic [15:0]                   cfg_axi_error_mask,
    input  logic [15:0]                   cfg_axi_timeout_mask,
    input  logic [15:0]                   cfg_axi_compl_mask,
    input  logic [15:0]                   cfg_axi_thresh_mask,
    input  logic [15:0]                   cfg_axi_perf_mask,
    input  logic [15:0]                   cfg_axi_addr_mask,
    input  logic [15:0]                   cfg_axi_debug_mask,
    // AXIS (protocol 1)
    input  logic [15:0]                   cfg_axis_pkt_mask,
    input  logic [15:0]                   cfg_axis_err_select,
    input  logic [15:0]                   cfg_axis_error_mask,
    input  logic [15:0]                   cfg_axis_timeout_mask,
    input  logic [15:0]                   cfg_axis_compl_mask,
    input  logic [15:0]                   cfg_axis_credit_mask,
    input  logic [15:0]                   cfg_axis_channel_mask,
    input  logic [15:0]                   cfg_axis_stream_mask,
    // CORE (protocol 4)
    input  logic [15:0]                   cfg_core_pkt_mask,
    input  logic [15:0]                   cfg_core_err_select,
    input  logic [15:0]                   cfg_core_error_mask,
    input  logic [15:0]                   cfg_core_timeout_mask,
    input  logic [15:0]                   cfg_core_compl_mask,
    input  logic [15:0]                   cfg_core_thresh_mask,
    input  logic [15:0]                   cfg_core_perf_mask,
    input  logic [15:0]                   cfg_core_debug_mask,

    // ------------------------------------------------------------------
    // Compressor stats (zero in raw mode; live when USE_COMPRESSION == 1)
    // ------------------------------------------------------------------
    output logic [31:0]                   mon_compressor_stat_tier1_a,
    output logic [31:0]                   mon_compressor_stat_tier1_b,
    output logic [31:0]                   mon_compressor_stat_tier1_c,
    output logic [31:0]                   mon_compressor_stat_tier0,
    output logic [31:0]                   mon_compressor_stat_cam_miss,
    output logic [31:0]                   mon_compressor_stat_delta_ts_ovf,
    output logic [31:0]                   mon_compressor_stat_event_data_ovf,
    output logic [31:0]                   mon_compressor_stat_ed_delta_ovf,

    // ------------------------------------------------------------------
    // AXI4-shaped master-write FUB (driven by core, bridged by wrapper)
    // ------------------------------------------------------------------
    output logic [AXI_ID_WIDTH_M-1:0]     fub_m_awid,
    output logic [ADDR_WIDTH-1:0]         fub_m_awaddr,
    output logic [7:0]                    fub_m_awlen,
    output logic [2:0]                    fub_m_awsize,
    output logic [1:0]                    fub_m_awburst,
    output logic                          fub_m_awvalid,
    input  logic                          fub_m_awready,

    output logic [63:0]                   fub_m_wdata,
    output logic [7:0]                    fub_m_wstrb,
    output logic                          fub_m_wlast,
    output logic                          fub_m_wvalid,
    input  logic                          fub_m_wready,

    input  logic [AXI_ID_WIDTH_M-1:0]     fub_m_bid,    // ignored
    input  logic [1:0]                    fub_m_bresp,  // ignored
    input  logic                          fub_m_bvalid,
    output logic                          fub_m_bready,

    // ------------------------------------------------------------------
    // AXI4-shaped slave-read FUB (driven by wrapper, answered by core)
    // ------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH_S-1:0]     fub_s_arid,
    input  logic [ADDR_WIDTH-1:0]         fub_s_araddr,
    input  logic [7:0]                    fub_s_arlen,
    input  logic [2:0]                    fub_s_arsize,
    input  logic [1:0]                    fub_s_arburst,
    input  logic                          fub_s_arvalid,
    output logic                          fub_s_arready,

    output logic [AXI_ID_WIDTH_S-1:0]     fub_s_rid,
    output logic [63:0]                   fub_s_rdata,
    output logic [1:0]                    fub_s_rresp,
    output logic                          fub_s_rlast,
    output logic                          fub_s_rvalid,
    input  logic                          fub_s_rready
);

    // ==================================================================
    // Local parameters
    // ==================================================================

    localparam int BYTES_PER_BEAT   = 8;                   // 64-bit beats
    localparam logic [3:0] WRITE_TAG_RAW = 4'h0;

    // Runtime compression select. The compressor hardware exists only when
    // USE_COMPRESSION==1; cfg_compress_en then picks compressed vs raw at
    // run time. In raw-only builds w_use_comp is constant 0 (the
    // USE_COMPRESSION!=0 term folds away), so cfg_compress_en is a
    // don't-care and the expander path is always selected.
    logic        w_use_comp;
    assign w_use_comp = (USE_COMPRESSION != 0) && cfg_compress_en;

    // Record size for the burst-writer geometry: raw records are 3 beats
    // (ts, pkt_hi, pkt_lo); compressed slots are self-contained 1-beat
    // units. Runtime now that compression is runtime-selectable.
    logic [15:0] w_beats_per_unit;
    assign w_beats_per_unit = w_use_comp ? 16'd1 : 16'd3;

    // Round-to-whole-record (raw mode) = X - (X mod 3). The mod-3 comes from
    // mod_3_compress instances (u_mod3_geo / u_mod3_fifo, below): the div15
    // carry-save-compressor idiom applied to the operation we actually need --
    // a base-4 digit sum reduced by 3:2 compressors. A few LUTs, not a wide
    // reciprocal-multiply tree by the compressor CAM.
    logic [1:0] w_geo_rem3;     // s2_beats_planned mod 3
    logic [1:0] w_fifo_rem3;    // r_fifo_beats     mod 3

    localparam int ERR_REC_WIDTH    = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;
    localparam int WRITE_FIFO_AW    = $clog2(FIFO_DEPTH_WRITE);

    // Suppress lint warnings on params held for API stability
    /* verilator lint_off UNUSEDPARAM */
    localparam int NUM_PROTOCOLS_LP = NUM_PROTOCOLS;
    /* verilator lint_on UNUSEDPARAM */

    // ==================================================================
    // Internal signals
    // ==================================================================

    // Filtering
    logic [3:0]                      pkt_type;
    logic [3:0]                      pkt_protocol;
    logic [7:0]                      pkt_event_code;
    logic [3:0]                      ec_idx;
    logic                            ec_in_mask_range;
    /* verilator lint_off UNUSED */
    logic [63:0]                     pkt_event_data;
    /* verilator lint_on UNUSED */
    logic                            pkt_drop;
    logic                            pkt_to_err_fifo;
    logic                            pkt_to_write_path;
    logic                            pkt_event_masked;

    monbus_timestamp_t               r_ts_counter;

    // Err FIFO (record-granular, 192-bit)
    logic                            err_fifo_wr_valid;
    logic                            err_fifo_wr_ready;
    logic [ERR_REC_WIDTH-1:0]        err_fifo_wr_data;
    logic                            err_fifo_rd_valid;
    logic                            err_fifo_rd_ready;
    logic [ERR_REC_WIDTH-1:0]        err_fifo_rd_data;
    logic                            err_fifo_empty;
    logic [$clog2(FIFO_DEPTH_ERR):0] err_fifo_count_full;

    // Write FIFO (beat-granular, 64-bit)
    logic                            write_fifo_wr_valid;
    logic                            write_fifo_wr_ready;
    logic [63:0]                     write_fifo_wr_data;
    logic                            write_fifo_rd_valid;
    logic                            write_fifo_rd_ready;
    logic [63:0]                     write_fifo_rd_data;
    logic                            write_fifo_empty;
    logic [WRITE_FIFO_AW:0]          write_fifo_beat_count;

    // ==================================================================
    // Free-running timestamp counter
    // ==================================================================

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_ts_counter <= '0;
        end else begin
            r_ts_counter <= r_ts_counter + 1'b1;
        end
    )

    assign mon_time_out = r_ts_counter;

    // ==================================================================
    // Packet analysis + filter
    // ==================================================================

    assign pkt_type       = get_packet_type(monbus_packet);
    assign pkt_protocol   = monbus_packet[108:105];
    assign pkt_event_code = get_event_code(monbus_packet);
    assign pkt_event_data = get_event_data(monbus_packet);

    assign ec_idx           = pkt_event_code[3:0];
    assign ec_in_mask_range = (pkt_event_code[7:4] == 4'h0);

    always_comb begin
        pkt_drop          = 1'b0;
        pkt_to_err_fifo   = 1'b0;
        pkt_to_write_path = 1'b0;
        pkt_event_masked  = 1'b0;

        if (monbus_valid) begin
            case (pkt_protocol)
                PROTOCOL_AXI: begin
                    pkt_drop        = cfg_axi_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;
                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_axi_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_axi_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask  [ec_idx];
                            PktTypeThreshold:  pkt_event_masked = cfg_axi_thresh_mask [ec_idx];
                            PktTypePerf:       pkt_event_masked = cfg_axi_perf_mask   [ec_idx];
                            PktTypeAddrMatch:  pkt_event_masked = cfg_axi_addr_mask   [ec_idx];
                            PktTypeDebug:      pkt_event_masked = cfg_axi_debug_mask  [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end
                PROTOCOL_AXIS: begin
                    pkt_drop        = cfg_axis_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_axis_err_select[pkt_type] && !pkt_drop;
                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_axis_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_axis_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_axis_compl_mask  [ec_idx];
                            PktTypeCredit:     pkt_event_masked = cfg_axis_credit_mask [ec_idx];
                            PktTypeChannel:    pkt_event_masked = cfg_axis_channel_mask[ec_idx];
                            PktTypeStream:     pkt_event_masked = cfg_axis_stream_mask [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end
                PROTOCOL_CORE: begin
                    pkt_drop        = cfg_core_pkt_mask[pkt_type];
                    pkt_to_err_fifo = cfg_core_err_select[pkt_type] && !pkt_drop;
                    if (ec_in_mask_range) begin
                        case (pkt_type)
                            PktTypeError:      pkt_event_masked = cfg_core_error_mask  [ec_idx];
                            PktTypeTimeout:    pkt_event_masked = cfg_core_timeout_mask[ec_idx];
                            PktTypeCompletion: pkt_event_masked = cfg_core_compl_mask  [ec_idx];
                            PktTypeThreshold:  pkt_event_masked = cfg_core_thresh_mask [ec_idx];
                            PktTypePerf:       pkt_event_masked = cfg_core_perf_mask   [ec_idx];
                            PktTypeDebug:      pkt_event_masked = cfg_core_debug_mask  [ec_idx];
                            default:           pkt_event_masked = 1'b0;
                        endcase
                    end
                end
                default: pkt_drop = 1'b1;
            endcase

            if (pkt_event_masked) begin
                pkt_drop        = 1'b1;
                pkt_to_err_fifo = 1'b0;
            end

            pkt_to_write_path = !pkt_drop && !pkt_to_err_fifo;
        end
    end

    // ==================================================================
    // Err FIFO (record-granular 192-bit; same layout as legacy module)
    // ==================================================================

    assign err_fifo_wr_valid = monbus_valid && pkt_to_err_fifo && !pkt_drop;
    assign err_fifo_wr_data  = {monbus_timestamp, monbus_packet};

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (ERR_REC_WIDTH),
        .DEPTH      (FIFO_DEPTH_ERR)
    ) u_err_fifo (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (err_fifo_wr_valid),
        .wr_ready    (err_fifo_wr_ready),
        .wr_data     (err_fifo_wr_data),
        .rd_valid    (err_fifo_rd_valid),
        .rd_ready    (err_fifo_rd_ready),
        .rd_data     (err_fifo_rd_data),
        .count       (err_fifo_count_full)
    );

    assign err_fifo_empty = !err_fifo_rd_valid;
    assign err_fifo_full  = !err_fifo_wr_ready;
    assign irq_out        = !err_fifo_empty;
    assign err_fifo_count = {{(16-$clog2(FIFO_DEPTH_ERR)-1){1'b0}}, err_fifo_count_full};

    // ==================================================================
    // Slave-read drain  (AXI4-shaped FUB, supports burst AR)
    //
    // A burst of (arlen+1) beats slices `(arlen+1)` 64-bit chunks out of
    // consecutive 192-bit err-FIFO records. Slice order is:
    //   slice 0 = {tag=4'h0, source_ts[59:0]}
    //   slice 1 = packet[127:64]
    //   slice 2 = packet[63:0]
    // The FIFO record is popped on slice 2. The CPU should size arlen as
    // a multiple-of-3 minus one to cleanly land on record boundaries
    // (the slicer doesn't enforce this; misaligned bursts simply leave
    // the next AR pointing mid-record).
    //
    // AR is accepted only when the slicer is at slice 0 AND the FIFO
    // has at least one record buffered. rvalid drops mid-burst if the
    // FIFO underruns (the slicer waits at slice 0 until a new record
    // arrives, then resumes). rlast asserts on the (arlen+1)-th beat.
    // ==================================================================

    typedef enum logic [1:0] {
        SLICE_SRC_TS = 2'd0,
        SLICE_PKT_HI = 2'd1,
        SLICE_PKT_LO = 2'd2,
        SLICE_RSVD   = 2'd3
    } read_slice_t;

    read_slice_t                   r_slice_idx;
    logic [8:0]                    r_rd_beats_remaining;   // arlen is 8 bits -> need 9 bits for "arlen+1"
    logic                          r_rd_in_burst;
    logic [AXI_ID_WIDTH_S-1:0]     r_rd_burst_id;

    // arready: accept a new burst only when we're idle (no burst in flight)
    assign fub_s_arready = !r_rd_in_burst;

    // rvalid: a slice is available whenever a burst is active AND the
    // err FIFO has a record we can slice from.
    assign fub_s_rvalid  = r_rd_in_burst && !err_fifo_empty;

    // rlast on the final beat of the burst (r_rd_beats_remaining == 1)
    assign fub_s_rlast   = r_rd_in_burst && (r_rd_beats_remaining == 9'd1);

    // rid echoes the burst id throughout the burst
    assign fub_s_rid     = r_rd_burst_id;
    assign fub_s_rresp   = 2'b00; // OKAY

    // rdata multiplexer
    always_comb begin
        unique case (r_slice_idx)
            SLICE_SRC_TS: fub_s_rdata = {WRITE_TAG_RAW,
                                         err_fifo_rd_data[MONBUS_PKT_WIDTH+59:MONBUS_PKT_WIDTH]};
            SLICE_PKT_HI: fub_s_rdata = err_fifo_rd_data[MONBUS_PKT_WIDTH-1:64];
            SLICE_PKT_LO: fub_s_rdata = err_fifo_rd_data[63:0];
            default:      fub_s_rdata = '0;
        endcase
    end

    // Pop FIFO only when the slicer completes a record (slice 2 fires)
    assign err_fifo_rd_ready = fub_s_rvalid && fub_s_rready
                            && (r_slice_idx == SLICE_PKT_LO);

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_slice_idx          <= SLICE_SRC_TS;
            r_rd_beats_remaining <= 9'd0;
            r_rd_in_burst        <= 1'b0;
            r_rd_burst_id        <= '0;
        end else begin
            // Start of burst: latch arlen+1 and id
            if (fub_s_arvalid && fub_s_arready) begin
                r_rd_in_burst        <= 1'b1;
                r_rd_beats_remaining <= {1'b0, fub_s_arlen} + 9'd1;
                r_rd_burst_id        <= fub_s_arid;
            end

            // Beat retire
            if (fub_s_rvalid && fub_s_rready) begin
                r_rd_beats_remaining <= r_rd_beats_remaining - 9'd1;
                if (r_slice_idx == SLICE_PKT_LO) begin
                    r_slice_idx <= SLICE_SRC_TS;
                end else begin
                    r_slice_idx <= read_slice_t'(r_slice_idx + 2'd1);
                end
                // End of burst
                if (r_rd_beats_remaining == 9'd1) begin
                    r_rd_in_burst <= 1'b0;
                end
            end
        end
    )

    // Suppress lint: arsize/arburst not used (we always emit 64-bit INCR)
    /* verilator lint_off UNUSED */
    logic [2:0] _unused_arsize  = fub_s_arsize;
    logic [1:0] _unused_arburst = fub_s_arburst;
    logic [ADDR_WIDTH-1:0] _unused_araddr = fub_s_araddr;
    /* verilator lint_on UNUSED */

    // ==================================================================
    // Write path -- raw 3-beat expander and (optionally) the compressor
    // both feed the 64-bit write FIFO; cfg_compress_en (via w_use_comp)
    // selects which one is active at run time.
    //
    //   raw  (w_use_comp == 0): a 3-state expander pushes {ts, pkt_hi,
    //     pkt_lo} beats into the FIFO atomically (a record is never split
    //     across backpressure).
    //   comp (w_use_comp == 1): monbus_compressor sits between the input
    //     and the FIFO; each emitted slot is one beat.
    //
    // The expander is always elaborated (a cheap FSM). The compressor is
    // elaborated only when USE_COMPRESSION==1 (it owns the CAM, the
    // expensive part); in raw-only builds its nets are tied off and
    // w_use_comp is constant 0. Only one path is ever active (gated by
    // w_use_comp), so the two FIFO-write outputs are simply muxed.
    // ==================================================================

    // Expander outputs (active when !w_use_comp).
    logic        exp_wr_valid;
    logic [63:0] exp_wr_data;
    logic        exp_term;        // "expander accepted the input this cycle"
    // Compressor outputs (active when w_use_comp; tied 0 when absent).
    logic        comp_wr_valid;
    logic [63:0] comp_wr_data;
    logic        comp_in_ready;

    // ---- Raw 3-beat expander (always present) ----
    typedef enum logic [1:0] {
        EXP_TS   = 2'd0,
        EXP_HI   = 2'd1,
        EXP_LO   = 2'd2,
        EXP_RSVD = 2'd3
    } exp_state_t;

    exp_state_t                  r_exp_state;
    monitor_packet_t             r_lat_packet;
    monbus_timestamp_t           r_lat_source_ts;

    // Start a record only when raw mode is selected (!w_use_comp). Once
    // started (EXP_TS handshake) the expander commits to driving the other
    // two beats with wvalid held high until each is accepted (atomicity:
    // monbus_valid is not polled in EXP_HI/EXP_LO). Per-beat wr_ready is
    // used (not a "3 slots free" precheck) to avoid a count -> wr_valid ->
    // count combinational loop. With compression enabled the expander sits
    // idle in EXP_TS and drives nothing.
    logic exp_accepting_now;
    assign exp_accepting_now = (r_exp_state == EXP_TS)
                            && monbus_valid && pkt_to_write_path && !w_use_comp;

    always_comb begin
        exp_wr_valid = 1'b0;
        exp_wr_data  = 64'd0;
        unique case (r_exp_state)
            EXP_TS:   if (exp_accepting_now) begin
                          exp_wr_valid = 1'b1;
                          exp_wr_data  = {WRITE_TAG_RAW, monbus_timestamp[59:0]};
                      end
            EXP_HI:   begin
                          exp_wr_valid = 1'b1;
                          exp_wr_data  = r_lat_packet[MONBUS_PKT_WIDTH-1:64];
                      end
            EXP_LO:   begin
                          exp_wr_valid = 1'b1;
                          exp_wr_data  = r_lat_packet[63:0];
                      end
            default:  ;
        endcase
    end

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_exp_state     <= EXP_TS;
            r_lat_packet    <= '0;
            r_lat_source_ts <= '0;
        end else begin
            unique case (r_exp_state)
                EXP_TS: if (exp_accepting_now && write_fifo_wr_ready) begin
                            r_lat_packet    <= monbus_packet;
                            r_lat_source_ts <= monbus_timestamp;
                            r_exp_state     <= EXP_HI;
                        end
                EXP_HI: if (write_fifo_wr_ready) r_exp_state <= EXP_LO;
                EXP_LO: if (write_fifo_wr_ready) r_exp_state <= EXP_TS;
                default: r_exp_state <= EXP_TS;
            endcase
        end
    )

    // raw-mode input handshake term for monbus_ready.
    assign exp_term = exp_accepting_now && write_fifo_wr_ready;

    // Keep the latched source ts visible to lint (latch kept for future
    // format work).
    /* verilator lint_off UNUSED */
    monbus_timestamp_t _unused_lat_ts = r_lat_source_ts;
    /* verilator lint_on UNUSED */

    // ---- Compressor (present only when USE_COMPRESSION==1) ----
    generate
    if (USE_COMPRESSION != 0) begin : gen_compressor

        // monbus_compressor consumes (packet, source_ts) records and
        // emits 64-bit self-tagged slots. Records are fed only while
        // compression is enabled (w_use_comp).
        //
        // Input skid: the monbus aggregator's output skid sits far from this
        // compressor's CAM, so the combinational path aggregator -> in_key ->
        // 32-way CAM match/commit was the route-dominated 100 MHz worst path
        // (~74% routing). A 2-deep skid registers (source_ts, packet) right
        // at the compressor boundary, so that long hop ends at a LOCAL flop
        // and the CAM lookup starts fresh from it. Full throughput preserved
        // (skid), +1 cycle latency on the compression path (sanctioned), and
        // the record sequence is unchanged so the slot stream stays bit-exact.
        localparam int COMP_IN_W = MONBUS_TS_WIDTH + MONBUS_PKT_WIDTH;
        logic                 comp_skid_wr_valid;
        logic                 comp_skid_wr_ready;
        logic [COMP_IN_W-1:0] comp_skid_wr_data;
        logic                 comp_skid_rd_valid;
        logic                 comp_core_in_ready;
        logic [COMP_IN_W-1:0] comp_skid_rd_data;
        monitor_packet_t      comp_in_packet;
        monbus_timestamp_t    comp_in_source_ts;
        logic        comp_out_valid;
        logic        comp_out_ready;
        logic [63:0] comp_out_slot;
        logic        comp_out_half_valid;
        logic [29:0] comp_out_half_slot;

        assign comp_skid_wr_valid = monbus_valid && pkt_to_write_path
                                 && !pkt_drop && w_use_comp;
        assign comp_skid_wr_data  = {monbus_timestamp, monbus_packet};

        gaxi_skid_buffer #(.DATA_WIDTH(COMP_IN_W), .DEPTH(2)) u_comp_in_skid (
            .axi_aclk    (axi_aclk),
            .axi_aresetn (axi_aresetn),
            .wr_valid    (comp_skid_wr_valid),
            .wr_ready    (comp_skid_wr_ready),
            .wr_data     (comp_skid_wr_data),
            .count       (),
            .rd_valid    (comp_skid_rd_valid),
            .rd_ready    (comp_core_in_ready),
            .rd_count    (),
            .rd_data     (comp_skid_rd_data)
        );
        assign {comp_in_source_ts, comp_in_packet} = comp_skid_rd_data;
        // A record is consumed off monbus when the skid accepts it.
        assign comp_in_ready = comp_skid_wr_ready;

        monbus_compressor #(
            .HALF_BEAT_EN        (HALF_BEAT_EN)
        ) u_compressor (
            .clk                 (axi_aclk),
            .rst_n               (axi_aresetn),

            .in_valid            (comp_skid_rd_valid),
            .in_ready            (comp_core_in_ready),
            .in_packet           (comp_in_packet),
            .in_source_ts        (comp_in_source_ts),

            .out_valid           (comp_out_valid),
            .out_ready           (comp_out_ready),
            .out_slot            (comp_out_slot),
            .out_half_valid      (comp_out_half_valid),
            .out_half_slot       (comp_out_half_slot),

            .stat_tier1_a        (mon_compressor_stat_tier1_a),
            .stat_tier1_b        (mon_compressor_stat_tier1_b),
            .stat_tier1_c        (mon_compressor_stat_tier1_c),
            .stat_tier0          (mon_compressor_stat_tier0),
            .stat_cam_miss       (mon_compressor_stat_cam_miss),
            .stat_delta_ts_ovf   (mon_compressor_stat_delta_ts_ovf),
            .stat_event_data_ovf (mon_compressor_stat_event_data_ovf),
            .stat_ed_delta_ovf   (mon_compressor_stat_ed_delta_ovf)
        );

        // ---- Optional half-beat packer (HALF_BEAT_EN==1) ----
        // Packs two 30-bit half-slots per beat downstream of the compressor.
        // When disabled the compressor drives the write FIFO directly (the
        // committed, timing-closed path).
        if (HALF_BEAT_EN != 0) begin : gen_halfbeat_packer
            monbus_halfbeat_packer u_packer (
                .clk           (axi_aclk),
                .rst_n         (axi_aresetn),
                .in_valid      (comp_out_valid),
                .in_ready      (comp_out_ready),
                .in_slot       (comp_out_slot),
                .in_half_valid (comp_out_half_valid),
                .in_half_slot  (comp_out_half_slot),
                .out_valid     (comp_wr_valid),
                .out_ready     (write_fifo_wr_ready),
                .out_slot      (comp_wr_data)
            );
        end else begin : gen_no_halfbeat
            assign comp_wr_valid  = comp_out_valid;
            assign comp_wr_data   = comp_out_slot;
            assign comp_out_ready = write_fifo_wr_ready;
        end

    end else begin : gen_no_compressor

        // Compressor hardware absent; tie its nets off. w_use_comp is a
        // constant 0 in this build, so these are never selected anyway.
        assign comp_wr_valid = 1'b0;
        assign comp_wr_data  = 64'd0;
        assign comp_in_ready = 1'b0;
        assign mon_compressor_stat_tier1_a        = 32'd0;
        assign mon_compressor_stat_tier1_b        = 32'd0;
        assign mon_compressor_stat_tier1_c        = 32'd0;
        assign mon_compressor_stat_tier0          = 32'd0;
        assign mon_compressor_stat_cam_miss       = 32'd0;
        assign mon_compressor_stat_delta_ts_ovf   = 32'd0;
        assign mon_compressor_stat_event_data_ovf = 32'd0;
        assign mon_compressor_stat_ed_delta_ovf   = 32'd0;

    end
    endgenerate

    // ---- Select the active path into the write FIFO ----
    assign write_fifo_wr_valid = w_use_comp ? comp_wr_valid : exp_wr_valid;
    assign write_fifo_wr_data  = w_use_comp ? comp_wr_data  : exp_wr_data;

    assign monbus_ready = pkt_drop
                       || (pkt_to_err_fifo && err_fifo_wr_ready)
                       || (pkt_to_write_path && (w_use_comp ? comp_in_ready
                                                            : exp_term));

    // ==================================================================
    // Write FIFO -- beat-granular (one queue entry = one 64-bit beat)
    // ==================================================================

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (64),
        .DEPTH      (FIFO_DEPTH_WRITE)
    ) u_write_fifo (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .wr_valid    (write_fifo_wr_valid),
        .wr_ready    (write_fifo_wr_ready),
        .wr_data     (write_fifo_wr_data),
        .rd_valid    (write_fifo_rd_valid),
        .rd_ready    (write_fifo_rd_ready),
        .rd_data     (write_fifo_rd_data),
        .count       (write_fifo_beat_count)
    );

    assign write_fifo_empty = !write_fifo_rd_valid;
    assign write_fifo_full  = !write_fifo_wr_ready;
    assign write_fifo_count = {{(16-WRITE_FIFO_AW-1){1'b0}}, write_fifo_beat_count};

    // ==================================================================
    // Master-write burst writer
    //
    //   Triggers a flush burst when either:
    //     (a) write_fifo_beat_count >= cfg_flush_watermark
    //     (b) timeout: FLUSH_TIMEOUT_CYCLES since the last accepted W
    //         handshake AND the FIFO holds at least BEATS_PER_UNIT beats.
    //
    //   Burst length (in beats), chosen at the start of each burst:
    //     beats = min(write_fifo_beat_count,
    //                 MAX_BURST_BEATS,
    //                 beats_to_limit,         // staying inside cfg_limit
    //                 beats_to_4kb_boundary)
    //     beats = (beats / BEATS_PER_UNIT) * BEATS_PER_UNIT
    //   If beats < BEATS_PER_UNIT after rounding, attempt a rewind to
    //   cfg_base_addr and re-check. If still 0, give up this cycle (wait
    //   for more data or for the address window to allow a unit).
    //
    //   No mid-burst wrap: the burst is sized so the last byte is <=
    //   cfg_limit_addr AND does not cross the 4KB boundary AXI4 demands.
    // ==================================================================

    typedef enum logic [2:0] {
        WR_IDLE  = 3'd0,
        WR_AW    = 3'd1,
        WR_W     = 3'd2,
        WR_B     = 3'd3
    } wr_state_t;

    wr_state_t                   r_wr_state;
    logic [ADDR_WIDTH-1:0]       r_wr_addr;
    logic [ADDR_WIDTH-1:0]       r_aw_addr;          // latched AW address
    logic [7:0]                  r_aw_len;           // latched awlen (=sub-burst beats-1)
    logic [8:0]                  r_w_beats_remaining; // beats left in current sub-burst W
    logic [15:0]                 r_unit_remaining;   // beats left in this drain cycle
    logic [31:0]                 r_timeout_cnt;

    // Beats geometry. The ADDRESS-derived drain-plan math (window / 4KB
    // caps off r_wr_addr, the min tree, and the whole-record rounding) is a
    // long combinational chain; doing it in the same cycle as the WR_IDLE
    // -> WR_AW commit was the 100 MHz critical path (it fed straight back
    // into r_wr_addr). r_wr_addr is STABLE while the writer sits in WR_IDLE
    // (only WR_W advances it), so that math is pipelined over 3 registered
    // stages and the FSM consumes the pre-computed plan (r_plan_*).
    // geom_valid gates the commit until the pipeline reflects the settled
    // r_wr_addr.
    //
    // IMPORTANT: the FIFO-occupancy cap is NOT pipelined -- the FIFO keeps
    // filling while the writer sits in WR_IDLE, so a pipelined (3-cycle
    // stale) FIFO count would short the burst (e.g. drain 21 of 24 beats
    // when the watermark fires). Instead the pipeline produces a purely
    // address-feasible whole-record count (r_plan_geo_units) and the FRESH
    // FIFO cap is applied combinationally at commit. Because floor-to-whole-
    // records is monotonic, min(round(geo), round(fifo)) == round(min) -- so
    // rounding each side independently is exact. The fresh-FIFO path starts
    // from a fast counter (no address subtract/shift), so it does not
    // recreate the critical path.
    //
    // Final burst length is min(r_plan_geo_units, w_fifo_units) (16 bits) but
    // only the low 9 bits go to AWLEN (AXI4 arlen+1, max 256 beats).
    logic [15:0]                 beats_in_fifo;
    // stage 1: per-cap geometry from a stable r_wr_addr
    logic [15:0]                 s1_beats_to_limit;
    logic [15:0]                 s1_beats_to_4kb;
    logic                        s1_in_window;
    logic [ADDR_WIDTH-1:0]       s1_wr_addr;
    // stage 2: planned beats (geometry cap only)
    logic [15:0]                 s2_beats_planned;
    logic                        s2_in_window;
    logic [ADDR_WIDTH-1:0]       s2_wr_addr;
    // stage 3: GEOMETRY-only whole-record cap + effective start address.
    // (The FIFO cap is applied fresh at commit -- see header note.)
    logic [15:0]                 r_plan_geo_units;   // address-feasible whole-record beats
    logic [ADDR_WIDTH-1:0]       r_plan_addr;
    logic                        r_plan_ok;          // geometry allows >= 1 record
    // Registered raw FIFO beat count. beats_in_fifo is combinationally live
    // (it reflects the in-flight write, traced back through the packet
    // filter and the far-placed config registers), so using it directly at
    // commit put a deep cone -- plus the runtime /3 -- on the WR_IDLE
    // critical path. Register the raw count once; BOTH the flush trigger
    // and the burst cap derive from this same flop (see w_fifo_units), so
    // they stay consistent (the earlier split -- fresh trigger vs lagged
    // cap -- shorted the burst to 21/24). The whole-record rounding is then
    // a short combinational op off this flop.
    logic [15:0]                 r_fifo_beats;
    // pipeline settled against the current r_wr_addr
    logic [1:0]                  r_geom_settle;
    logic                        geom_valid;
    // flush triggers (short combinational paths off beats_in_fifo / cnt)
    logic                        flush_trigger_watermark;
    logic                        flush_trigger_timeout;
    logic                        have_one_unit;
    logic                        do_flush;

    assign beats_in_fifo = {{(16-WRITE_FIFO_AW-1){1'b0}}, write_fifo_beat_count};

    // Pipeline reflects the settled r_wr_addr once it has been stable for
    // the full pipeline depth (3 stages). r_geom_settle resets whenever
    // the writer leaves WR_IDLE (r_wr_addr starts moving) in the FSM below.
    assign geom_valid = (r_geom_settle == 2'd3);

    // 3-stage geometry pipeline. Each stage is a shallow slice of the old
    // single-cycle chain that used to feed straight back into r_wr_addr
    // (the 100 MHz critical path). Stage N reads stage N-1's registers, so
    // the plan trails r_wr_addr by 3 cycles -- harmless because r_wr_addr
    // is stable in WR_IDLE and the FIFO only grows there.
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            s1_beats_to_limit <= 16'd0;
            s1_beats_to_4kb   <= 16'd0;
            s1_in_window      <= 1'b0;
            s1_wr_addr        <= '0;
            s2_beats_planned  <= 16'd0;
            s2_in_window      <= 1'b0;
            s2_wr_addr        <= '0;
            r_plan_geo_units  <= 16'd0;
            r_plan_addr       <= '0;
            r_plan_ok         <= 1'b0;
            r_fifo_beats      <= 16'd0;
        end else begin
            // Registered raw FIFO beat count (the trigger + cap both use it).
            r_fifo_beats <= beats_in_fifo;
            // ---- stage 1: window test + per-cap geometry off r_wr_addr.
            // beats_to_limit = ((limit - geom - 7) >> 3) + 1 when it fits,
            // else 0 -- computed without the +1 overflow the legacy form
            // hit at limit=0xFFFF_FFFF (see the flush-bug postmortem).
            begin : stage1
                logic                  in_w;
                logic [ADDR_WIDTH-1:0] gaddr;
                logic [ADDR_WIDTH-1:0] diff;
                logic [ADDR_WIDTH-1:0] beats_raw;
                logic [12:0]           bytes4;
                in_w      = (r_wr_addr >= cfg_base_addr) && (r_wr_addr <= cfg_limit_addr);
                gaddr     = in_w ? r_wr_addr : cfg_base_addr;
                diff      = cfg_limit_addr - gaddr;
                beats_raw = (diff < ADDR_WIDTH'(7)) ? '0
                          : (((diff - ADDR_WIDTH'(7)) >> 3) + ADDR_WIDTH'(1));
                bytes4    = 13'h1000 - {1'b0, gaddr[11:0]};
                s1_in_window      <= in_w;
                s1_wr_addr        <= r_wr_addr;
                s1_beats_to_limit <= (beats_raw > ADDR_WIDTH'(16'hFFFF))
                                     ? 16'hFFFF : beats_raw[15:0];
                s1_beats_to_4kb   <= {6'd0, bytes4[12:3]};
            end

            // ---- stage 2: cap by GEOMETRY only (min of window / 4KB). The
            // FIFO cap is intentionally NOT applied here -- it is applied
            // fresh at commit (see header note) so a stale FIFO count cannot
            // short the burst.
            begin : stage2
                logic [15:0] cap_geo;
                cap_geo = (s1_beats_to_limit < s1_beats_to_4kb)
                        ? s1_beats_to_limit : s1_beats_to_4kb;
                s2_beats_planned <= cap_geo;
                s2_in_window     <= s1_in_window;
                s2_wr_addr       <= s1_wr_addr;
            end

            // ---- stage 3: round the geometry cap down to whole records
            // (keeps the memory image on record boundaries) + effective
            // start address (rewind to base when out of window or a record
            // doesn't fit by geometry). Round-down = X - (X mod 3), with the
            // mod-3 from u_mod3_geo.
            begin : stage3
                logic [15:0] units;
                logic        rew;
                units = (w_beats_per_unit == 16'd1)
                      ? s2_beats_planned
                      : (s2_beats_planned - 16'(w_geo_rem3));
                rew   = !s2_in_window || (units < w_beats_per_unit);
                r_plan_geo_units <= units;
                r_plan_addr      <= rew ? cfg_base_addr : s2_wr_addr;
                r_plan_ok        <= (units >= w_beats_per_unit);
            end
        end
    )

    // Whole-record FIFO cap, combinationally off the REGISTERED raw count
    // (r_fifo_beats) -- short, local path; round-down = X - (X mod 3), mod-3
    // from u_mod3_fifo. Both the trigger and the commit derive from
    // r_fifo_beats so they agree.
    logic [15:0] w_fifo_units;
    assign w_fifo_units = w_use_comp ? r_fifo_beats
                                     : (r_fifo_beats - 16'(w_fifo_rem3));

    // Compressor-style mod-3 instances (combinational); fed by the pipelined
    // s2_beats_planned and the registered r_fifo_beats.
    mod_3_compress u_mod3_geo (
        .d_in    (s2_beats_planned),
        .rem_out (w_geo_rem3)
    );
    mod_3_compress u_mod3_fifo (
        .d_in    (r_fifo_beats),
        .rem_out (w_fifo_rem3)
    );

    // Triggers: watermark / timeout (short combinational paths). Watermark
    // uses the SAME registered count the cap uses (r_fifo_beats) -- a fresh
    // trigger against a registered cap shorted the burst (21/24).
    assign have_one_unit            = (w_fifo_units >= w_beats_per_unit);
    assign flush_trigger_watermark  = (r_fifo_beats >= cfg_flush_watermark);
    assign flush_trigger_timeout    = (r_timeout_cnt >= 32'(FLUSH_TIMEOUT_CYCLES));

    assign do_flush = (flush_trigger_watermark || flush_trigger_timeout) && have_one_unit;

    // AW / W / B drive
    assign fub_m_awid    = '0;
    assign fub_m_awsize  = 3'd3;          // 2^3 = 8 bytes
    assign fub_m_awburst = 2'b01;         // INCR
    assign fub_m_awvalid = (r_wr_state == WR_AW);
    assign fub_m_awaddr  = r_aw_addr;
    assign fub_m_awlen   = r_aw_len;

    assign fub_m_wvalid  = (r_wr_state == WR_W) && write_fifo_rd_valid;
    assign fub_m_wdata   = write_fifo_rd_data;
    assign fub_m_wstrb   = 8'hFF;
    assign fub_m_wlast   = (r_wr_state == WR_W) && (r_w_beats_remaining == 9'd1);

    assign fub_m_bready  = (r_wr_state == WR_B);

    // Pop a beat from the FIFO on each accepted W beat
    assign write_fifo_rd_ready = (r_wr_state == WR_W) && fub_m_wready && write_fifo_rd_valid;

    // FSM
    //
    // A drain cycle is launched from WR_IDLE when do_flush asserts and
    // beats_planned_units >= BEATS_PER_UNIT. The cycle commits to
    // emitting `beats_planned_units` total beats at consecutive
    // 8-byte-stride addresses starting at eff_addr.
    //
    // Each sub-burst inside the drain cycle is bounded by MAX_BURST_BEATS
    // (the per-AW limit imposed by the master leaf). The cycle emits as
    // many AW + N x W + B sub-bursts as needed: AXI4 with
    // MAX_BURST_BEATS=64 typically emits a single large sub-burst per
    // cycle, while AXIL with MAX_BURST_BEATS=1 emits one sub-burst per
    // beat. The address advances per beat regardless.
    //
    // r_unit_remaining tracks how many beats are left in this drain
    // cycle. r_w_beats_remaining tracks how many beats are left in the
    // current sub-burst (for wlast assertion).
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_wr_state          <= WR_IDLE;
            r_wr_addr           <= '0;
            r_aw_addr           <= '0;
            r_aw_len            <= 8'd0;
            r_w_beats_remaining <= 9'd0;
            r_unit_remaining    <= 16'd0;
            r_timeout_cnt       <= 32'd0;
            r_geom_settle       <= 2'd0;
        end else begin
            // Timeout counter: count up while the FIFO has data and we're
            // not currently emitting; clear on W handshake or when empty.
            if (write_fifo_empty) begin
                r_timeout_cnt <= 32'd0;
            end else if (r_wr_state == WR_W && fub_m_wvalid && fub_m_wready) begin
                r_timeout_cnt <= 32'd0;
            end else if (r_timeout_cnt < 32'(FLUSH_TIMEOUT_CYCLES)) begin
                r_timeout_cnt <= r_timeout_cnt + 32'd1;
            end

            // Geometry-pipeline settle: r_wr_addr only moves outside
            // WR_IDLE, so hold the plan-valid flag low until it has been
            // stable for the full pipeline depth.
            if (r_wr_state != WR_IDLE) begin
                r_geom_settle <= 2'd0;
            end else if (r_geom_settle != 2'd3) begin
                r_geom_settle <= r_geom_settle + 2'd1;
            end

            case (r_wr_state)
                WR_IDLE: begin
                    // Consume the pre-computed ADDRESS plan (r_plan_*) and
                    // the whole-record FIFO cap (w_fifo_units, off the
                    // registered raw count) so the burst drains what is
                    // queued. geom_valid guarantees the address plan was
                    // computed from the settled r_wr_addr; r_plan_addr
                    // handles the out-of-window rewind to cfg_base_addr.
                    if (do_flush && geom_valid && r_plan_ok) begin
                        logic [15:0] total_units;   // beats this drain cycle
                        logic [15:0] first_sub_burst;

                        total_units = (r_plan_geo_units < w_fifo_units)
                                    ? r_plan_geo_units : w_fifo_units;
                        first_sub_burst = (total_units < 16'(MAX_BURST_BEATS))
                                        ? total_units
                                        : 16'(MAX_BURST_BEATS);

                        r_wr_addr  <= r_plan_addr;
                        r_aw_addr  <= r_plan_addr;
                        r_aw_len   <= 8'(first_sub_burst - 16'd1);
                        r_w_beats_remaining <= 9'(first_sub_burst);
                        r_unit_remaining    <= total_units;
                        r_wr_state <= WR_AW;
                    end
                end

                WR_AW: begin
                    if (fub_m_awvalid && fub_m_awready) begin
                        r_wr_state <= WR_W;
                    end
                end

                WR_W: begin
                    if (fub_m_wvalid && fub_m_wready) begin
                        // Advance address one beat. r_unit_remaining counts
                        // total beats in this drain cycle; r_w_beats_remaining
                        // counts beats in the current sub-burst (for wlast).
                        r_wr_addr           <= r_wr_addr + ADDR_WIDTH'(BYTES_PER_BEAT);
                        r_w_beats_remaining <= r_w_beats_remaining - 9'd1;
                        r_unit_remaining    <= r_unit_remaining - 16'd1;
                        if (r_w_beats_remaining == 9'd1) begin
                            r_wr_state <= WR_B;
                        end
                    end
                end

                WR_B: begin
                    if (fub_m_bvalid && fub_m_bready) begin
                        if (r_unit_remaining > 16'd0) begin
                            // More beats to emit in this drain cycle --
                            // launch the next sub-burst at r_wr_addr (which
                            // has been advancing per W beat).
                            logic [15:0] next_sub_burst;
                            next_sub_burst = (r_unit_remaining < 16'(MAX_BURST_BEATS))
                                           ? r_unit_remaining
                                           : 16'(MAX_BURST_BEATS);
                            r_aw_addr  <= r_wr_addr;
                            r_aw_len   <= 8'(next_sub_burst - 16'd1);
                            r_w_beats_remaining <= 9'(next_sub_burst);
                            r_wr_state <= WR_AW;
                        end else begin
                            r_wr_state <= WR_IDLE;
                        end
                    end
                end

                default: r_wr_state <= WR_IDLE;
            endcase
        end
    )

    // Lint: bresp/bid not used internally
    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH_M-1:0] _unused_bid   = fub_m_bid;
    logic [1:0]                _unused_bresp = fub_m_bresp;
    /* verilator lint_on UNUSED */

endmodule : monbus_group_core
