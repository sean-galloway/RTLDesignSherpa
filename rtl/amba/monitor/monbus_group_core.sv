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
//   management, compression, and the FSM-free burst writer / slicer
//   logic. The wrappers are pure structural adapters.
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
    // Synchronous CAM clear: empties the compressor template CAM + zeroes its
    // stat counters (no effect when USE_COMPRESSION=0). Pulse when idle.
    input  logic                          cam_clear,

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
`ifdef FORMAL
    ,
    // Formal-only probes of the continuous write-burst writer.
    output logic [ADDR_WIDTH-1:0]         f_r_wr_addr,
    output logic [15:0]                   f_r_win_beats,
    output logic [16:0]                   f_r_w_unsent_beats,
    output logic [16:0]                   f_r_aw_cov_beats,
    output logic [15:0]                   f_r_epoch_total,
    output logic [8:0]                    f_r_aw_subs,
    output logic [8:0]                    f_r_b_subs,
    output logic [2:0]                    f_r_os_count,
    output logic [2:0]                    f_r_ws_count,
    output logic [9:0]                    f_r_w_rem_in_sub,
    output logic [15:0]                   f_w_aw_beats,
    output logic                          f_w_aw_issue
`endif
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
    // math_mod_3_compress instances (u_mod3_win / u_mod3_4kb / u_mod3_fifo,
    // below): the div15 carry-save-compressor idiom applied to the operation
    // we actually need -- a base-4 digit sum reduced by 3:2 compressors. A
    // few LUTs, not a wide reciprocal-multiply tree by the compressor CAM.

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
    // AR is accepted whenever no burst is in flight (fub_s_arready =
    // !r_rd_in_burst) -- NOT gated on slice position or FIFO occupancy.
    // An AR on an empty FIFO is accepted and rvalid simply stalls until a
    // record arrives; an AR after a misaligned burst is accepted with the
    // slicer parked mid-record. rvalid drops mid-burst if the FIFO
    // underruns (the slicer holds its slice until a new record arrives,
    // then resumes). rlast asserts on the (arlen+1)-th beat.
    // (This comment used to claim slice-0-plus-buffered-record gating; the
    // docs were written from it, so both were wrong -- qc round_24.)
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
            .clear               (cam_clear),

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
    // Master-write burst writer -- continuous, FSM-free (amba BUG-039,
    // 2026-10-09 redesign; replaces the WR_IDLE/WR_RUN drain-cycle FSM,
    // which quiesced the whole pipeline at every flush boundary).
    //
    // There is no drain cycle and no writer state machine.  An AW
    // handshake fires whenever all of these hold:
    //     (a) a flush trigger: r_fifo_beats >= cfg_flush_watermark OR
    //         FLUSH_TIMEOUT_CYCLES since the last W handshake, and the
    //         FIFO holds at least one whole record;
    //     (b) at least one whole record is in the FIFO that no previous
    //         AW owns (AW cap = record-rounded FIFO beats minus the
    //         committed-not-W-sent prefix counter);
    //     (c) an outstanding slot is free (r_os_count < WR_OS_CAP) and the
    //         window geometry allows a whole record
    //         (min(window budget, beats-to-4KB, FIFO avail, MAX_BURST)).
    // Batches form naturally and run back-to-back: when a trigger is
    // active the AWs keep issuing until nothing uncommitted remains, and
    // when it deasserts mid-stream the W/B streams simply drain in flight
    // -- there is nothing to re-arm and no geometry re-settle bubble.
    //
    // Window geometry is a saturating down-counter, not a pipeline: the
    // window is a contiguous [base, limit] range written strictly
    // sequentially, so "beats left from the running pointer" decrements
    // by each AW's beat count and reloads full on config adoption,
    // rewind, or base-stub step-over.  The 33-bit (limit + 1 - base)
    // subtract that was the 100 MHz critical path (amba ISSUE-001) now
    // feeds a flop once per config change and never sits on the per-AW
    // path; the only per-AW geometry left is the 13-bit beats-to-4KB
    // from r_wr_addr[11:0].  The watermark/timeout knobs keep their
    // batching-floor semantics exactly -- they only gate issue.
    //
    // Sub-burst lengths (awlen / wlast) ride in two small circular queues
    // pushed at every AW handshake; AXI's per-ID in-order B guarantee
    // makes the credit accounting exact.
    // ==================================================================

    // Max outstanding writes the issue logic allows.  The leaf skids are
    // 2 deep, but the B-return pipeline (leaf B skid + the slave's B
    // register) adds ~2 more cycles of transit; 4 covers it without letting
    // AW run far enough ahead to stress slaves that only tolerate a couple
    // of outstanding single-beat writes.
    localparam int WR_OS_CAP = 4;

    logic [ADDR_WIDTH-1:0]       r_wr_addr;           // running write pointer
    logic [15:0]                 r_win_beats;         // beats remaining in the window from r_wr_addr
    logic [16:0]                 r_w_unsent_beats;    // AW-committed beats not yet W-sent (FIFO prefix)
    logic [16:0]                 r_aw_cov_beats;      // beats covered by AWs in the current epoch
    logic [15:0]                 r_epoch_total;       // frozen epoch budget (loaded at epoch start)
    logic                        r_cfg_pend_load;     // sticky: config adoption waiting for an epoch boundary
    logic [8:0]                  r_aw_subs;           // AW (sub-burst) handshakes issued (stats)
    logic [8:0]                  r_b_subs;            // B handshakes returned (credit)
    logic [9:0]                  r_w_rem_in_sub;      // beats left in W-side current sub-burst (0 = none loaded)
    logic [8:0]                  r_os_len [0:WR_OS_CAP-1]; // B-side sub-burst lengths (beats-1), AW order
    logic [1:0]                  r_os_rd, r_os_wr;
    logic [2:0]                  r_os_count;
    logic [8:0]                  r_ws_len [0:WR_OS_CAP-1]; // W-side sub-burst lengths (beats-1), AW order
    logic [1:0]                  r_ws_rd, r_ws_wr;
    logic [2:0]                  r_ws_count;
    logic [31:0]                 r_timeout_cnt;
    logic [15:0]                 r_fifo_beats;        // registered raw FIFO beat count

    // Locally-registered copies of the quasi-static window config.  They
    // feed the once-per-change budget load and the registered stub/rewind
    // compares; registering them here sources those loads from adjacent
    // flops instead of the far-placed config CSRs (amba ISSUE-001), and
    // the max_fanout cap forces driver replication.  Config is static
    // during operation; a change reloads the budget, so no AW is planned
    // against a half-adopted window.
    (* max_fanout = 24 *) logic [ADDR_WIDTH-1:0] r_cfg_base_addr;
    (* max_fanout = 24 *) logic [ADDR_WIDTH-1:0] r_cfg_limit_addr;
    // limit + 1, 33 bits, registered with the config: the budget divide
    // is (limit + 1 - base) >> 3 for every limit - base, including
    // 0xFFFF_FFFF (which is why the +1 is taken on the quasi-static side,
    // in 33 bits).
    logic [ADDR_WIDTH:0]                          r_cfg_limit_p1;
    // Delayed copy of the registered config.  The difference detects an
    // adopted change exactly once and loads the window budget from the
    // settled registered values; the raw cfg vs r_cfg compare is the
    // 1-cycle-earlier "change in flight" detect and holds AW issue.
    logic [ADDR_WIDTH-1:0]                        r_cfg_base_d1;
    logic [ADDR_WIDTH-1:0]                        r_cfg_limit_d1;

    // Window-budget and AW-cap math (all inputs registered or shallow).
    logic [15:0]                 beats_in_fifo;
    logic [ADDR_WIDTH:0]         w_full_budget_raw;
    logic [15:0]                 w_full_budget;
    logic                        w_cfg_raw_chg;
    logic                        w_cfg_adopted_chg;
    logic [15:0]                 w_4kb_beats;        // beats to the next 4KB boundary
    logic [15:0]                 w_win_units;        // record-rounded window room
    logic [15:0]                 w_4kb_units;        // record-rounded 4KB room
    logic [16:0]                 w_fifo_avail_beats; // uncommitted FIFO beats
    logic [16:0]                 w_fifo_epoch_beats; // avail + covered: coverable by this epoch
    logic [15:0]                 w_fifo_epoch_units; // record-rounded epoch budget (FIFO side)
    logic [15:0]                 w_epoch_live;       // min caps, valid at epoch start (covered == 0)
    logic                        w_epoch_inflight;   // covered != 0: epoch total is frozen
    logic [16:0]                 w_epoch_room;       // beats this epoch may still cover
    logic [15:0]                 w_aw_beats;         // beats the next AW covers
    logic [16:0]                 w_aw_beats_p1;
    logic                        w_epoch_load_en;    // freeze the epoch total this cycle
    logic                        w_epoch_roll;       // epoch complete: restart at the boundary
    logic                        w_geo_blocked;      // no whole record fits from r_wr_addr
    logic                        w_stub_at_base;     // ...but base sits in a too-short stub
    logic [3:0]                  w_win_rem3;
    logic [3:0]                  w_4kb_rem3;
    logic [3:0]                  w_epoch_rem3;
    // flush triggers
    logic                        flush_trigger_watermark;
    logic                        flush_trigger_timeout;
    logic                        have_one_unit;
    logic                        do_flush;

    assign beats_in_fifo = {{(16-WRITE_FIFO_AW-1){1'b0}}, write_fifo_beat_count};

    // Full window budget off the REGISTERED config: (limit + 1 - base) >> 3,
    // saturated to 16 bits (the 33-bit subtract now loads a counter once
    // per config change / rewind and never sits on the per-AW path).
    assign w_full_budget_raw = (r_cfg_limit_p1 - {1'b0, r_cfg_base_addr}) >> 3;
    assign w_full_budget     = (|w_full_budget_raw[ADDR_WIDTH:16])
                             ? 16'hFFFF : w_full_budget_raw[15:0];

    assign w_cfg_raw_chg     = (cfg_base_addr  != r_cfg_base_addr)
                            || (cfg_limit_addr != r_cfg_limit_addr);
    assign w_cfg_adopted_chg = (r_cfg_base_addr  != r_cfg_base_d1)
                            || (r_cfg_limit_addr != r_cfg_limit_d1);

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_cfg_base_addr  <= '0;
            r_cfg_limit_addr <= '0;
            r_cfg_limit_p1   <= '0;
            r_cfg_base_d1    <= '0;
            r_cfg_limit_d1   <= '0;
        end else begin
            r_cfg_base_addr  <= cfg_base_addr;
            r_cfg_limit_addr <= cfg_limit_addr;
            r_cfg_limit_p1   <= {1'b0, cfg_limit_addr} + 1'b1;
            r_cfg_base_d1    <= r_cfg_base_addr;
            r_cfg_limit_d1   <= r_cfg_limit_addr;
        end
    )

    // Beats to the next 4KB boundary from the running pointer.  13-bit off
    // the registered r_wr_addr[11:0] -- the only per-AW geometry left.
    assign w_4kb_beats = 16'((13'h1000 - {1'b0, r_wr_addr[11:0]}) >> 3);

    // Strobes of the continuous writer (declared before the epoch logic
    // that references them).
    logic w_aw_issue;
    logic w_w_issue;
    logic w_b_issue;
    logic w_ws_pop;           // W-side queue pop this cycle

    // Record-rounded room on each cap.  floor-to-whole-record is monotonic,
    // so min(then-round) == round(each-then-min): each side rounds
    // independently and the min stays exact.
    assign w_win_units  = w_use_comp ? r_win_beats
                        : (r_win_beats - 16'(w_win_rem3));
    assign w_4kb_units  = w_use_comp ? w_4kb_beats
                        : (w_4kb_beats - 16'(w_4kb_rem3));
    // Beats the FIFO holds that no AW owns yet.  Unsent committed beats are
    // a prefix of the FIFO -- W pops in AW order, and a record is only
    // committable once its beats have all arrived -- so this never
    // underflows.  r_fifo_beats lags the live count by exactly one flop,
    // and the W that drains a committed beat decrements r_w_unsent_beats
    // the same cycle, so the cap stays exact.
    assign w_fifo_avail_beats = 17'(r_fifo_beats) - r_w_unsent_beats;

    // Epoch budget, FIFO side: beats this covering epoch may still commit.
    // avail + covered = beats arrived minus beats covered by previous
    // epochs, so rounding it down to a whole-record multiple never covers
    // an already-covered or not-yet-arrived beat.  The epoch TOTAL is
    // frozen at epoch start (r_epoch_total, loaded the cycle the first AW
    // of an epoch issues): freezing pins the 4KB cap to the page the
    // epoch started in, so a pointer that advances past a page boundary
    // mid-epoch cannot shrink the live cap below the covered count (the
    // unsigned room would underflow), and the epoch always completes at
    // exactly the frozen total -- the pointer lands on a record boundary.
    // Mid-epoch W handshakes leave avail + covered constant, so draining
    // the committed beats never starves the epoch that owns them; new
    // arrivals during the epoch are deferred to the next one (they
    // cannot join: covered > 0 freezes the total).
    assign w_fifo_epoch_beats  = w_fifo_avail_beats + r_aw_cov_beats;
    assign w_fifo_epoch_units  = w_use_comp ? 16'(w_fifo_epoch_beats[15:0])
                            : (16'(w_fifo_epoch_beats[15:0]) - 16'(w_epoch_rem3));

    // Live epoch cap: min of the three record-rounded caps, valid at
    // epoch start (covered == 0).  Individual sub-bursts (awlen) may
    // split records; the alignment invariant lives at the epoch total.
    // MAX_BURST_BEATS may be smaller than a record (AXIL leaves), which
    // only means more sub-bursts per epoch.  Only the low 8 bits go to
    // AWLEN (AXI4 awlen+1 <= 256 beats).
    assign w_epoch_live = (w_win_units < w_4kb_units)
                        ? ((w_win_units  < w_fifo_epoch_units) ? w_win_units  : w_fifo_epoch_units)
                        : ((w_4kb_units  < w_fifo_epoch_units) ? w_4kb_units  : w_fifo_epoch_units);
    assign w_epoch_inflight = (r_aw_cov_beats != 17'd0);
    assign w_epoch_room = w_epoch_inflight ? (17'(r_epoch_total) - r_aw_cov_beats)
                                           : 17'(w_epoch_live);
    assign w_epoch_load_en  = !w_epoch_inflight && w_aw_issue;
    assign w_epoch_roll     = w_epoch_inflight && (w_epoch_room == 17'd0)
                           && (r_w_unsent_beats == 17'd0) && (r_ws_count == 3'd0);
    assign w_aw_beats   = (w_epoch_room == 17'd0) ? 16'd0
                        : (w_epoch_room < 17'(MAX_BURST_BEATS))
                        ? 16'(w_epoch_room) : 16'(MAX_BURST_BEATS);
    assign w_aw_beats_p1 = 17'(w_aw_beats);

    // No whole record fits from the current position (window budget
    // exhausted, or a 4KB stub shorter than one record ahead): the
    // registered fixup in the counter block re-establishes the pointer
    // (rewind home, or step over a stub at base).  Evaluated only when no
    // epoch is in flight: the frozen total already caps the in-flight
    // pointer to the page/span the epoch started in, and re-establishing
    // the pointer mid-epoch would split a record across non-adjacent
    // addresses.
    assign w_geo_blocked = ((w_win_units < w_beats_per_unit)
                        ||  (w_4kb_units < w_beats_per_unit))
                        && !w_epoch_inflight;
    // Exception: the window itself still has room and base is the stub --
    // step over the stub instead of rewinding (a full 4KB region always
    // fits at least one record).
    assign w_stub_at_base = w_geo_blocked
                         && (r_wr_addr == r_cfg_base_addr)
                         && (w_win_units >= w_beats_per_unit);

    // Compressor-style mod-3 instances (combinational); fed by the
    // registered budget / FIFO counters and the shallow 4KB math.
    math_mod_3_compress u_mod3_win (
        .d_in    (r_win_beats),
        .rem_out (w_win_rem3)
    );
    math_mod_3_compress u_mod3_4kb (
        .d_in    (w_4kb_beats),
        .rem_out (w_4kb_rem3)
    );
    math_mod_3_compress u_mod3_fifo (
        .d_in    (16'(w_fifo_epoch_beats[15:0])),
        .rem_out (w_epoch_rem3)
    );

    // Triggers: watermark / timeout (short combinational paths).  Watermark
    // and the >=1-record guard read the SAME registered count (r_fifo_beats)
    // -- the guard is exact without record rounding, because
    // floor(x/u)*u >= u iff x >= u.
    assign have_one_unit            = (r_fifo_beats >= w_beats_per_unit);
    assign flush_trigger_watermark  = (r_fifo_beats >= cfg_flush_watermark);
    assign flush_trigger_timeout    = (r_timeout_cnt >= 32'(FLUSH_TIMEOUT_CYCLES));

    assign do_flush = (flush_trigger_watermark || flush_trigger_timeout) && have_one_unit;

    // AW fires whenever a flush trigger, a free outstanding slot, epoch
    // room, and the window geometry align; W streams the write FIFO in
    // the AW (sub-burst) order AXI4 demands; B is a pure credit return
    // consumed while any write is outstanding.  The epoch room -- not a
    // per-AW record count -- gates issue, so MAX_BURST_BEATS < record
    // size (AXIL leaves) just means more sub-bursts per epoch.  AW issue
    // holds while a config change is in flight and on the cycle a
    // (possibly deferred) adoption lands, so an address can never be
    // planned against a half-adopted window and an adopted change never
    // clobbers an in-flight AW's pointer advance.
    // Record-alignment gating (do_flush / have_one_unit) applies only to
    // EPOCH START: a fresh epoch must not plan beats that cannot form whole
    // records.  Once an epoch is in flight its beats are already committed
    // -- the frozen total was capped by the FIFO count at start, so the
    // data for every in-epoch sub-burst is provably present -- and gating
    // in-epoch AWs on the live FIFO count deadlocks the tail: the FIFO
    // drops below one record mid-epoch and the remaining covered beats
    // can never issue, leaving the epoch unable to roll (group_chain
    // drains-hang, 2026-10).  In-epoch issue needs only epoch room and a
    // free outstanding slot.
    assign fub_m_awvalid   = (w_epoch_inflight || do_flush)
                          && (w_aw_beats != 16'd0)
                          && (r_os_count < 3'(WR_OS_CAP))
                          && !(w_cfg_raw_chg && !w_epoch_inflight)
                          && !(w_cfg_adopted_chg && !w_epoch_inflight)
                          && !(r_cfg_pend_load && !w_epoch_inflight);
    assign fub_m_awid      = '0;
    assign fub_m_awsize    = 3'd3;          // 2^3 = 8 bytes
    assign fub_m_awburst   = 2'b01;         // INCR
    assign fub_m_awaddr    = r_wr_addr;
    assign fub_m_awlen     = 8'(w_aw_beats - 16'd1);
    assign w_aw_issue      = fub_m_awvalid && fub_m_awready;

    assign fub_m_wvalid    = (r_w_rem_in_sub != 10'd0) && write_fifo_rd_valid;
    assign fub_m_wdata     = write_fifo_rd_data;
    assign fub_m_wstrb     = 8'hFF;
    assign fub_m_wlast     = (r_w_rem_in_sub == 10'd1);
    assign write_fifo_rd_ready = fub_m_wvalid && fub_m_wready;
    assign w_w_issue       = write_fifo_rd_ready;

    assign fub_m_bready    = (r_os_count != 3'd0);
    assign w_b_issue       = fub_m_bvalid && fub_m_bready;

    // W-side queue pop: on the last beat of the loaded sub-burst (handover)
    // or on a load while no sub-burst is loaded.
    always_comb begin
        if (w_w_issue)
            w_ws_pop = (r_w_rem_in_sub == 10'd1) && (r_ws_count != 3'd0);
        else
            w_ws_pop = (r_w_rem_in_sub == 10'd0) && (r_ws_count != 3'd0);
    end

    // Counters -- the writer is FSM-free: every behavior above is a
    // function of the registered counters below plus the combinational
    // gates of the section header.  Running-pointer discipline, at most
    // one pointer event per cycle, priority:
    //
    //   adopted config : pointer <- base, budget <- full window -- at an
    //                    epoch boundary; an adoption that arrives mid-epoch
    //                    is sticky-deferred (r_cfg_pend_load) so an
    //                    in-flight epoch always completes on the window it
    //                    started in (re-windowing mid-epoch would split a
    //                    record across non-adjacent addresses)
    //   stub at base   : pointer <- next 4KB boundary, budget -= stub
    //                    beats (the stub bytes are inside the window and
    //                    are given up)
    //   AW handshake   : pointer += awlen+1 beats, budget -= awlen+1; the
    //                    epoch total freezes on the first AW of an epoch
    //   geo blocked    : pointer <- base, budget <- full window (window
    //                    end, or a mid-window stub: snap home and continue
    //                    from base, the old writer's ring behavior;
    //                    ping-pongs to a stall with write_fifo_full when
    //                    the window cannot hold one record, the documented
    //                    misconfiguration)
    //
    // Fixups are evaluated every cycle (not just under do_flush): they
    // only move these registers, so an eager rewind between epochs costs
    // nothing and removes the old WR_IDLE settle bubble entirely.
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_wr_addr           <= '0;
            r_win_beats         <= 16'd0;
            r_w_unsent_beats    <= 17'd0;
            r_aw_cov_beats      <= 17'd0;
            r_epoch_total       <= 16'd0;
            r_cfg_pend_load     <= 1'b0;
            r_aw_subs           <= 9'd0;
            r_b_subs            <= 9'd0;
            r_w_rem_in_sub      <= 10'd0;
            r_os_len[0]         <= 9'd0;
            r_os_len[1]         <= 9'd0;
            r_os_len[2]         <= 9'd0;
            r_os_len[3]         <= 9'd0;
            r_os_rd             <= 2'd0;
            r_os_wr             <= 2'd0;
            r_os_count          <= 3'd0;
            r_ws_len[0]         <= 9'd0;
            r_ws_len[1]         <= 9'd0;
            r_ws_len[2]         <= 9'd0;
            r_ws_len[3]         <= 9'd0;
            r_ws_rd             <= 2'd0;
            r_ws_wr             <= 2'd0;
            r_ws_count          <= 3'd0;
            r_timeout_cnt       <= 32'd0;
            r_fifo_beats        <= 16'd0;
        end else begin
            // Registered raw FIFO beat count (the trigger and the AW cap
            // both read it; see the header note on the one-flop lag).
            r_fifo_beats <= beats_in_fifo;

            // Timeout counter: cycles since the last accepted W handshake
            // while the FIFO holds data (feeds flush_trigger_timeout).
            if (write_fifo_empty) begin
                r_timeout_cnt <= 32'd0;
            end else if (w_w_issue) begin
                r_timeout_cnt <= 32'd0;
            end else if (r_timeout_cnt < 32'(FLUSH_TIMEOUT_CYCLES)) begin
                r_timeout_cnt <= r_timeout_cnt + 32'd1;
            end

            // Running pointer / window budget / epoch state (one pointer
            // event per cycle; every pointer re-establishment restarts the
            // covering epoch at a record boundary).
            if ((r_cfg_pend_load || w_cfg_adopted_chg) && !w_epoch_inflight) begin
                // Config adoption lands: either a deferred one (sticky
                // flag, set when the change arrived mid-epoch) or the
                // 1-cycle adopted-change pulse, both only at an epoch
                // boundary.  r_cfg_* always hold the latest config, so a
                // deferred adoption picks up the newest window.
                r_wr_addr           <= r_cfg_base_addr;
                r_win_beats         <= w_full_budget;
                r_aw_cov_beats      <= 17'd0;
                r_epoch_total       <= 16'd0;
                r_cfg_pend_load     <= 1'b0;
            end else begin
                if (w_cfg_adopted_chg) r_cfg_pend_load <= 1'b1;   // defer to the epoch boundary
                if (w_stub_at_base) begin
                    r_wr_addr      <= {r_cfg_base_addr[ADDR_WIDTH-1:12] + 1'b1,
                                       12'd0};
                    r_win_beats    <= (r_win_beats > w_4kb_beats)
                                    ? (r_win_beats - w_4kb_beats) : 16'd0;
                    r_aw_cov_beats <= 17'd0;
                    r_epoch_total  <= 16'd0;
                end else if (w_aw_issue) begin
                    r_wr_addr      <= r_wr_addr
                                    + ADDR_WIDTH'(w_aw_beats_p1 * 17'(BYTES_PER_BEAT));
                    r_win_beats    <= r_win_beats - w_aw_beats;
                    r_aw_cov_beats <= r_aw_cov_beats + w_aw_beats_p1;
                end else if (w_geo_blocked) begin
                    r_wr_addr      <= r_cfg_base_addr;
                    r_win_beats    <= w_full_budget;
                    r_aw_cov_beats <= 17'd0;
                    r_epoch_total  <= 16'd0;
                end
            end

            // Freeze the epoch total on the first AW of an epoch
            // (w_epoch_load_en); it holds until the epoch completes.
            if (w_epoch_load_en) r_epoch_total <= w_epoch_live;

            // Epoch rollover: the frozen total is fully covered and every
            // committed beat has left the W stream (unsent == 0 and the
            // W-side length queue is drained), so the pointer sits on a
            // record boundary -- restart the epoch so the next live load
            // can issue.  B credits may still be in flight (os_count > 0);
            // AXI in-order B makes that safe and the next epoch's AWs may
            // issue while they return (os slot cap permitting), so the
            // roll costs no bubble: the room is already zero the cycle it
            // fires, and the next AW issues the cycle covered clears.
            if (w_epoch_roll) begin
                r_aw_cov_beats <= 17'd0;
                r_epoch_total  <= 16'd0;
            end

            // AW-committed-not-W-sent beats (a prefix of the FIFO).
            case ({w_aw_issue, w_w_issue})
                2'b10:   r_w_unsent_beats <= r_w_unsent_beats + w_aw_beats_p1;
                2'b01:   r_w_unsent_beats <= r_w_unsent_beats - 17'd1;
                // Both: a beat left the FIFO AND a new sub-burst committed.
                // Unlike the entry-count queues below (push+pop = net 0),
                // this is a BEAT counter, so the two events do not cancel:
                // net +aw_beats-1.  Recording nothing here under-counts the
                // committed prefix and lets an epoch over-plan the FIFO.
                2'b11:   r_w_unsent_beats <= r_w_unsent_beats + w_aw_beats_p1 - 17'd1;
                default: ;
            endcase

            // -- AW stream bookkeeping: push each sub-burst's length into
            //    both bookkeeping queues.
            if (w_aw_issue) begin
                r_aw_subs         <= r_aw_subs + 9'd1;
                r_os_len[r_os_wr] <= 9'(w_aw_beats - 16'd1);
                r_os_wr           <= r_os_wr + 2'd1;
                r_ws_len[r_ws_wr] <= 9'(w_aw_beats - 16'd1);
                r_ws_wr           <= r_ws_wr + 2'd1;
            end

            // -- B stream: credit return, in AW order (AXI per-ID
            //    in-order guarantee)
            if (w_b_issue) begin
                r_b_subs <= r_b_subs + 9'd1;
                r_os_rd  <= r_os_rd + 2'd1;
            end

            // -- W stream: pop the FIFO in sub-burst order.  Load the
            //    next sub-burst from the W-side queue either one beat
            //    ahead (seamless handover on the last beat of the
            //    current sub-burst) or whenever no sub-burst is loaded
            //    and a length is queued.
            if (w_w_issue) begin
                if (r_w_rem_in_sub == 10'd1) begin
                    r_w_rem_in_sub <= w_ws_pop
                                    ? (10'(r_ws_len[r_ws_rd]) + 10'd1)
                                    : 10'd0;
                end else begin
                    r_w_rem_in_sub <= r_w_rem_in_sub - 10'd1;
                end
            end else if (w_ws_pop) begin
                r_w_rem_in_sub <= 10'(r_ws_len[r_ws_rd]) + 10'd1;
            end
            if (w_ws_pop) begin
                r_ws_rd <= r_ws_rd + 2'd1;
            end

            // -- queue occupancy: one combined update per queue so
            //    simultaneous push/pop cannot clobber (NBA last-win).
            case ({w_aw_issue, w_b_issue})
                2'b10:   r_os_count <= r_os_count + 3'd1;
                2'b01:   r_os_count <= r_os_count - 3'd1;
                default: ;
            endcase
            case ({w_aw_issue, w_ws_pop})
                2'b10:   r_ws_count <= r_ws_count + 3'd1;
                2'b01:   r_ws_count <= r_ws_count - 3'd1;
                default: ;
            endcase
        end
    )

`ifdef FORMAL
    // Formal-only probes: expose the continuous writer state for harness-side
    // checks (hierarchical references are not supported by the sv2v/Yosys flow).
    assign f_r_wr_addr        = r_wr_addr;
    assign f_r_win_beats      = r_win_beats;
    assign f_r_w_unsent_beats = r_w_unsent_beats;
    assign f_r_aw_cov_beats   = r_aw_cov_beats;
    assign f_r_epoch_total    = r_epoch_total;
    assign f_r_aw_subs        = r_aw_subs;
    assign f_r_b_subs         = r_b_subs;
    assign f_r_os_count       = r_os_count;
    assign f_r_ws_count       = r_ws_count;
    assign f_r_w_rem_in_sub   = r_w_rem_in_sub;
    assign f_w_aw_beats       = w_aw_beats;
    assign f_w_aw_issue       = w_aw_issue;
`endif

    // Lint: bresp/bid not used internally
    /* verilator lint_off UNUSED */
    logic [AXI_ID_WIDTH_M-1:0] _unused_bid   = fub_m_bid;
    logic [1:0]                _unused_bresp = fub_m_bresp;
    /* verilator lint_on UNUSED */

endmodule : monbus_group_core
