// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_group_core_1wr
// Purpose: Ocelus-bus capture core with ONE master-write port.
//
//   The monbus_group_core variant for systems that have no slave-read
//   path for the CPU to walk: everything the group accepts is written to
//   memory, over a single AXI4-shaped master-write FUB, but into two
//   separate address windows:
//
//     error window  [cfg_err_base_addr, cfg_err_limit_addr]
//         packets the per-protocol err_select masks pick. Always raw
//         3-beat records (never compressed), their own beat FIFO, their
//         own watermark / timeout flush, and priority over the trace
//         stream at the write port. irq_out pulses once per WHOLE error
//         record the memory system has acknowledged (all three beats'
//         B returned) and err_rec_count counts them: by the time the host
//         sees a pulse, that record is in the window.
//
//     trace window  [cfg_base_addr, cfg_limit_addr]
//         everything else accepted: raw 3-beat records, or (with
//         USE_COMPRESSION=1 and cfg_compress_en) compressor slots,
//         exactly as monbus_group_core writes them.
//
//   Structure: the filter is monbus_group_core's; each path is a
//   monbus_record_expander (the error path) or expander + optional
//   monbus_compressor (the trace path) into a 64-bit beat FIFO, drained
//   by its own monbus_burst_writer; monbus_wr_mux2 merges the two writers
//   onto the one port in AW order with in-order B routing.
//
//   What is NOT here, relative to monbus_group_core: the AXI4-shaped
//   slave-read FUB (fub_s_*), the 192-bit record FIFO it sliced, and the
//   level irq_out that meant "records waiting to be read". The error
//   FIFO is beat-granular now (FIFO_DEPTH_ERR counts 64-bit beats, three
//   per record).
//
// Beat layout (both windows, raw): beat 0 = {tag=4'h0, source_ts[59:0]},
//   beat 1 = packet[127:64], beat 2 = packet[63:0].
// Beat layout (trace window, compressed): monbus_compressor slot, tag in
//   bits [63:60].
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_group_core_1wr
    import ocelus_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR            = 192,     // beats (64-bit each) -- 3 per record
    parameter int FIFO_DEPTH_WRITE          = 96,      // beats (64-bit each)
    parameter int ADDR_WIDTH                = 32,
    parameter int AXI_ID_WIDTH_M            = 1,       // master-write id (1 in AXIL builds)
    parameter int MAX_BURST_BEATS           = 1,       // master-write max beats/burst
                                                       //   AXIL builds: 1, AXI4 builds: up to 256
    parameter int FLUSH_TIMEOUT_CYCLES      = 1024,    // trace: cycles since last W to force flush
    parameter int ERR_FLUSH_TIMEOUT_CYCLES  = 64,      // error: same, shorter -- errors leave promptly
    parameter int NUM_PROTOCOLS             = 3,       // informational
    parameter int USE_COMPRESSION           = 0,       // trace path: 0 = raw, 1 = compressor present
    parameter int HALF_BEAT_EN              = 0        // 1 = pack two 30-bit slots/beat
                                                       //     (requires USE_COMPRESSION==1)
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,
    // Synchronous CAM clear: empties the compressor template CAM + zeroes its
    // stat counters (no effect when USE_COMPRESSION=0). Pulse when idle.
    input  logic                          cam_clear,

    // ------------------------------------------------------------------
    // Ocelus-bus input (single stream; upstream arbitration if any)
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
    output logic                          irq_out,           // 1-cycle pulse per whole error record landed (B)
    output logic [15:0]                   err_rec_count,     // whole error records landed, free-running
    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [15:0]                   err_fifo_count,    // beats
    output logic [15:0]                   write_fifo_count,  // beats

    // ------------------------------------------------------------------
    // Trace window + flush threshold
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark,     // beats

    // ------------------------------------------------------------------
    // Error window + flush threshold (3 = flush every record as it lands)
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]         cfg_err_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_err_limit_addr,
    input  logic [15:0]                   cfg_err_flush_watermark, // beats

    // Runtime compression enable for the TRACE path only. Meaningful when
    // USE_COMPRESSION==1. MUST be held stable while the trace write path
    // is active (see monbus_group_core). The error path ignores it.
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
    // AXIS (protocol 1) -- also filters CXS (protocol 6), see the case below
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
    // Single AXI4-shaped master-write FUB (driven by core, bridged by wrapper)
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
    output logic                          fub_m_bready
);

    // ==================================================================
    // Local parameters
    // ==================================================================

    localparam int ERR_FIFO_AW   = $clog2(FIFO_DEPTH_ERR);
    localparam int WRITE_FIFO_AW = $clog2(FIFO_DEPTH_WRITE);

    // Runtime compression select (trace path). The compressor hardware
    // exists only when USE_COMPRESSION==1; in raw-only builds w_use_comp
    // is constant 0 and the expander path is always selected.
    logic        w_use_comp;
    assign w_use_comp = (USE_COMPRESSION != 0) && cfg_compress_en;

    // Record size for each writer: the error path is always raw.
    logic [15:0] w_trace_beats_per_unit;
    assign w_trace_beats_per_unit = w_use_comp ? 16'd1 : 16'd3;
    localparam logic [15:0] ERR_BEATS_PER_UNIT = 16'd3;

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

    // Err FIFO (beat-granular, 64-bit)
    logic                            err_exp_in_ready;
    logic                            err_fifo_wr_valid;
    logic                            err_fifo_wr_ready;
    logic [63:0]                     err_fifo_wr_data;
    logic                            err_fifo_rd_valid;
    logic                            err_fifo_rd_ready;
    logic [63:0]                     err_fifo_rd_data;
    logic [ERR_FIFO_AW:0]            err_fifo_beat_count;

    // Write FIFO (beat-granular, 64-bit)
    logic                            write_fifo_wr_valid;
    logic                            write_fifo_wr_ready;
    logic [63:0]                     write_fifo_wr_data;
    logic                            write_fifo_rd_valid;
    logic                            write_fifo_rd_ready;
    logic [63:0]                     write_fifo_rd_data;
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
                // CXS is a stream protocol with exactly the AXIS packet-type
                // set (Error/Timeout/Completion/Credit/Channel/Stream), so it
                // shares the stream filter slot rather than adding eight more
                // mask ports to every group wrapper. Event masks index the
                // low nibble of each protocol's own codes.
                PROTOCOL_AXIS, PROTOCOL_CXS: begin
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
    // Error path: raw 3-beat expander -> beat FIFO (never compressed)
    // ==================================================================

    monbus_record_expander u_err_expander (
        .axi_aclk     (axi_aclk),
        .axi_aresetn  (axi_aresetn),
        .in_valid     (monbus_valid && pkt_to_err_fifo),
        .in_ready     (err_exp_in_ready),
        .in_packet    (monbus_packet),
        .in_source_ts (monbus_timestamp),
        .out_valid    (err_fifo_wr_valid),
        .out_ready    (err_fifo_wr_ready),
        .out_data     (err_fifo_wr_data)
    );

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (64),
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
        .count       (err_fifo_beat_count)
    );

    assign err_fifo_full  = !err_fifo_wr_ready;
    assign err_fifo_count = {{(16-ERR_FIFO_AW-1){1'b0}}, err_fifo_beat_count};

    // ==================================================================
    // Trace path -- raw 3-beat expander and (optionally) the compressor
    // both feed the 64-bit write FIFO; cfg_compress_en (via w_use_comp)
    // selects which one is active at run time. Same arrangement as
    // monbus_group_core.
    // ==================================================================

    // Expander outputs (active when !w_use_comp).
    logic        exp_wr_valid;
    logic [63:0] exp_wr_data;
    logic        exp_term;        // "expander accepted the input this cycle"
    // Compressor outputs (active when w_use_comp; tied 0 when absent).
    logic        comp_wr_valid;
    logic [63:0] comp_wr_data;
    logic        comp_in_ready;

    monbus_record_expander u_trace_expander (
        .axi_aclk     (axi_aclk),
        .axi_aresetn  (axi_aresetn),
        .in_valid     (monbus_valid && pkt_to_write_path && !w_use_comp),
        .in_ready     (exp_term),
        .in_packet    (monbus_packet),
        .in_source_ts (monbus_timestamp),
        .out_valid    (exp_wr_valid),
        .out_ready    (write_fifo_wr_ready),
        .out_data     (exp_wr_data)
    );

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
                       || (pkt_to_err_fifo && err_exp_in_ready)
                       || (pkt_to_write_path && (w_use_comp ? comp_in_ready
                                                            : exp_term));

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

    assign write_fifo_full  = !write_fifo_wr_ready;
    assign write_fifo_count = {{(16-WRITE_FIFO_AW-1){1'b0}}, write_fifo_beat_count};

    // ==================================================================
    // Two burst writers, one per window, merged onto the single port.
    // Port 0 of the mux (priority) is the error writer.
    // ==================================================================

    logic [AXI_ID_WIDTH_M-1:0] err_awid,    trc_awid;
    logic [ADDR_WIDTH-1:0]     err_awaddr,  trc_awaddr;
    logic [7:0]                err_awlen,   trc_awlen;
    logic [2:0]                err_awsize,  trc_awsize;
    logic [1:0]                err_awburst, trc_awburst;
    logic                      err_awvalid, trc_awvalid;
    logic                      err_awready, trc_awready;
    logic [63:0]               err_wdata,   trc_wdata;
    logic [7:0]                err_wstrb,   trc_wstrb;
    logic                      err_wlast,   trc_wlast;
    logic                      err_wvalid,  trc_wvalid;
    logic                      err_wready,  trc_wready;
    logic [AXI_ID_WIDTH_M-1:0] err_bid,     trc_bid;
    logic [1:0]                err_bresp,   trc_bresp;
    logic                      err_bvalid,  trc_bvalid;
    logic                      err_bready,  trc_bready;

    monbus_burst_writer #(
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (AXI_ID_WIDTH_M),
        .MAX_BURST_BEATS      (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES (ERR_FLUSH_TIMEOUT_CYCLES)
    ) u_err_writer (
        .axi_aclk            (axi_aclk),
        .axi_aresetn         (axi_aresetn),
        .fifo_rd_valid       (err_fifo_rd_valid),
        .fifo_rd_ready       (err_fifo_rd_ready),
        .fifo_rd_data        (err_fifo_rd_data),
        .fifo_beat_count     (err_fifo_count),
        .beats_per_unit      (ERR_BEATS_PER_UNIT),
        .cfg_base_addr       (cfg_err_base_addr),
        .cfg_limit_addr      (cfg_err_limit_addr),
        .cfg_flush_watermark (cfg_err_flush_watermark),
        .fub_m_awid          (err_awid),
        .fub_m_awaddr        (err_awaddr),
        .fub_m_awlen         (err_awlen),
        .fub_m_awsize        (err_awsize),
        .fub_m_awburst       (err_awburst),
        .fub_m_awvalid       (err_awvalid),
        .fub_m_awready       (err_awready),
        .fub_m_wdata         (err_wdata),
        .fub_m_wstrb         (err_wstrb),
        .fub_m_wlast         (err_wlast),
        .fub_m_wvalid        (err_wvalid),
        .fub_m_wready        (err_wready),
        .fub_m_bid           (err_bid),
        .fub_m_bresp         (err_bresp),
        .fub_m_bvalid        (err_bvalid),
        .fub_m_bready        (err_bready)
    );

    monbus_burst_writer #(
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (AXI_ID_WIDTH_M),
        .MAX_BURST_BEATS      (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT_CYCLES)
    ) u_trace_writer (
        .axi_aclk            (axi_aclk),
        .axi_aresetn         (axi_aresetn),
        .fifo_rd_valid       (write_fifo_rd_valid),
        .fifo_rd_ready       (write_fifo_rd_ready),
        .fifo_rd_data        (write_fifo_rd_data),
        .fifo_beat_count     (write_fifo_count),
        .beats_per_unit      (w_trace_beats_per_unit),
        .cfg_base_addr       (cfg_base_addr),
        .cfg_limit_addr      (cfg_limit_addr),
        .cfg_flush_watermark (cfg_flush_watermark),
        .fub_m_awid          (trc_awid),
        .fub_m_awaddr        (trc_awaddr),
        .fub_m_awlen         (trc_awlen),
        .fub_m_awsize        (trc_awsize),
        .fub_m_awburst       (trc_awburst),
        .fub_m_awvalid       (trc_awvalid),
        .fub_m_awready       (trc_awready),
        .fub_m_wdata         (trc_wdata),
        .fub_m_wstrb         (trc_wstrb),
        .fub_m_wlast         (trc_wlast),
        .fub_m_wvalid        (trc_wvalid),
        .fub_m_wready        (trc_wready),
        .fub_m_bid           (trc_bid),
        .fub_m_bresp         (trc_bresp),
        .fub_m_bvalid        (trc_bvalid),
        .fub_m_bready        (trc_bready)
    );

    monbus_wr_mux2 #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_ID_WIDTH (AXI_ID_WIDTH_M),
        .ORDER_DEPTH  (8)
    ) u_wr_mux (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .s0_awid     (err_awid),    .s0_awaddr (err_awaddr), .s0_awlen (err_awlen),
        .s0_awsize   (err_awsize),  .s0_awburst(err_awburst),
        .s0_awvalid  (err_awvalid), .s0_awready(err_awready),
        .s0_wdata    (err_wdata),   .s0_wstrb  (err_wstrb),  .s0_wlast (err_wlast),
        .s0_wvalid   (err_wvalid),  .s0_wready (err_wready),
        .s0_bid      (err_bid),     .s0_bresp  (err_bresp),
        .s0_bvalid   (err_bvalid),  .s0_bready (err_bready),
        .s1_awid     (trc_awid),    .s1_awaddr (trc_awaddr), .s1_awlen (trc_awlen),
        .s1_awsize   (trc_awsize),  .s1_awburst(trc_awburst),
        .s1_awvalid  (trc_awvalid), .s1_awready(trc_awready),
        .s1_wdata    (trc_wdata),   .s1_wstrb  (trc_wstrb),  .s1_wlast (trc_wlast),
        .s1_wvalid   (trc_wvalid),  .s1_wready (trc_wready),
        .s1_bid      (trc_bid),     .s1_bresp  (trc_bresp),
        .s1_bvalid   (trc_bvalid),  .s1_bready (trc_bready),
        .m_awid      (fub_m_awid),    .m_awaddr (fub_m_awaddr), .m_awlen (fub_m_awlen),
        .m_awsize    (fub_m_awsize),  .m_awburst(fub_m_awburst),
        .m_awvalid   (fub_m_awvalid), .m_awready(fub_m_awready),
        .m_wdata     (fub_m_wdata),   .m_wstrb  (fub_m_wstrb),  .m_wlast (fub_m_wlast),
        .m_wvalid    (fub_m_wvalid),  .m_wready (fub_m_wready),
        .m_bid       (fub_m_bid),     .m_bresp  (fub_m_bresp),
        .m_bvalid    (fub_m_bvalid),  .m_bready (fub_m_bready)
    );

    // ==================================================================
    // Error records landed. The error writer's sub-bursts do not line up
    // with records (MAX_BURST_BEATS=1 makes a record three sub-bursts; 16
    // can end mid-record), so a B alone says nothing about whole records.
    // Keep the error writer's sub-burst lengths in AW order (the queue the
    // writer keeps internally, re-derived at its port; it caps itself at
    // ERR_OS_CAP outstanding so this one cannot overflow), add each
    // acknowledged sub-burst's beats to a pool on its B, and drain the
    // pool one record (three beats) per cycle: one irq_out pulse and one
    // err_rec_count step per whole record in the window. Counters and
    // qualifiers only; irq_out is registered, so there is no path from
    // fub_m_bvalid to the pin.
    // ==================================================================

    localparam int ERR_OS_CAP = 4;      // monbus_burst_writer WR_OS_CAP

    logic [7:0]  r_err_len_q [ERR_OS_CAP];   // awlen per outstanding error sub-burst
    logic [1:0]  r_err_lq_rd, r_err_lq_wr;
    logic [15:0] r_err_beats_acked;          // acknowledged beats not yet counted as records
    logic        w_err_aw_hs, w_err_b_hs, w_err_rec_done;
    logic [15:0] w_err_b_beats;

    assign w_err_aw_hs    = err_awvalid && err_awready;
    assign w_err_b_hs     = err_bvalid  && err_bready;
    assign w_err_b_beats  = 16'(r_err_len_q[r_err_lq_rd]) + 16'd1;
    assign w_err_rec_done = (r_err_beats_acked >= 16'd3);

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_err_len_q[0]    <= 8'd0;
            r_err_len_q[1]    <= 8'd0;
            r_err_len_q[2]    <= 8'd0;
            r_err_len_q[3]    <= 8'd0;
            r_err_lq_rd       <= 2'd0;
            r_err_lq_wr       <= 2'd0;
            r_err_beats_acked <= 16'd0;
            irq_out           <= 1'b0;
            err_rec_count     <= 16'd0;
        end else begin
            if (w_err_aw_hs) begin
                r_err_len_q[r_err_lq_wr] <= err_awlen;
                r_err_lq_wr              <= r_err_lq_wr + 2'd1;
            end
            if (w_err_b_hs) r_err_lq_rd <= r_err_lq_rd + 2'd1;
            // One combined update: a B may land the same cycle a record drains.
            case ({w_err_b_hs, w_err_rec_done})
                2'b10:   r_err_beats_acked <= r_err_beats_acked + w_err_b_beats;
                2'b01:   r_err_beats_acked <= r_err_beats_acked - 16'd3;
                2'b11:   r_err_beats_acked <= r_err_beats_acked + w_err_b_beats - 16'd3;
                default: ;
            endcase
            irq_out <= w_err_rec_done;
            if (w_err_rec_done) err_rec_count <= err_rec_count + 16'd1;
        end
    )

endmodule : monbus_group_core_1wr
