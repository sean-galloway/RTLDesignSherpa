// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_compressor
// Purpose: Hardware encoder for the bulk-trace monbus compression
//          format locked in commit 5bbb83d1. Sits in front of the
//          master writer inside the monbus_group family when a wrapper
//          opts in via USE_COMPRESSION.
//
// Documentation:
//   projects/NexysA7/stream_characterization/reports/compression_dataset/
//     README_COMPRESSION_DATASET.md  -- format spec, dataset, acceptance test
//   bin/TBClasses/monbus/monbus_compressor.py  -- bit-exact Python golden
//
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-06-07
//
// ============================================================================
// Module: monbus_compressor
// ============================================================================
//
// What this is
// ------------
// Streams (monitor_packet_t, monbus_timestamp_t) records in on one
// valid/ready handshake and emits 64-bit AXIL slots on another. The
// encoded slot stream is bit-exact to what the Python `Encoder` class
// in bin/TBClasses/monbus/monbus_compressor.py produces from the same
// record sequence -- that's the acceptance criterion for this module.
//
// Format (locked spec, see README_COMPRESSION_DATASET.md §2)
// ----------------------------------------------------------
// All slots are 64 bits, with a 4-bit tag in the top:
//
//   tag = 0x0  RAW   (3-beat escape: ts beat, pkt_hi, pkt_lo)
//   tag = 0x1  T1-A  (template hit, small payload, 1 beat)
//   tag = 0x2  T1-B  (template hit, big delta_ts, 1 beat)
//   tag = 0x3  T1-C  (template hit, event_data delta, 1 beat)
//
// Internal state
// --------------
//   r_last_ts (60 bits)  -- timestamp of last record encoded
//   monbus_cam            -- 32-entry LRU CAM (sub-instance)
//   FSM                   -- 3 states: IDLE / RAW1 / RAW2
//
// Pipeline (2 stages)
// -------------------
// Stage 1 (lookup/commit): key build -> CAM lookup -> CAM commit + last_ts
//          update. The CAM still does lookup+commit in a single cycle, so
//          its update SEQUENCE (and the emitted slot stream) is bit-exact
//          to the original single-cycle module.
// Stage 2 (encode/emit): delta/fits/format-select -> slot pack -> output,
//          plus RAW (tier-0) beat expansion.
//
// Throughput is unchanged from the single-cycle design:
//   Tier-1 records: 1 record/cycle (1 slot out).
//   Tier-0 records: 1 record / 3 cycles (3 slots out).
// The encode is one cycle of added latency only -- bandwidth is preserved.
//
// Rationale: the fits/fmt/pack tail (a 65-bit signed subtract plus 60/64-bit
// magnitude compares) was the 100 MHz critical path when fused with the CAM
// lookup. Splitting it into stage 2 shortens both halves. There is no CAM
// read-after-write hazard because the commit (action = hit ? TOUCH :
// INSTALL) depends only on the stage-1 lookup, not on the stage-2 format.
//
// Statistics
// ----------
// Per-tier hit counters (tier1_a / tier1_b / tier1_c / tier0_escape)
// plus per-escape-reason counters are exposed for the host-side
// observability path.
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_compressor
    import monitor_common_pkg::*;
(
    input  logic                    clk,
    input  logic                    rst_n,

    // === Input: (packet, source_ts) records ===
    input  logic                    in_valid,
    output logic                    in_ready,
    input  monitor_packet_t         in_packet,
    input  monbus_timestamp_t       in_source_ts,

    // === Output: 64-bit AXIL slots ===
    output logic                    out_valid,
    input  logic                    out_ready,
    output logic [63:0]             out_slot,

    // === Statistics CSR outputs (combinational on the registers) ===
    output logic [31:0]             stat_tier1_a,
    output logic [31:0]             stat_tier1_b,
    output logic [31:0]             stat_tier1_c,
    output logic [31:0]             stat_tier0,
    output logic [31:0]             stat_cam_miss,
    output logic [31:0]             stat_delta_ts_ovf,
    output logic [31:0]             stat_event_data_ovf,
    output logic [31:0]             stat_ed_delta_ovf
);

    // ------------------------------------------------------------------------
    // Format constants (mirror bin/TBClasses/monbus/monbus_compressor.py).
    // ------------------------------------------------------------------------
    localparam logic [3:0] TAG_RAW       = 4'h0;
    localparam logic [3:0] TAG_FORMAT_A  = 4'h1;
    localparam logic [3:0] TAG_FORMAT_B  = 4'h2;
    localparam logic [3:0] TAG_FORMAT_C  = 4'h3;

    localparam int TS_BITS              = 60;
    localparam int DELTA_TS_A_BITS      = 15;   // ~328 us @ 100 MHz
    localparam int DELTA_TS_B_BITS      = 23;   // ~84 ms @ 100 MHz
    localparam int DELTA_TS_C_BITS      = 15;
    localparam int EVENT_DATA_A_BITS    = 40;
    localparam int EVENT_DATA_B_BITS    = 32;
    localparam int EVENT_DATA_C_DELTA   = 40;   // signed
    localparam int TMPL_IDX_BITS        = 5;    // 32-entry CAM
    localparam int TMPL_IDX_SHIFT       = 64 - 4 - TMPL_IDX_BITS;  // = 55
    localparam int CAM_DEPTH            = 32;
    localparam int KEY_WIDTH            = 49;   // 4+4+8+9+16+8

    // ------------------------------------------------------------------------
    // Key extraction from the 128-bit packet (must match
    // _key_from_packet in monbus_compressor.py).
    // ------------------------------------------------------------------------
    logic [3:0]    in_packet_type;
    logic [3:0]    in_protocol;
    logic [7:0]    in_event_code;
    logic [8:0]    in_channel_id;
    logic [15:0]   in_agent_id;
    logic [7:0]    in_unit_id;
    logic [63:0]   in_event_data;
    logic [KEY_WIDTH-1:0] in_key;

    assign in_packet_type = in_packet[127:124];
    assign in_protocol    = in_packet[108:105];
    assign in_event_code  = in_packet[104:97];
    assign in_channel_id  = in_packet[96:88];
    assign in_agent_id    = in_packet[87:72];
    assign in_unit_id     = in_packet[71:64];
    assign in_event_data  = in_packet[63:0];
    assign in_key = {in_packet_type, in_protocol, in_event_code,
                     in_channel_id, in_agent_id, in_unit_id};

    // ------------------------------------------------------------------------
    // Last timestamp register + delta computation.
    // ------------------------------------------------------------------------
    logic [TS_BITS-1:0] r_last_ts;
    logic [TS_BITS-1:0] in_src_ts60;
    logic [TS_BITS-1:0] delta_ts;
    assign in_src_ts60 = in_source_ts[TS_BITS-1:0];
    assign delta_ts    = in_src_ts60 - r_last_ts;

    // ------------------------------------------------------------------------
    // CAM instance.
    // ------------------------------------------------------------------------
    logic                       cam_access_hit;
    logic [TMPL_IDX_BITS-1:0]   cam_access_idx;
    logic [63:0]                cam_access_old_data;
    logic [1:0]                 cam_access_action;
    logic [63:0]                cam_access_new_data;
    logic                       cam_full;
    logic [$clog2(CAM_DEPTH+1)-1:0] cam_count;
    logic                       cam_evicted;

    localparam logic [1:0] CAM_ACTION_NONE    = 2'b00;
    localparam logic [1:0] CAM_ACTION_TOUCH   = 2'b01;
    localparam logic [1:0] CAM_ACTION_INSTALL = 2'b10;

    monbus_cam #(
        .KEY_WIDTH  (KEY_WIDTH),
        .DATA_WIDTH (64),
        .DEPTH      (CAM_DEPTH)
    ) u_cam (
        .clk             (clk),
        .rst_n           (rst_n),
        .access_key      (in_key),
        .access_hit      (cam_access_hit),
        .access_idx      (cam_access_idx),
        .access_old_data (cam_access_old_data),
        .access_action   (cam_access_action),
        .access_new_data (cam_access_new_data),
        .cam_full        (cam_full),
        .cam_count       (cam_count),
        .evicted         (cam_evicted)
    );

    // ------------------------------------------------------------------------
    // Pipeline stage register (stage 1 lookup/commit -> stage 2 encode/emit).
    //
    // Timing background
    // -----------------
    // The original single-cycle datapath ran
    //   in_packet -> in_key -> CAM 32-way match -> fits/fmt -> slot pack -> FIFO
    // all in one clock. At 100 MHz on the Nexys A7 (-1 speed grade) the
    // fits/fmt/pack tail (a 65-bit signed subtract plus several 60/64-bit
    // magnitude compares) pushed this path negative.
    //
    // Splitting the encode off into its own cycle keeps the CAM
    // lookup-and-commit in a single cycle (stage 1) -- so the CAM/last_ts
    // update SEQUENCE is byte-for-byte identical to the original -- while
    // the heavy arithmetic (fits/fmt/pack) and the RAW beat expansion move
    // to stage 2. The emitted slot STREAM is bit-identical to the old
    // module's, just delayed one cycle. Throughput is unchanged:
    //   tier-1 : 1 record in -> 1 slot  out, 1 record/cycle
    //   tier-0 : 1 record in -> 3 slots out, 1 record/3 cycles
    //
    // Why there is no CAM read-after-write hazard: stage 1 commits the CAM
    // the same cycle it accepts a record (the action depends only on
    // hit/miss, NOT on the stage-2 format decision), exactly as before. The
    // next record's lookup is one cycle later and therefore sees the
    // committed state -- identical ordering to the single-cycle design.
    // ------------------------------------------------------------------------
    localparam logic [1:0] BEAT0 = 2'd0;   // tier-1 slot, or RAW ts beat
    localparam logic [1:0] BEAT1 = 2'd1;   // RAW pkt_hi
    localparam logic [1:0] BEAT2 = 2'd2;   // RAW pkt_lo

    logic                     p_valid;      // stage 2 holds a record
    logic [1:0]               r_beat;       // current output beat
    logic                     p_hit;
    logic [TMPL_IDX_BITS-1:0] p_idx;
    logic [63:0]              p_old_data;
    logic [TS_BITS-1:0]       p_delta_ts;
    logic [63:0]              p_event_data;
    logic [TS_BITS-1:0]       p_src_ts60;
    logic [127:0]             p_packet;

    // ------------------------------------------------------------------------
    // Stage 2: format-fit decisions (combinational on the REGISTERED stage-1
    // lookup result, not the live CAM port).
    // ------------------------------------------------------------------------
    logic fits_a;
    logic fits_b;
    logic fits_c_ts;
    logic fits_c_ed;
    logic fits_c;

    assign fits_a    = (p_delta_ts < (60'(1) << DELTA_TS_A_BITS)) &&
                       (p_event_data < (64'(1) << EVENT_DATA_A_BITS));
    assign fits_b    = (p_delta_ts < (60'(1) << DELTA_TS_B_BITS)) &&
                       (p_event_data < (64'(1) << EVENT_DATA_B_BITS));
    assign fits_c_ts = (p_delta_ts < (60'(1) << DELTA_TS_C_BITS));

    // Full bit-exact signed 64-bit event_data delta (matches Python's
    // _pack_format_c semantics).
    logic signed [64:0] ed_delta_full;
    assign ed_delta_full = $signed({1'b0, p_event_data})
                         - $signed({1'b0, p_old_data});
    assign fits_c_ed = (ed_delta_full >= -(65'sd1 <<< 39)) &&
                       (ed_delta_full <   (65'sd1 <<< 39));
    assign fits_c    = fits_c_ts && fits_c_ed;

    // Format selection (priority A > B > C > RAW; same order as Python).
    typedef enum logic [1:0] {
        FMT_A   = 2'd0,
        FMT_B   = 2'd1,
        FMT_C   = 2'd2,
        FMT_RAW = 2'd3
    } fmt_t;

    fmt_t  fmt_sel;
    always_comb begin
        if (p_hit && fits_a) begin
            fmt_sel = FMT_A;
        end else if (p_hit && fits_b) begin
            fmt_sel = FMT_B;
        end else if (p_hit && fits_c) begin
            fmt_sel = FMT_C;
        end else begin
            fmt_sel = FMT_RAW;
        end
    end

    // ------------------------------------------------------------------------
    // Slot packers — match Python _pack_format_a/b/c verbatim (now sourced
    // from the registered stage-1 values).
    // ------------------------------------------------------------------------
    logic [63:0] slot_a;
    logic [63:0] slot_b;
    logic [63:0] slot_c;
    logic [63:0] slot_raw0;    // tag=0 + ts60

    assign slot_a = {TAG_FORMAT_A,
                     p_idx,
                     p_delta_ts[DELTA_TS_A_BITS-1:0],
                     p_event_data[EVENT_DATA_A_BITS-1:0]};

    assign slot_b = {TAG_FORMAT_B,
                     p_idx,
                     p_delta_ts[DELTA_TS_B_BITS-1:0],
                     p_event_data[EVENT_DATA_B_BITS-1:0]};

    assign slot_c = {TAG_FORMAT_C,
                     p_idx,
                     p_delta_ts[DELTA_TS_C_BITS-1:0],
                     ed_delta_full[EVENT_DATA_C_DELTA-1:0]};

    assign slot_raw0 = {TAG_RAW, p_src_ts60};

    // Beat-0 slot select (tier-1 slot, or RAW ts beat).
    logic [63:0] beat0_slot;
    always_comb begin
        unique case (fmt_sel)
            FMT_A:   beat0_slot = slot_a;
            FMT_B:   beat0_slot = slot_b;
            FMT_C:   beat0_slot = slot_c;
            FMT_RAW: beat0_slot = slot_raw0;
            default: beat0_slot = 64'h0;
        endcase
    end

    // ------------------------------------------------------------------------
    // Stage 2 output mux. Tier-1 emits beat 0 only; tier-0 (RAW) emits
    // beat0 (ts), beat1 (pkt_hi), beat2 (pkt_lo) over three cycles.
    // ------------------------------------------------------------------------
    always_comb begin
        out_valid = p_valid;
        unique case (r_beat)
            BEAT0:   out_slot = beat0_slot;
            BEAT1:   out_slot = p_packet[127:64];
            BEAT2:   out_slot = p_packet[63:0];
            default: out_slot = 64'h0;
        endcase
    end

    // Stage 2 retires (and can take a new record) when it consumes its last
    // beat: beat0 for tier-1, beat2 for tier-0 (RAW).
    logic s2_retire;
    logic s2_can_load;
    logic accept;
    assign s2_retire   = p_valid && out_ready &&
                         (((r_beat == BEAT0) && (fmt_sel != FMT_RAW)) ||
                          (r_beat == BEAT2));
    assign s2_can_load = (!p_valid) || s2_retire;
    assign in_ready    = s2_can_load;
    assign accept      = in_valid && in_ready;

    // ------------------------------------------------------------------------
    // Stage 1 CAM commit (only when we accept a record). The action depends
    // SOLELY on hit/miss -- independent of the stage-2 format decision -- so
    // the CAM remains a single-cycle lookup+commit and the update order is
    // identical to the original module.
    //   hit  -> TOUCH the matched entry with event_data (move-to-front).
    //   miss -> INSTALL the new entry at MRU (evict LRU if full).
    // ------------------------------------------------------------------------
    always_comb begin
        cam_access_action   = CAM_ACTION_NONE;
        cam_access_new_data = in_event_data;
        if (accept) begin
            cam_access_action = cam_access_hit ? CAM_ACTION_TOUCH
                                               : CAM_ACTION_INSTALL;
        end
    end

    // ------------------------------------------------------------------------
    // Pipeline sequential update (stage-1 latch + last_ts + RAW beat walk).
    // ------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            p_valid      <= 1'b0;
            r_beat       <= BEAT0;
            r_last_ts    <= '0;
            p_hit        <= 1'b0;
            p_idx        <= '0;
            p_old_data   <= '0;
            p_delta_ts   <= '0;
            p_event_data <= '0;
            p_src_ts60   <= '0;
            p_packet     <= '0;
        end else begin
            if (accept) begin
                // Stage 1 accepts a record: commit happens on the CAM port
                // this cycle; latch the lookup result + advance last_ts.
                r_last_ts    <= in_src_ts60;
                p_valid      <= 1'b1;
                r_beat       <= BEAT0;
                p_hit        <= cam_access_hit;
                p_idx        <= cam_access_idx;
                p_old_data   <= cam_access_old_data;
                p_delta_ts   <= delta_ts;
                p_event_data <= in_event_data;
                p_src_ts60   <= in_src_ts60;
                p_packet     <= in_packet;
            end else if (s2_retire) begin
                // Stage 2 emptied with no new record to load.
                p_valid <= 1'b0;
            end else if (p_valid && out_ready) begin
                // Mid-RAW beat advance (BEAT0 -> BEAT1 -> BEAT2). BEAT2's
                // retire is handled by the s2_retire branch above.
                if (r_beat == BEAT0)      r_beat <= BEAT1;
                else if (r_beat == BEAT1) r_beat <= BEAT2;
            end
        end
    )

    // ------------------------------------------------------------------------
    // Statistics counters.
    // ------------------------------------------------------------------------
    logic [31:0] r_tier1_a;
    logic [31:0] r_tier1_b;
    logic [31:0] r_tier1_c;
    logic [31:0] r_tier0;
    logic [31:0] r_cam_miss;
    logic [31:0] r_delta_ts_ovf;
    logic [31:0] r_event_data_ovf;
    logic [31:0] r_ed_delta_ovf;

    // Fires exactly once per record, the cycle stage 2 emits its beat 0.
    logic s2_emit_beat0;
    assign s2_emit_beat0 = p_valid && (r_beat == BEAT0) && out_ready;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tier1_a        <= '0;
            r_tier1_b        <= '0;
            r_tier1_c        <= '0;
            r_tier0          <= '0;
            r_cam_miss       <= '0;
            r_delta_ts_ovf   <= '0;
            r_event_data_ovf <= '0;
            r_ed_delta_ovf   <= '0;
        end else if (s2_emit_beat0) begin
            unique case (fmt_sel)
                FMT_A: r_tier1_a <= r_tier1_a + 1;
                FMT_B: r_tier1_b <= r_tier1_b + 1;
                FMT_C: r_tier1_c <= r_tier1_c + 1;
                FMT_RAW: begin
                    r_tier0 <= r_tier0 + 1;
                    // Per Python: classify the escape reason. Miss is
                    // exclusive of overflows; the overflow-priority
                    // mirrors Python's `if delta_ts >= 2^B elif ed >= 2^A`.
                    if (!p_hit) begin
                        r_cam_miss <= r_cam_miss + 1;
                    end else if (p_delta_ts >= (60'(1) << DELTA_TS_B_BITS)) begin
                        r_delta_ts_ovf <= r_delta_ts_ovf + 1;
                    end else if (p_event_data >= (64'(1) << EVENT_DATA_A_BITS)) begin
                        r_event_data_ovf <= r_event_data_ovf + 1;
                    end else begin
                        r_ed_delta_ovf <= r_ed_delta_ovf + 1;
                    end
                end
                default: ;
            endcase
        end
    )

    assign stat_tier1_a        = r_tier1_a;
    assign stat_tier1_b        = r_tier1_b;
    assign stat_tier1_c        = r_tier1_c;
    assign stat_tier0          = r_tier0;
    assign stat_cam_miss       = r_cam_miss;
    assign stat_delta_ts_ovf   = r_delta_ts_ovf;
    assign stat_event_data_ovf = r_event_data_ovf;
    assign stat_ed_delta_ovf   = r_ed_delta_ovf;

endmodule : monbus_compressor
