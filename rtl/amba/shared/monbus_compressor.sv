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
//   per-template last_ts -- each CAM entry stores its own last timestamp
//                           (low TS_STORE_BITS); delta_ts is measured per
//                           template, so interleaved sources don't escape
//   monbus_cam            -- 32-entry LRU CAM (sub-instance)
//   FSM                   -- 3 states: IDLE / RAW1 / RAW2
//
// Pipeline (3 stages)
// -------------------
// Stage 1 (lookup/commit, p_*): key build -> CAM lookup -> CAM commit (incl.
//          this record's per-template timestamp). The CAM still does
//          lookup+commit in a single cycle, so its update SEQUENCE (and the
//          emitted slot stream) is bit-exact to the original module.
// Stage 2a (encode register, q_*): delta/fits/format-select -> slot pack,
//          REGISTERED. Registering the format decision keeps the 65-bit
//          format-C ed_delta + fits off the stage-1 commit / input-handshake
//          path -- that fused path was the 100 MHz critical path.
// Stage 2b (output): drive the slot(s); RAW (tier-0) beat expansion.
//
// Throughput is unchanged:
//   Tier-1 records: 1 record/cycle (1 slot out).
//   Tier-0 records: 1 record / 3 cycles (3 slots out).
// The extra encode register adds one cycle of latency only -- bandwidth is
// preserved, and the slot stream is identical (just delayed).
//
// No CAM read-after-write hazard: the commit (action = hit ? TOUCH : INSTALL)
// depends only on the stage-1 lookup, not on the registered format decision.
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
#(
    // 0 = 64-bit-slot codec only (default; the committed, timing-closed path).
    // 1 = also expose a 30-bit half-slot sideband (out_half_*) for the
    //     downstream monbus_halfbeat_packer. The slot STREAM out_slot is
    //     unchanged; the sideband just tells the packer when a tier-1 record
    //     also fits a 30-bit half-slot (and supplies it). All half logic
    //     constant-folds away when HALF_BEAT_EN==0.
    parameter int HALF_BEAT_EN = 0,
    // 0 = single-cycle monbus_cam (default; committed, timing-directive path).
    // 1 = 2-cycle monbus_cam_pipe: splits the route-bound compare ->
    //     priority-encode -> move-to-front-shift chain across two cycles with a
    //     depth-1 forwarding CAM + a credit-gated result skid (full throughput).
    //     +1 record latency on the compression path; slot stream bit-identical.
    parameter int CAM_PIPELINE = 0
) (
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

    // === Half-beat sideband (HALF_BEAT_EN==1; tied 0 otherwise) ===
    // Valid alongside out_valid on a tier-1 beat that also fits a 30-bit
    // half-slot. The packer buffers/pairs out_half_slot and ignores out_slot
    // for that beat; when out_half_valid==0 the beat is a full 64-bit slot or
    // a raw payload beat and the packer forwards out_slot verbatim.
    output logic                    out_half_valid,
    output logic [29:0]             out_half_slot,

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

    // Half-slot format (see monbus_compressor.py): a 30-bit slot is
    // {sub[1:0], idx[4:0], delta_ts[HALF_DELTA_BITS-1:0], data[HALF_DATA_BITS-1:0]}.
    localparam int         HALF_DELTA_BITS = 10;
    localparam int         HALF_DATA_BITS  = 13;
    localparam logic [1:0] HSUB_A          = 2'h1;
    localparam logic [1:0] HSUB_C          = 2'h2;

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
    // Per-template delta computation.
    //
    // delta_ts is measured against the matched template's OWN last timestamp
    // (stored per CAM entry), NOT a single global last_ts. With multiple
    // interleaved monitor sources (e.g. N channels) a global delta hops
    // between sources and wraps negative, forcing ~1/3 of records to RAW;
    // each source's own stream is monotonic, so a per-template delta stays
    // small and positive and fits Tier-1. Only the low TS_STORE_BITS of the
    // timestamp are kept per entry (enough to represent + detect-overflow any
    // realistic in-template gap; gaps >= 2^TS_STORE_BITS cycles are beyond a
    // run and would mis-compress, same caveat as any delta scheme).
    // ------------------------------------------------------------------------
    localparam int TS_STORE_BITS = 24;
    logic [TS_BITS-1:0]        in_src_ts60;
    logic [TS_STORE_BITS-1:0]  in_src_ts_lo;
    logic [TS_STORE_BITS-1:0]  cam_access_old_ts;
    logic [TS_BITS-1:0]        delta_ts;
    assign in_src_ts60  = in_source_ts[TS_BITS-1:0];
    assign in_src_ts_lo = in_src_ts60[TS_STORE_BITS-1:0];
    // Per-template delta (valid on a hit; on a miss the record goes RAW and
    // delta_ts is unused). Zero-extended to TS_BITS for the fits checks.
    assign delta_ts = {{(TS_BITS-TS_STORE_BITS){1'b0}},
                       (in_src_ts_lo - cam_access_old_ts)};

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

    // Stage-1 result registers (p_*) and the handshake signals the CAM
    // generate below references. DECLARED HERE, before the generate, so there
    // is no forward reference: tools that bind generate-scope identifiers to
    // implicit local nets (Vivado) would otherwise create phantom wires that
    // never connect to the module-level signals (sim/synth divergence). The
    // pre-commit check (bin/check_sv_decl_order.py) enforces this.
    logic                     p_valid;
    logic                     p_hit;
    logic [TMPL_IDX_BITS-1:0] p_idx;
    logic [63:0]              p_old_data;
    logic [TS_BITS-1:0]       p_delta_ts;
    logic [63:0]              p_event_data;
    logic [TS_BITS-1:0]       p_src_ts60;
    logic [127:0]             p_packet;
    logic                     enc_commit;   // a record is encoded into q this cycle
    logic                     cam_en;       // path-1 present-to-CAM (driven in gen_cam_pipe)

    generate
    if (CAM_PIPELINE == 0) begin : gen_cam_single
        monbus_cam #(
            .KEY_WIDTH  (KEY_WIDTH),
            .DATA_WIDTH (64),
            .TS_WIDTH   (TS_STORE_BITS),
            .DEPTH      (CAM_DEPTH)
        ) u_cam (
            .clk             (clk),
            .rst_n           (rst_n),
            .access_key      (in_key),
            .access_hit      (cam_access_hit),
            .access_idx      (cam_access_idx),
            .access_old_data (cam_access_old_data),
            .access_old_ts   (cam_access_old_ts),
            .access_action   (cam_access_action),
            .access_new_data (cam_access_new_data),
            .access_new_ts   (in_src_ts_lo),
            .cam_full        (cam_full),
            .cam_count       (cam_count),
            .evicted         (cam_evicted)
        );
        assign cam_en = 1'b0;   // unused in the single-cycle path
    end else begin : gen_cam_pipe
        // ---- 2-cycle pipelined CAM + credit-gated result skid ----
        // Present a record to the CAM at cycle T (cam_en); its result and a
        // record-aligned copy of the fields arrive at T+1 and are pushed into
        // a 2-deep skid. p_* are driven combinationally from the skid output,
        // so stage 2 (q) is unchanged. A credit counter (in-flight + skid
        // occupancy) gates cam_en so every autonomous result has a slot.
        localparam int SKID_DEPTH = 2;
        // p_hit + p_idx + p_old_data + p_delta_ts + p_event_data + p_src_ts60 + p_packet
        localparam int P_W = 1 + TMPL_IDX_BITS + 64 + TS_BITS + 64 + TS_BITS + 128;

        logic                      pipe_res_valid;
        logic                      pipe_res_hit;
        logic [TMPL_IDX_BITS-1:0]  pipe_res_idx;
        logic [63:0]               pipe_res_old_data;
        logic [TS_STORE_BITS-1:0]  pipe_res_old_ts;

        // Credit: records presented but not yet popped from the skid (cam_en
        // is the top-level present signal, muxed into in_ready above).
        logic [2:0]                r_credit;
        logic                      pop;            // skid read handshake
        assign cam_en = in_valid && (r_credit < 3'(SKID_DEPTH));

        monbus_cam_pipe #(
            .KEY_WIDTH(KEY_WIDTH), .DATA_WIDTH(64),
            .TS_WIDTH(TS_STORE_BITS), .DEPTH(CAM_DEPTH)
        ) u_cam_pipe (
            .clk(clk), .rst_n(rst_n),
            .access_en(cam_en), .access_key(in_key),
            .access_new_data(in_event_data), .access_new_ts(in_src_ts_lo),
            .result_valid(pipe_res_valid), .result_hit(pipe_res_hit),
            .result_idx(pipe_res_idx), .result_old_data(pipe_res_old_data),
            .result_old_ts(pipe_res_old_ts),
            .cam_full(), .cam_count()
        );

        // Record fields aligned with the result (registered when presented).
        logic [127:0]              m_packet;
        logic [63:0]               m_event_data;
        logic [TS_BITS-1:0]        m_src_ts60;
        logic [TS_STORE_BITS-1:0]  m_src_ts_lo;
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                m_packet <= '0; m_event_data <= '0; m_src_ts60 <= '0; m_src_ts_lo <= '0;
            end else if (cam_en) begin
                m_packet     <= in_packet;
                m_event_data <= in_event_data;
                m_src_ts60   <= in_src_ts60;
                m_src_ts_lo  <= in_src_ts_lo;
            end
        )

        // Per-template delta off the registered result (short, off the path).
        logic [TS_BITS-1:0] pipe_delta_ts;
        assign pipe_delta_ts = {{(TS_BITS-TS_STORE_BITS){1'b0}},
                                (m_src_ts_lo - pipe_res_old_ts)};

        // Skid input payload = the full stage-1 result.
        logic [P_W-1:0] skid_wr_data, skid_rd_data;
        logic           skid_rd_valid, skid_wr_ready;
        assign skid_wr_data = {pipe_res_hit, pipe_res_idx, pipe_res_old_data,
                               pipe_delta_ts, m_event_data, m_src_ts60, m_packet};

        gaxi_skid_buffer #(.DATA_WIDTH(P_W), .DEPTH(SKID_DEPTH)) u_res_skid (
            .axi_aclk(clk), .axi_aresetn(rst_n),
            .wr_valid(pipe_res_valid), .wr_ready(skid_wr_ready),
            .wr_data(skid_wr_data), .count(),
            .rd_valid(skid_rd_valid), .rd_ready(pop),
            .rd_count(), .rd_data(skid_rd_data)
        );

        // p_* driven from the skid output; stage 2 consumes via enc_commit.
        assign p_valid    = skid_rd_valid;
        assign {p_hit, p_idx, p_old_data, p_delta_ts, p_event_data, p_src_ts60,
                p_packet} = skid_rd_data;
        assign pop        = enc_commit;

        // credit = in-flight (presented, result pending) + skid occupancy.
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) r_credit <= 3'd0;
            else r_credit <= r_credit + 3'(cam_en) - 3'(pop && skid_rd_valid);
        )

        // Unused single-cycle CAM nets in this path (cam_access_action /
        // cam_access_new_data are driven by the shared always_comb; harmless
        // here as no monbus_cam consumes them).
        assign cam_access_hit      = 1'b0;
        assign cam_access_idx      = '0;
        assign cam_access_old_data = '0;
        assign cam_access_old_ts   = '0;
        assign cam_full            = 1'b0;
        assign cam_count           = '0;
        assign cam_evicted         = 1'b0;
    end
    endgenerate

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

    // Stage 1 result registers (p_*) are declared above, before the CAM
    // generate that references them.

    // Stage 2a (REGISTERED encode result). Registering the format decision
    // here keeps the 65-bit format-C ed_delta + fits/fmt off the stage-1 CAM
    // commit / input-handshake path (it was the 100 MHz worst path). The
    // output handshake below uses q_is_raw (registered), not the live fmt.
    logic                     q_valid;
    logic                     q_is_raw;     // 1 = RAW (3 beats), 0 = tier-1 (1 beat)
    logic [63:0]              q_beat0;      // tier-1 slot, or RAW ts beat
    logic [127:0]             q_packet;     // RAW beats 1/2
    logic [1:0]               r_beat;       // stage-2b output beat counter
    logic                     q_half_valid; // registered half-slot sideband
    logic [29:0]              q_half_slot;

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
    // Half-beat sideband. A tier-1 hit that ALSO fits a 30-bit slot is offered
    // to the downstream packer (which buffers two into one beat). Priority
    // mirrors the Python golden: half-A, then half-C, then the full 64-bit
    // formats. All of this constant-folds away when HALF_BEAT_EN==0.
    // ------------------------------------------------------------------------
    logic        half_a_fit;
    logic        half_c_fit;
    logic [29:0] half_slot_a;
    logic [29:0] half_slot_c;
    logic        half_valid_c;     // combinational "this record fits a half-slot"
    logic [29:0] half_slot_sel;

    assign half_a_fit = (HALF_BEAT_EN != 0) && p_hit &&
                        (p_delta_ts   < (60'(1) << HALF_DELTA_BITS)) &&
                        (p_event_data < (64'(1) << HALF_DATA_BITS));
    assign half_c_fit = (HALF_BEAT_EN != 0) && p_hit &&
                        (p_delta_ts < (60'(1) << HALF_DELTA_BITS)) &&
                        (ed_delta_full >= -(65'sd1 <<< (HALF_DATA_BITS-1))) &&
                        (ed_delta_full <   (65'sd1 <<< (HALF_DATA_BITS-1)));

    assign half_slot_a = {HSUB_A, p_idx,
                          p_delta_ts[HALF_DELTA_BITS-1:0],
                          p_event_data[HALF_DATA_BITS-1:0]};
    assign half_slot_c = {HSUB_C, p_idx,
                          p_delta_ts[HALF_DELTA_BITS-1:0],
                          ed_delta_full[HALF_DATA_BITS-1:0]};

    assign half_valid_c  = half_a_fit || half_c_fit;
    assign half_slot_sel = half_a_fit ? half_slot_a : half_slot_c;

    // Classification used for the stat counters so a half-A counts as tier1_a
    // and a half-C as tier1_c (matches the golden). Identical to fmt_sel when
    // HALF_BEAT_EN==0.
    fmt_t stat_class;
    always_comb begin
        if      (half_a_fit) stat_class = FMT_A;
        else if (half_c_fit) stat_class = FMT_C;
        else                 stat_class = fmt_sel;
    end

    // ------------------------------------------------------------------------
    // Stage 2b output mux (from the REGISTERED encode result q_*). Tier-1
    // emits beat 0 only; RAW emits beat0 (ts), beat1 (pkt_hi), beat2 (pkt_lo).
    // ------------------------------------------------------------------------
    always_comb begin
        out_valid = q_valid;
        unique case (r_beat)
            BEAT0:   out_slot = q_beat0;
            BEAT1:   out_slot = q_packet[127:64];
            BEAT2:   out_slot = q_packet[63:0];
            default: out_slot = 64'h0;
        endcase
    end

    // Half-beat sideband: only meaningful on a tier-1 beat (beat0, !raw).
    assign out_half_valid = q_valid && q_half_valid && (r_beat == BEAT0);
    assign out_half_slot  = q_half_slot;

    // Handshake. q (stage 2b) retires when it emits its last beat (beat0 for
    // tier-1, beat2 for RAW); then it can take p's encoded record (q_can_load);
    // then stage 1 (and the CAM commit) can accept a new input (p_can_load).
    // q_is_raw is REGISTERED, so none of this passes through the format-C
    // ed_delta -- that was the 100 MHz worst path.
    logic q_retire;
    logic q_can_load;
    logic p_can_load;
    logic accept;
    // enc_commit and cam_en are declared earlier (before the CAM generate).
    assign q_retire   = q_valid && out_ready &&
                        (((r_beat == BEAT0) && !q_is_raw) || (r_beat == BEAT2));
    assign q_can_load = (!q_valid) || q_retire;
    assign enc_commit = p_valid && q_can_load;
    assign p_can_load = (!p_valid) || q_can_load;
    // Single-cycle: gate input on p free. Pipelined: gate on the CAM credit
    // (cam_en, computed in gen_cam_pipe). p_valid is a register in the single
    // path and the skid rd_valid in the pipelined path.
    assign in_ready   = (CAM_PIPELINE != 0) ? cam_en : p_can_load;
    assign accept     = in_valid && p_can_load;

    // ------------------------------------------------------------------------
    // Stage 1 CAM commit (only when we accept a record). The action depends
    // SOLELY on hit/miss -- independent of the format decision -- so the CAM
    // stays a single-cycle lookup+commit and the update order is unchanged.
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
    // Pipeline sequential update: stage 1 lookup latch, stage 2a encode
    // register, stage 2b output beat walk. (Per-template last_ts lives in the
    // CAM via access_new_ts.)
    // ------------------------------------------------------------------------
    // ---- Stage 1 register (p_*): forked by CAM_PIPELINE below. The
    // single-cycle path drives p_* from this always_ff; the pipelined path
    // drives p_* combinationally from its result skid (see the generate).
    if (CAM_PIPELINE == 0) begin : gen_p_single
        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                p_valid      <= 1'b0;
                p_hit        <= 1'b0;
                p_idx        <= '0;
                p_old_data   <= '0;
                p_delta_ts   <= '0;
                p_event_data <= '0;
                p_src_ts60   <= '0;
                p_packet     <= '0;
            end else begin
                // Stage 1: accept a new record (the CAM commits this cycle,
                // incl. this record's timestamp via access_new_ts).
                if (accept) begin
                    p_valid      <= 1'b1;
                    p_hit        <= cam_access_hit;
                    p_idx        <= cam_access_idx;
                    p_old_data   <= cam_access_old_data;
                    p_delta_ts   <= delta_ts;
                    p_event_data <= in_event_data;
                    p_src_ts60   <= in_src_ts60;
                    p_packet     <= in_packet;
                end else if (enc_commit) begin
                    // p's record moved into q with nothing new to replace it.
                    p_valid <= 1'b0;
                end
            end
        )
    end

    // ---- Stage 2 register (q_* / r_beat): common to both CAM variants. Reads
    // p_* (single-cycle reg or pipelined skid output) the same way.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            q_valid      <= 1'b0;
            q_is_raw     <= 1'b0;
            q_beat0      <= '0;
            q_packet     <= '0;
            r_beat       <= BEAT0;
            q_half_valid <= 1'b0;
            q_half_slot  <= '0;
        end else begin
            // Stage 2a: register the encode result when q takes p's record
            // (reads this cycle's combinational fmt_sel / beat0_slot).
            if (enc_commit) begin
                q_valid      <= 1'b1;
                q_is_raw     <= (fmt_sel == FMT_RAW);
                q_beat0      <= beat0_slot;
                q_packet     <= p_packet;
                r_beat       <= BEAT0;
                q_half_valid <= half_valid_c;
                q_half_slot  <= half_slot_sel;
            end else if (q_retire) begin
                q_valid <= 1'b0;
            end else if (q_valid && out_ready) begin
                // Stage 2b: RAW beat advance (BEAT0 -> BEAT1 -> BEAT2).
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

    // Counted once per record, the cycle it is encoded into q (enc_commit),
    // using that cycle's combinational fmt_sel / p_* values.
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
        end else if (enc_commit) begin
            // stat_class == fmt_sel when HALF_BEAT_EN==0; otherwise a half-A
            // counts as tier1_a and a half-C as tier1_c (matches the golden).
            unique case (stat_class)
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
