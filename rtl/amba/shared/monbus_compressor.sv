// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_compressor
// Purpose: Hardware encoder for the bulk-trace monbus compression
//          format locked in commit 5bbb83d1. Sits in front of the
//          AXIL writer inside monbus_axil_group when the wrapper
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
// Pipeline
// --------
// Tier-1 records: 1 cycle in -> 1 slot out. Throughput 1 record/cycle
//                 (assuming both handshakes are ready).
// Tier-0 records: 1 cycle in -> 3 slots out (over 3 cycles). Throughput
//                 1 record / 3 cycles.
//
// The combinational path on cycle 0 includes:
//   key build -> CAM lookup -> delta_ts -> format select -> slot pack
// Substantial logic depth; if timing closure becomes an issue, register
// the CAM lookup result and add a "decide" pipeline stage. For typical
// monbus traffic at 100 MHz this should close comfortably.
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
    // Format-fit decisions (combinational on this cycle's lookup result).
    // ------------------------------------------------------------------------
    logic fits_a;
    logic fits_b;
    logic fits_c_ts;
    logic fits_c_ed;
    logic fits_c;
    logic signed [40:0] ed_delta_s;   // 41-bit so we can range-check 40-bit signed

    assign fits_a    = (delta_ts < (60'(1) << DELTA_TS_A_BITS)) &&
                       (in_event_data < (64'(1) << EVENT_DATA_A_BITS));
    assign fits_b    = (delta_ts < (60'(1) << DELTA_TS_B_BITS)) &&
                       (in_event_data < (64'(1) << EVENT_DATA_B_BITS));
    assign fits_c_ts = (delta_ts < (60'(1) << DELTA_TS_C_BITS));

    // Signed 41-bit subtract; in-range iff value sign-extends to fit 40 bits.
    assign ed_delta_s = $signed({1'b0, in_event_data[39:0]})
                      - $signed({1'b0, cam_access_old_data[39:0]});
    // Above is for the low 40 bits only. For the FULL bit-exact signed
    // delta in 64 bits, do it as:
    //   ed_delta_full = $signed(in_event_data) - $signed(old);
    //   fits_c_ed = (ed_delta_full >= -(1<<39)) && (ed_delta_full < (1<<39))
    //
    // ...which is the correct semantics per Python. Use that instead.
    logic signed [64:0] ed_delta_full;
    assign ed_delta_full = $signed({1'b0, in_event_data})
                         - $signed({1'b0, cam_access_old_data});
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
        if (cam_access_hit && fits_a) begin
            fmt_sel = FMT_A;
        end else if (cam_access_hit && fits_b) begin
            fmt_sel = FMT_B;
        end else if (cam_access_hit && fits_c) begin
            fmt_sel = FMT_C;
        end else begin
            fmt_sel = FMT_RAW;
        end
    end

    // ------------------------------------------------------------------------
    // Slot packers — match Python _pack_format_a/b/c verbatim.
    // ------------------------------------------------------------------------
    logic [63:0] slot_a;
    logic [63:0] slot_b;
    logic [63:0] slot_c;
    logic [63:0] slot_raw0;    // tag=0 + ts60

    assign slot_a = {TAG_FORMAT_A,
                     cam_access_idx,
                     delta_ts[DELTA_TS_A_BITS-1:0],
                     in_event_data[EVENT_DATA_A_BITS-1:0]};

    assign slot_b = {TAG_FORMAT_B,
                     cam_access_idx,
                     delta_ts[DELTA_TS_B_BITS-1:0],
                     in_event_data[EVENT_DATA_B_BITS-1:0]};

    assign slot_c = {TAG_FORMAT_C,
                     cam_access_idx,
                     delta_ts[DELTA_TS_C_BITS-1:0],
                     ed_delta_full[EVENT_DATA_C_DELTA-1:0]};

    assign slot_raw0 = {TAG_RAW, in_src_ts60};

    // ------------------------------------------------------------------------
    // FSM: 3 states (IDLE, RAW1, RAW2). Tier-1 lives in IDLE entirely
    // (single-cycle); Tier-0 occupies all three (one cycle per beat).
    // ------------------------------------------------------------------------
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_RAW1 = 2'd1,
        S_RAW2 = 2'd2
    } state_t;

    state_t r_state;
    logic [127:0] r_pkt;   // latched packet for raw beats 1/2

    // Combinational outputs.
    logic        out_valid_idle;
    logic [63:0] out_slot_idle;
    always_comb begin
        unique case (fmt_sel)
            FMT_A:   out_slot_idle = slot_a;
            FMT_B:   out_slot_idle = slot_b;
            FMT_C:   out_slot_idle = slot_c;
            FMT_RAW: out_slot_idle = slot_raw0;
            default: out_slot_idle = 64'h0;
        endcase
        out_valid_idle = in_valid;
    end

    always_comb begin
        case (r_state)
            S_IDLE: begin
                out_valid = out_valid_idle;
                out_slot  = out_slot_idle;
            end
            S_RAW1: begin
                out_valid = 1'b1;
                out_slot  = r_pkt[127:64];
            end
            S_RAW2: begin
                out_valid = 1'b1;
                out_slot  = r_pkt[63:0];
            end
            default: begin
                out_valid = 1'b0;
                out_slot  = 64'h0;
            end
        endcase
    end

    // in_ready only when we can absorb a new record AND emit at least
    // beat 0 in the same cycle.
    assign in_ready = (r_state == S_IDLE) && out_ready;

    // CAM action (only meaningful in S_IDLE when we accept a record).
    //   Tier-1 (any sub-format) -> TOUCH the matched entry with event_data.
    //   Tier-0 with hit (overflow) -> still TOUCH (Python's install()
    //                                  hits the existing entry and just
    //                                  updates data + move-to-front).
    //   Tier-0 with miss -> INSTALL the new entry.
    always_comb begin
        cam_access_action   = CAM_ACTION_NONE;
        cam_access_new_data = in_event_data;
        if ((r_state == S_IDLE) && in_valid && in_ready) begin
            cam_access_action = cam_access_hit ? CAM_ACTION_TOUCH
                                               : CAM_ACTION_INSTALL;
        end
    end

    // ------------------------------------------------------------------------
    // Sequential update (FSM + r_last_ts + r_pkt).
    // ------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state   <= S_IDLE;
            r_last_ts <= '0;
            r_pkt     <= '0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (in_valid && in_ready) begin
                        r_last_ts <= in_src_ts60;
                        if (fmt_sel == FMT_RAW) begin
                            r_pkt   <= in_packet;
                            r_state <= S_RAW1;
                        end
                        // Tier-1: state stays IDLE; the slot was emitted.
                    end
                end
                S_RAW1: begin
                    if (out_ready) r_state <= S_RAW2;
                end
                S_RAW2: begin
                    if (out_ready) r_state <= S_IDLE;
                end
                default: r_state <= S_IDLE;
            endcase
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
        end else if ((r_state == S_IDLE) && in_valid && in_ready) begin
            unique case (fmt_sel)
                FMT_A: r_tier1_a <= r_tier1_a + 1;
                FMT_B: r_tier1_b <= r_tier1_b + 1;
                FMT_C: r_tier1_c <= r_tier1_c + 1;
                FMT_RAW: begin
                    r_tier0 <= r_tier0 + 1;
                    // Per Python: classify the escape reason. Miss is
                    // exclusive of overflows; the overflow-priority
                    // mirrors Python's `if delta_ts >= 2^B elif ed >= 2^A`.
                    if (!cam_access_hit) begin
                        r_cam_miss <= r_cam_miss + 1;
                    end else if (delta_ts >= (60'(1) << DELTA_TS_B_BITS)) begin
                        r_delta_ts_ovf <= r_delta_ts_ovf + 1;
                    end else if (in_event_data >= (64'(1) << EVENT_DATA_A_BITS)) begin
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
