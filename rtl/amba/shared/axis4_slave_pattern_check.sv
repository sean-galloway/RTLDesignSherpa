// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis4_slave_pattern_check
// Purpose: AXI-Stream slave that checks a deterministic, PER-CHANNEL LFSR data
//          pattern. This is the AXIS SOURCE checker for the RAPIDS
//          characterization harness and is pattern/CRC-CONSISTENT with
//          axi4_slave_rd_pattern_gen: the per-channel 32-bit CRC-32 it computes
//          is bit-identical to axi4_slave_rd_pattern_gen.read_crc_value for the
//          same stream (source self-check: rd_gen -> m_axis -> axis_check).
//
// Description:
//   On cfg_start every channel's LFSR is seeded identically to the generator
//   (seed ^ ch). Incoming beats are DEMUXed by s_axis_tid[CIW-1:0] into the
//   matching channel context. On each accepted beat for channel ch:
//     - the received tdata is compared against the locally-regenerated pattern
//       {REP{lfsr_out[ch]}}; any mismatch latches o_data_error (sticky);
//     - that channel's LFSR + dataint_crc-32 advance (fed the 32-bit
//       lfsr_out[ch], exactly like axi4_slave_rd_pattern_gen).
//   The LFSR advances only on accepted beats, so the check is independent of
//   upstream stalls / interleave order across channels.
//
//   Per-channel CRC (o_actual_crc[ch]/o_actual_crc_valid[ch]) mirrors
//   axi4_slave_rd_pattern_gen.read_crc_value semantics -- NOT the old XOR-fold.
//
// CRC bit-consistency (copied VERBATIM from the axi4 blocks): identical LFSR
//   (WIDTH=32, TAP_INDEX_WIDTH=12, TAP_COUNT=4, seed ^ ch) + identical
//   dataint_crc (DATA_WIDTH=32, CRC_WIDTH=32, POLY=0x04C11DB7,
//   POLY_INIT=0xFFFFFFFF, XOROUT=0xFFFFFFFF, REFIN=1, REFOUT=1,
//   cascade_sel=4'b1000, data=lfsr_out[ch]) with the same gating
//   (load_crc_start=cfg_start, load_from_cascade=accepted-beat-for-ch).
//
// Notes:
//   - AXIS_DATA_WIDTH must be a multiple of LFSR_WIDTH.
//   - s_axis_tready = ready_en (pure sink; deassert to model backpressure).
//
// Documentation: projects/components/dmas/rapids/CONTROL_ENGINE_INTEGRATION.md (harness)
// Subsystem: amba/shared

`timescale 1ns / 1ps

module axis4_slave_pattern_check #(
    parameter int          NUM_CHANNELS     = 1,
    parameter int          AXIS_DATA_WIDTH  = 512,
    parameter int          AXIS_ID_WIDTH    = 8,
    parameter int          AXIS_DEST_WIDTH  = 4,
    parameter int          AXIS_USER_WIDTH  = 1,

    // LFSR parameters (32-bit fixed; MUST MATCH axi4_slave_rd_pattern_gen!)
    parameter int          LFSR_WIDTH       = 32,
    parameter logic [31:0] LFSR_SEED        = 32'hDEADBEEF,
    parameter logic [47:0] LFSR_TAPS        = {12'd32, 12'd22, 12'd2, 12'd1},

    // CRC parameters (fixed; MUST MATCH axi4_slave_rd_pattern_gen!)
    parameter int          CRC_WIDTH        = 32,
    parameter int          CRC_DATA_WIDTH   = 32,
    parameter logic [31:0] CRC_POLY         = 32'h04C11DB7,
    parameter logic [31:0] CRC_INIT         = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT       = 32'hFFFFFFFF,
    parameter int          CRC_REFIN        = 1,
    parameter int          CRC_REFOUT       = 1,

    parameter int          BEAT_COUNT_WIDTH = 32,
    // Derived
    parameter int          STRB_WIDTH       = AXIS_DATA_WIDTH / 8,
    parameter int          REP              = AXIS_DATA_WIDTH / LFSR_WIDTH,
    parameter int          CIW              = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Configuration / control
    input  logic                          cfg_start,          // pulse: arm + seed all channels
    input  logic [LFSR_WIDTH-1:0]         cfg_lfsr_seed,      // 0 => use LFSR_SEED param
    input  logic                          ready_en,           // s_axis_tready = ready_en

    // Per-channel actual CRC (mirrors axi4_slave_rd_pattern_gen.read_crc_value)
    output logic [NUM_CHANNELS-1:0][31:0] o_actual_crc,
    output logic [NUM_CHANNELS-1:0]       o_actual_crc_valid,
    output logic                          o_data_error,       // sticky: any beat mismatch
    output logic [NUM_CHANNELS-1:0][31:0] o_beat_count,       // per-channel beats received
    output logic [31:0]                   o_beat_count_total, // sum across channels
    output logic [BEAT_COUNT_WIDTH-1:0]   o_pkt_count,        // tlast beats received (aggregate)

    // AXI-Stream slave
    input  logic                          s_axis_tvalid,
    output logic                          s_axis_tready,
    input  logic [AXIS_DATA_WIDTH-1:0]    s_axis_tdata,
    input  logic [STRB_WIDTH-1:0]         s_axis_tstrb,
    input  logic                          s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]      s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]    s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]    s_axis_tuser
);

    localparam int LFSR_TAP_INDEX_WIDTH = 12;
    localparam int LFSR_TAP_COUNT       = 4;

    logic                       w_load;
    logic                       w_beat;
    logic [CIW-1:0]             w_ch;
    logic [LFSR_WIDTH-1:0]      w_seed;

    logic [31:0]                lfsr_out_per_ch      [NUM_CHANNELS];
    logic [31:0]                crc_out_per_ch       [NUM_CHANNELS];
    logic [AXIS_DATA_WIDTH-1:0] expected_data_per_ch [NUM_CHANNELS];

    // Sink readiness driven by ready_en (tie high for a pure sink; deassert to
    // model backpressure). Drives the SAME handshake the upstream sees, so both
    // sides advance in lockstep.
    assign s_axis_tready = ready_en;

    assign w_load = cfg_start;
    assign w_seed = (cfg_lfsr_seed == '0) ? LFSR_SEED[LFSR_WIDTH-1:0] : cfg_lfsr_seed;
    assign w_beat = s_axis_tvalid && s_axis_tready;
    assign w_ch   = (NUM_CHANNELS == 1) ? '0 : s_axis_tid[CIW-1:0];

    //==========================================================================
    // Per-channel LFSR pattern regenerators + CRC-32 calculators
    //==========================================================================
    // seed/taps/replication/CRC instantiation + gating are copied VERBATIM from
    // axi4_slave_rd_pattern_gen so the per-channel 32-bit CRC is bit-identical.

    genvar gch;
    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_ch
            logic ch_beat;
            logic r_ch_crc_valid;
            logic [31:0] r_ch_beat_count;

            // This channel advances only on an accepted beat carrying its tid;
            // all channels (re)load their seed on the arm pulse.
            assign ch_beat = w_beat && (w_ch == gch[CIW-1:0]);

            shifter_lfsr_fibonacci #(
                .WIDTH          (LFSR_WIDTH),
                .TAP_INDEX_WIDTH(LFSR_TAP_INDEX_WIDTH),
                .TAP_COUNT      (LFSR_TAP_COUNT)
            ) u_lfsr (
                .clk      (clk),
                .rst_n    (rst_n),
                .enable   (ch_beat || w_load),
                .seed_load(w_load),
                .seed_data(w_seed ^ 32'(gch)),   // unique seed per channel
                .taps     (LFSR_TAPS),
                .lfsr_out (lfsr_out_per_ch[gch]),
                .lfsr_done()
            );

            assign expected_data_per_ch[gch] = {REP{lfsr_out_per_ch[gch]}};

            dataint_crc #(
                .DATA_WIDTH(CRC_DATA_WIDTH),
                .CRC_WIDTH (CRC_WIDTH),
                .REFIN     (CRC_REFIN),
                .REFOUT    (CRC_REFOUT)
            ) u_crc (
                .POLY             (CRC_POLY),
                .POLY_INIT        (CRC_INIT),
                .XOROUT           (CRC_XOROUT),
                .clk              (clk),
                .rst_n            (rst_n),
                .load_crc_start   (w_load),
                .load_from_cascade(ch_beat),
                .cascade_sel      (4'b1000),          // process all 4 bytes of 32-bit slice
                .data             (lfsr_out_per_ch[gch]),
                .crc              (crc_out_per_ch[gch])
            );

            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    r_ch_crc_valid  <= 1'b0;
                    r_ch_beat_count <= '0;
                end else if (w_load) begin
                    r_ch_crc_valid  <= 1'b0;
                    r_ch_beat_count <= '0;
                end else if (ch_beat) begin
                    r_ch_crc_valid  <= 1'b1;
                    r_ch_beat_count <= r_ch_beat_count + 1'b1;
                end
            end

            assign o_actual_crc      [gch] = crc_out_per_ch[gch];
            assign o_actual_crc_valid[gch] = r_ch_crc_valid;
            assign o_beat_count      [gch] = r_ch_beat_count;
        end
    endgenerate

    // Aggregate beat count (sum across channels) for the harness timer.
    always_comb begin
        o_beat_count_total = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            o_beat_count_total = o_beat_count_total + o_beat_count[ch];
        end
    end

    //==========================================================================
    // Sticky data-error + aggregate packet counter
    //==========================================================================
    // Compare the received beat against the active channel's regenerated
    // expected data (current LFSR value, before it advances this same edge).

    logic w_data_mismatch;
    assign w_data_mismatch = w_beat && (s_axis_tdata != expected_data_per_ch[w_ch]);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            o_data_error <= 1'b0;
            o_pkt_count  <= '0;
        end else if (cfg_start) begin
            o_data_error <= 1'b0;
            o_pkt_count  <= '0;
        end else if (w_beat) begin
            if (w_data_mismatch)  o_data_error <= 1'b1;
            if (s_axis_tlast)     o_pkt_count  <= o_pkt_count + 1'b1;
        end
    end

endmodule : axis4_slave_pattern_check
