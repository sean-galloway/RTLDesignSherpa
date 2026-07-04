// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis4_master_pattern_gen
// Purpose: AXI-Stream master that emits a deterministic, PER-CHANNEL LFSR data
//          pattern for characterization/verification. This is the AXIS SINK
//          stimulus for the RAPIDS characterization harness and is
//          pattern/CRC-CONSISTENT with axi4_slave_rd_pattern_gen /
//          axi4_slave_wr_crc_check: the per-channel 32-bit CRC-32 it computes
//          is bit-identical to what axi4_slave_wr_crc_check produces for the
//          same emitted stream (sink self-check: axis_gen -> m_axi_wr ->
//          wr_crc_check).
//
// Description:
//   On cfg_start the block streams cfg_num_beats beats PER CHANNEL for every
//   channel selected in cfg_channel_mask (mask == 0 => all NUM_CHANNELS active),
//   scheduled sequentially (finish one channel, then the next) so each
//   channel's LFSR sequence is contiguous. Each channel N maintains an
//   independent LFSR seeded (seed ^ N) -- IDENTICAL to axi4_slave_rd_pattern_gen
//   -- and its own dataint_crc-32 instance. Each beat:
//     - m_axis_tid   = channel index
//     - m_axis_tdata = {REP{lfsr_out[ch]}}  (32-bit LFSR replicated to fill bus)
//     - the active channel's LFSR + CRC advance on the accepted beat only
//     - tlast asserted every cfg_beats_per_pkt beats (0 => tlast on each
//       channel's final beat only), and always on each channel's final beat.
//   Because the LFSR advances only on accepted beats, beat N of channel C is a
//   deterministic function of (seed ^ C, N), independent of tready stalls.
//
//   The per-channel expected CRC is exported continuously (o_expected_crc[ch],
//   o_expected_crc_valid[ch]) mirroring axi4_slave_rd_pattern_gen's
//   read_crc_value / read_crc_valid semantics -- NOT the old XOR-fold signature.
//
// CRC bit-consistency (copied VERBATIM from the axi4 blocks):
//   - shifter_lfsr_fibonacci #(WIDTH=32, TAP_INDEX_WIDTH=12, TAP_COUNT=4),
//     seed_data = (seed ^ ch), enable = (accepted-beat-for-ch || load),
//     seed_load = load.
//   - dataint_crc #(DATA_WIDTH=32, CRC_WIDTH=32, REFIN=1, REFOUT=1) with
//     POLY=0x04C11DB7, POLY_INIT=0xFFFFFFFF, XOROUT=0xFFFFFFFF,
//     cascade_sel=4'b1000, data=lfsr_out[ch], load_crc_start=load,
//     load_from_cascade=accepted-beat-for-ch.
//
// Notes:
//   - AXIS_DATA_WIDTH must be a multiple of LFSR_WIDTH (tdata = REP x lfsr_out).
//   - No address channel (pure stream): simpler than the AXI4 pattern gen.
//
// Documentation: projects/components/rapids/CONTROL_ENGINE_INTEGRATION.md (harness)
// Subsystem: amba/shared

`timescale 1ns / 1ps

module axis4_master_pattern_gen #(
    parameter int          NUM_CHANNELS     = 1,
    parameter int          AXIS_DATA_WIDTH  = 512,
    parameter int          AXIS_ID_WIDTH    = 8,
    parameter int          AXIS_DEST_WIDTH  = 4,
    parameter int          AXIS_USER_WIDTH  = 1,

    // LFSR parameters (32-bit fixed; MUST MATCH axi4_slave_rd_pattern_gen!)
    parameter int          LFSR_WIDTH       = 32,
    parameter logic [31:0] LFSR_SEED        = 32'hDEADBEEF,
    parameter logic [47:0] LFSR_TAPS        = {12'd32, 12'd22, 12'd2, 12'd1},

    // CRC parameters (fixed; MUST MATCH axi4_slave_rd_pattern_gen /
    // axi4_slave_wr_crc_check!)
    parameter int          CRC_WIDTH        = 32,
    parameter int          CRC_DATA_WIDTH   = 32,   // process 32-bit LFSR output only
    parameter logic [31:0] CRC_POLY         = 32'h04C11DB7,  // CRC-32 Ethernet
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
    input  logic                          cfg_start,          // pulse: begin a run
    input  logic [LFSR_WIDTH-1:0]         cfg_lfsr_seed,      // 0 => use LFSR_SEED param
    input  logic [NUM_CHANNELS-1:0]       cfg_channel_mask,   // active channels (0 => all)
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_num_beats,      // beats to send PER CHANNEL
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_beats_per_pkt,  // tlast cadence (0 => 1 pkt/channel)
    input  logic [AXIS_DEST_WIDTH-1:0]    cfg_tdest,
    output logic                          cfg_busy,
    output logic                          cfg_done,           // 1-cycle pulse at end of run

    // Per-channel expected CRC (mirrors axi4_slave_rd_pattern_gen.read_crc_value)
    output logic [NUM_CHANNELS-1:0][31:0] o_expected_crc,
    output logic [NUM_CHANNELS-1:0]       o_expected_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] o_beat_count,       // per-channel beats emitted
    output logic [31:0]                   o_beat_count_total, // sum across channels

    // AXI-Stream master
    output logic                          m_axis_tvalid,
    input  logic                          m_axis_tready,
    output logic [AXIS_DATA_WIDTH-1:0]    m_axis_tdata,
    output logic [STRB_WIDTH-1:0]         m_axis_tstrb,
    output logic                          m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]      m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]    m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]    m_axis_tuser
);

    localparam int LFSR_TAP_INDEX_WIDTH = 12;
    localparam int LFSR_TAP_COUNT       = 4;

    typedef enum logic [1:0] { IDLE, RUN, DONE } state_t;
    state_t r_state;

    logic [CIW-1:0]              r_ch;               // channel currently streaming
    logic [BEAT_COUNT_WIDTH-1:0] r_beats_remaining;  // beats left for current channel
    logic [BEAT_COUNT_WIDTH-1:0] r_pkt_cnt;          // tlast cadence counter (per channel)
    logic [NUM_CHANNELS-1:0]     r_channel_mask;     // latched active-channel mask
    logic [BEAT_COUNT_WIDTH-1:0] r_num_beats;        // latched beats-per-channel
    logic [BEAT_COUNT_WIDTH-1:0] r_beats_per_pkt;    // latched tlast cadence

    logic                        w_load;
    logic                        w_beat;
    logic                        w_ch_last_beat;
    logic                        w_pkt_last;
    logic [LFSR_WIDTH-1:0]       w_seed;
    logic [LFSR_WIDTH-1:0]       w_active_lfsr;

    logic [31:0] lfsr_out_per_ch [NUM_CHANNELS];
    logic [31:0] crc_out_per_ch  [NUM_CHANNELS];

    assign w_load = (r_state == IDLE) && cfg_start;
    assign w_seed = (cfg_lfsr_seed == '0) ? LFSR_SEED[LFSR_WIDTH-1:0] : cfg_lfsr_seed;
    assign w_beat = m_axis_tvalid && m_axis_tready;

    //==========================================================================
    // Next-active-channel search (sequential per-channel scheduling)
    //==========================================================================
    // Returns {found, idx} for the lowest active (masked) channel index strictly
    // greater than after_idx. after_idx = -1 => first active channel.

    function automatic logic [CIW:0] f_next_active_after(
        input logic [NUM_CHANNELS-1:0] mask,
        input int                      after_idx
    );
        logic           found;
        logic [CIW-1:0] idx;
        found = 1'b0;
        idx   = '0;
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (!found && (i > after_idx) && mask[i]) begin
                found = 1'b1;
                idx   = CIW'(i);
            end
        end
        return {found, idx};
    endfunction

    logic [NUM_CHANNELS-1:0] w_eff_mask;
    assign w_eff_mask = (cfg_channel_mask == '0) ? {NUM_CHANNELS{1'b1}} : cfg_channel_mask;

    logic [CIW:0] w_first_res, w_next_res;
    assign w_first_res = f_next_active_after(w_eff_mask, -1);
    assign w_next_res  = f_next_active_after(r_channel_mask, int'(r_ch));

    logic           w_first_found, w_next_found;
    logic [CIW-1:0] w_first_idx,   w_next_idx;
    assign w_first_found = w_first_res[CIW];
    assign w_first_idx   = w_first_res[CIW-1:0];
    assign w_next_found  = w_next_res[CIW];
    assign w_next_idx    = w_next_res[CIW-1:0];

    //==========================================================================
    // Per-channel LFSR pattern generators + CRC-32 calculators
    //==========================================================================
    // seed/taps/replication/CRC instantiation + gating are copied VERBATIM from
    // axi4_slave_rd_pattern_gen so the per-channel 32-bit CRC is bit-identical.

    genvar gch;
    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_ch
            logic ch_beat;
            logic r_ch_crc_valid;
            logic [31:0] r_ch_beat_count;

            // The active channel advances on its accepted beat; all channels
            // (re)load their seed on the global load pulse.
            assign ch_beat = w_beat && (r_ch == gch[CIW-1:0]);

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

            assign o_expected_crc      [gch] = crc_out_per_ch[gch];
            assign o_expected_crc_valid[gch] = r_ch_crc_valid;
            assign o_beat_count        [gch] = r_ch_beat_count;
        end
    endgenerate

    // Aggregate beat count (sum across channels) for the harness stop trigger.
    always_comb begin
        o_beat_count_total = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            o_beat_count_total = o_beat_count_total + o_beat_count[ch];
        end
    end

    //==========================================================================
    // Stream outputs
    //==========================================================================

    assign w_active_lfsr  = lfsr_out_per_ch[r_ch];
    assign w_ch_last_beat = (r_beats_remaining == {{(BEAT_COUNT_WIDTH-1){1'b0}}, 1'b1});
    assign w_pkt_last     = w_ch_last_beat ||
                            ((r_beats_per_pkt != '0) &&
                             (r_pkt_cnt == r_beats_per_pkt - 1'b1));

    assign m_axis_tvalid = (r_state == RUN);
    assign m_axis_tdata  = {REP{w_active_lfsr}};
    assign m_axis_tstrb  = {STRB_WIDTH{1'b1}};
    assign m_axis_tlast  = w_pkt_last;
    assign m_axis_tid    = AXIS_ID_WIDTH'(r_ch);
    assign m_axis_tdest  = cfg_tdest;
    assign m_axis_tuser  = '0;
    assign cfg_busy      = (r_state != IDLE);

    //==========================================================================
    // Scheduling FSM
    //==========================================================================

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_state           <= IDLE;
            r_ch              <= '0;
            r_beats_remaining <= '0;
            r_pkt_cnt         <= '0;
            r_channel_mask    <= '0;
            r_num_beats       <= '0;
            r_beats_per_pkt   <= '0;
            cfg_done          <= 1'b0;
        end else begin
            cfg_done <= 1'b0;   // default: single-cycle pulse
            case (r_state)
                IDLE: begin
                    if (cfg_start) begin
                        r_channel_mask  <= w_eff_mask;
                        r_num_beats     <= cfg_num_beats;
                        r_beats_per_pkt <= cfg_beats_per_pkt;
                        r_pkt_cnt       <= '0;
                        if ((cfg_num_beats == '0) || !w_first_found) begin
                            r_state <= DONE;
                        end else begin
                            r_ch              <= w_first_idx;
                            r_beats_remaining <= cfg_num_beats;
                            r_state           <= RUN;
                        end
                    end
                end

                RUN: begin
                    if (w_beat) begin
                        r_pkt_cnt <= w_pkt_last ? '0 : (r_pkt_cnt + 1'b1);
                        if (w_ch_last_beat) begin
                            // Finished this channel -> advance to the next active
                            // channel (its LFSR/CRC state is untouched), or finish.
                            if (w_next_found) begin
                                r_ch              <= w_next_idx;
                                r_beats_remaining <= r_num_beats;
                                r_pkt_cnt         <= '0;
                            end else begin
                                r_state <= DONE;
                            end
                        end else begin
                            r_beats_remaining <= r_beats_remaining - 1'b1;
                        end
                    end
                end

                DONE: begin
                    cfg_done <= 1'b1;
                    r_state  <= IDLE;
                end

                default: r_state <= IDLE;
            endcase
        end
    end

endmodule : axis4_master_pattern_gen
