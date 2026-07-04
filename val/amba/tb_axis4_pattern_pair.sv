// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Module: tb_axis4_pattern_pair
// Purpose: Pair the MULTI-CHANNEL axis4_master_pattern_gen -> axis4_slave_
//          pattern_check (m_axis driven straight into s_axis) so a cocotb test
//          can arm both, stream several beats across multiple tids, and verify
//          PER-CHANNEL: no data error, matching per-channel beat counts, and
//          gen.o_expected_crc[ch] == chk.o_actual_crc[ch] for every active
//          channel -- proving gen + checker agree under the shared dataint_crc
//          scheme. AXIS analog of tb_axi4_master_pat_crc_pair.

`timescale 1ns / 1ps

module tb_axis4_pattern_pair #(
    parameter int          NUM_CHANNELS     = 4,
    parameter int          AXIS_DATA_WIDTH  = 512,
    parameter int          AXIS_ID_WIDTH    = 8,
    parameter int          AXIS_DEST_WIDTH  = 4,
    parameter int          AXIS_USER_WIDTH  = 1,
    parameter int          LFSR_WIDTH       = 32,
    parameter int          BEAT_COUNT_WIDTH = 32
) (
    input  logic                          clk,
    input  logic                          rst_n,

    // Control (drive both engines)
    input  logic                          cfg_start_chk,      // arm checker first
    input  logic                          cfg_start_gen,      // then start generator
    input  logic [LFSR_WIDTH-1:0]         cfg_lfsr_seed,
    input  logic [NUM_CHANNELS-1:0]       cfg_channel_mask,   // active channels (0 => all)
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_num_beats,      // beats PER CHANNEL
    input  logic [BEAT_COUNT_WIDTH-1:0]   cfg_beats_per_pkt,
    input  logic [AXIS_DEST_WIDTH-1:0]    cfg_tdest,
    input  logic                          chk_backpressure,   // gate checker tready

    // Observation
    output logic                          gen_busy,
    output logic                          gen_done,
    output logic [NUM_CHANNELS-1:0][31:0] gen_expected_crc,
    output logic [NUM_CHANNELS-1:0]       gen_expected_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] gen_beat_count,
    output logic [31:0]                   gen_beat_count_total,
    output logic [NUM_CHANNELS-1:0][31:0] chk_actual_crc,
    output logic [NUM_CHANNELS-1:0]       chk_actual_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] chk_beat_count,
    output logic [31:0]                   chk_beat_count_total,
    output logic                          o_data_error,
    output logic [BEAT_COUNT_WIDTH-1:0]   o_pkt_count
);

    localparam int STRB_WIDTH = AXIS_DATA_WIDTH / 8;

    // Generator -> checker stream (single shared handshake)
    logic                          axis_tvalid;
    logic                          axis_tready;      // driven by checker (ready_en)
    logic [AXIS_DATA_WIDTH-1:0]    axis_tdata;
    logic [STRB_WIDTH-1:0]         axis_tstrb;
    logic                          axis_tlast;
    logic [AXIS_ID_WIDTH-1:0]      axis_tid;
    logic [AXIS_DEST_WIDTH-1:0]    axis_tdest;
    logic [AXIS_USER_WIDTH-1:0]    axis_tuser;

    // Backpressure is applied at the CONSUMER: the checker deasserts tready via
    // ready_en, and the generator sees that same tready -> lockstep, no desync.
    logic                          w_ready_en;
    assign w_ready_en = !chk_backpressure;

    axis4_master_pattern_gen #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH),
        .LFSR_WIDTH      (LFSR_WIDTH),
        .BEAT_COUNT_WIDTH(BEAT_COUNT_WIDTH)
    ) u_gen (
        .clk                 (clk),
        .rst_n               (rst_n),
        .cfg_start           (cfg_start_gen),
        .cfg_lfsr_seed       (cfg_lfsr_seed),
        .cfg_channel_mask    (cfg_channel_mask),
        .cfg_num_beats       (cfg_num_beats),
        .cfg_beats_per_pkt   (cfg_beats_per_pkt),
        .cfg_tdest           (cfg_tdest),
        .cfg_busy            (gen_busy),
        .cfg_done            (gen_done),
        .o_expected_crc      (gen_expected_crc),
        .o_expected_crc_valid(gen_expected_crc_valid),
        .o_beat_count        (gen_beat_count),
        .o_beat_count_total  (gen_beat_count_total),
        .m_axis_tvalid       (axis_tvalid),
        .m_axis_tready       (axis_tready),
        .m_axis_tdata        (axis_tdata),
        .m_axis_tstrb        (axis_tstrb),
        .m_axis_tlast        (axis_tlast),
        .m_axis_tid          (axis_tid),
        .m_axis_tdest        (axis_tdest),
        .m_axis_tuser        (axis_tuser)
    );

    axis4_slave_pattern_check #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (AXIS_DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH),
        .LFSR_WIDTH      (LFSR_WIDTH),
        .BEAT_COUNT_WIDTH(BEAT_COUNT_WIDTH)
    ) u_chk (
        .clk                (clk),
        .rst_n              (rst_n),
        .cfg_start          (cfg_start_chk),
        .cfg_lfsr_seed      (cfg_lfsr_seed),
        .ready_en           (w_ready_en),
        .o_actual_crc       (chk_actual_crc),
        .o_actual_crc_valid (chk_actual_crc_valid),
        .o_data_error       (o_data_error),
        .o_beat_count       (chk_beat_count),
        .o_beat_count_total (chk_beat_count_total),
        .o_pkt_count        (o_pkt_count),
        .s_axis_tvalid      (axis_tvalid),
        .s_axis_tready      (axis_tready),
        .s_axis_tdata       (axis_tdata),
        .s_axis_tstrb       (axis_tstrb),
        .s_axis_tlast       (axis_tlast),
        .s_axis_tid         (axis_tid),
        .s_axis_tdest       (axis_tdest),
        .s_axis_tuser       (axis_tuser)
    );

endmodule : tb_axis4_pattern_pair
