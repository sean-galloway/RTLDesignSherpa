// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_cxs_pattern_pair
// Purpose: The CXS sibling of tb_axis4_pattern_pair: cxs_master_injector's
//          m_cxs_* link wired straight into cxs_slave_pattern_check's s_cxs_*,
//          so the same per-channel CRC agreement is proven across a credited
//          CXS link. Same control/observation ports as the AXIS pair (one TB
//          class drives both), plus the link wires for a wire monitor and the
//          endpoints' sticky status.

`timescale 1ns / 1ps

module tb_cxs_pattern_pair #(
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
    input  logic                          cfg_interleave,     // 1: round-robin channels per beat
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
    output logic [BEAT_COUNT_WIDTH-1:0]   o_pkt_count,

    // Stream order probe: the TB reconstructs the channel schedule from it
    // (a flit on the CXS link; CXSSRCID carries the channel)
    output logic                          o_axis_hs,
    output logic [AXIS_ID_WIDTH-1:0]      o_axis_tid,

    // Link status
    output logic [1:0]                    tx_link_state,
    output logic [1:0]                    rx_link_state,
    output logic                          tx_protocol_error,
    output logic                          rx_protocol_error,
    output logic                          rx_unsupported
);

    localparam int STRB_WIDTH = AXIS_DATA_WIDTH / 8;
    localparam bit CARRY_TUSER = (STRB_WIDTH + AXIS_USER_WIDTH) <= 128;
    localparam int CXS_UW      = STRB_WIDTH + (CARRY_TUSER ? AXIS_USER_WIDTH : 0);
    localparam int CNTL_PW     = cxs_pkg::port_w(cxs_pkg::cntl_width(2, AXIS_DATA_WIDTH, 16));

    // The CXS link (the names a wire monitor binds to: cxs_*)
    logic                          cxs_valid;
    logic [AXIS_DATA_WIDTH-1:0]    cxs_data;
    logic [CNTL_PW-1:0]            cxs_cntl;
    logic [AXIS_ID_WIDTH-1:0]      cxs_srcid;
    logic [AXIS_DEST_WIDTH-1:0]    cxs_tgtid;
    logic [CXS_UW-1:0]             cxs_user;
    logic                          cxs_crdgnt, cxs_crdrtn;
    logic                          cxs_activereq, cxs_activeack, cxs_deacthint;

    // Backpressure is applied at the CONSUMER: the checker's ready_en stops
    // the receive FIFO draining, so the link stops granting credits.
    logic                          w_ready_en;
    assign w_ready_en = !chk_backpressure;
    assign o_axis_hs  = cxs_valid;
    assign o_axis_tid = cxs_srcid;

    cxs_master_injector #(
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
        .cfg_interleave      (cfg_interleave),
        .cfg_tdest           (cfg_tdest),
        .cfg_last_bytes      (8'd0),              // beat-granular packets
        .cfg_busy            (gen_busy),
        .cfg_done            (gen_done),
        .o_expected_crc      (gen_expected_crc),
        .o_expected_crc_valid(gen_expected_crc_valid),
        .o_beat_count        (gen_beat_count),
        .o_beat_count_total  (gen_beat_count_total),
        .m_cxs_valid         (cxs_valid),
        .m_cxs_data          (cxs_data),
        .m_cxs_cntl          (cxs_cntl),
        .m_cxs_srcid         (cxs_srcid),
        .m_cxs_tgtid         (cxs_tgtid),
        .m_cxs_user          (cxs_user),
        .m_cxs_crdgnt        (cxs_crdgnt),
        .m_cxs_crdrtn        (cxs_crdrtn),
        .m_cxs_activereq     (cxs_activereq),
        .m_cxs_activeack     (cxs_activeack),
        .m_cxs_deacthint     (cxs_deacthint),
        .link_state          (tx_link_state),
        .protocol_error      (tx_protocol_error)
    );

    cxs_slave_pattern_check #(
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
        .s_cxs_valid        (cxs_valid),
        .s_cxs_data         (cxs_data),
        .s_cxs_cntl         (cxs_cntl),
        .s_cxs_srcid        (cxs_srcid),
        .s_cxs_tgtid        (cxs_tgtid),
        .s_cxs_user         (cxs_user),
        .s_cxs_crdgnt       (cxs_crdgnt),
        .s_cxs_crdrtn       (cxs_crdrtn),
        .s_cxs_activereq    (cxs_activereq),
        .s_cxs_activeack    (cxs_activeack),
        .s_cxs_deacthint    (cxs_deacthint),
        .link_state         (rx_link_state),
        .protocol_error     (rx_protocol_error),
        .unsupported        (rx_unsupported)
    );

endmodule : tb_cxs_pattern_pair
