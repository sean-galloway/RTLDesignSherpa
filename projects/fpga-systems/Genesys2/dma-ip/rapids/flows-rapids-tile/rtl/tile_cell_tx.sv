// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: tile_cell_tx
// Purpose: One compute cell as RAPIDS's sink sees it (TILE_SPEC 11.9): tile
//          write packets into one sink channel, sent only against the cell's
//          strap, refilled by RAPIDS's credit returns (rapids TASK-032)
//
// Description:
//   The payload is axis4_master_injector's, one channel, seeded (seed ^ CH),
//   so beat N of the channel and its expected CRC are what the multi-channel
//   injector, and axi4_slave_wr_crc_check behind the sink, use for that
//   channel. In front of every packet the cell puts one header beat
//   (rapids_pkg::tile_hdr_pack: dst = RAPIDS, src = this cell, ptype mem,
//   op write, length in bytes, tag = the channel); the header does not
//   advance the LFSR.
//
//   The strap: a counter that starts at LAND_FLITS. A packet (header + its
//   beats) starts only when the counter covers all of it, and is charged
//   whole at its header. ret_valid adds ret_count back (ret_set replaces the
//   counter: a resync). A return that would take the counter past LAND_FLITS
//   is an over-return: sticky err_over_return, and the counter saturates.
//   A packet larger than the strap can never go: sticky err_pkt_too_big, and
//   the cell stops (it would wait forever).
//
//   Ordering (cfg_ordered; RAPIDS MAS ordering hazard O4): delta may
//   interleave or reorder packets, so the next packet waits until RAPIDS has
//   returned every flit sent, i.e. the strap is whole again. RAPIDS never
//   returns a flit it has not received, so a whole strap proves every earlier
//   packet landed and drained. The packet itself still goes whole, up to the
//   strap. Comparing the strap (not the sent / returned counts) keeps the rule
//   right across a resync set.
//
//   Packets: cfg_beats_per_pkt beats each (0 = the whole run in one), the last
//   one the remainder; cfg_num_beats in all. Every beat is full-strobe.
//
// Parameters:
//   - DW:          data width (the DUT's)
//   - LAND_FLITS:  the cell's strap, header included (RAPIDS TILE_STRAPS)
//   - RAPIDS_COORD: the destination coordinate
//
// Subsystem: fpga-systems/Genesys2/rapids tile harness
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "reset_defs.svh"

module tile_cell_tx #(
    parameter int DW          = 512,
    parameter int LAND_FLITS  = 16,
    parameter int TIDW        = 8,
    parameter int BCW         = 32,
    parameter logic [rapids_pkg::TILE_COORD_W-1:0] RAPIDS_COORD =
        {1'b0, rapids_pkg::TILE_LEVEL_IO, 12'h000},
    parameter int SW          = DW / 8,
    parameter int STW         = $clog2(LAND_FLITS + 1),
    parameter int CRW         = rapids_pkg::TILE_COORD_W
) (
    input  logic              clk,
    input  logic              rst_n,

    // Run control
    input  logic              cfg_start,          // pulse
    input  logic [31:0]       cfg_seed,           // the run seed; this cell uses seed ^ channel
    input  logic [3:0]        cfg_channel,        // the sink channel (the tag)
    input  logic [CRW-1:0]    cfg_coord,          // this cell's coordinate (the source)
    input  logic [BCW-1:0]    cfg_num_beats,
    input  logic [BCW-1:0]    cfg_beats_per_pkt,
    input  logic              cfg_ordered,        // O4: wait for every flit back
    output logic              busy,
    output logic              done,               // pulse

    // Credit returns for this cell (class 0)
    input  logic              ret_valid,
    input  logic              ret_set,
    input  logic [31:0]       ret_count,

    // Packets out
    output logic              m_valid,
    input  logic              m_ready,
    output logic [DW-1:0]     m_data,
    output logic [SW-1:0]     m_strb,
    output logic              m_last,
    output logic [TIDW-1:0]   m_tid,

    // Status
    output logic [31:0]       expected_crc,
    output logic [STW-1:0]    strap_free,
    output logic [31:0]       sent_flits,
    output logic [31:0]       returned_flits,
    output logic [31:0]       sent_pkts,
    output logic              err_over_return,    // sticky
    output logic              err_pkt_too_big     // sticky
);

    // ---- the payload: one channel of axis4_master_injector -------------
    logic          g_valid, g_ready, g_last;
    logic [DW-1:0] g_data;
    logic          g_busy, g_done;
    logic [31:0]   g_crc;

    axis4_master_injector #(
        .NUM_CHANNELS    (1),
        .AXIS_DATA_WIDTH (DW),
        .AXIS_ID_WIDTH   (TIDW),
        .AXIS_DEST_WIDTH (4),
        .AXIS_USER_WIDTH (1),
        .BEAT_COUNT_WIDTH(BCW)
    ) u_gen (
        .clk                  (clk),
        .rst_n                (rst_n),
        .cfg_start            (cfg_start),
        .cfg_lfsr_seed        (cfg_seed ^ 32'(cfg_channel)),
        .cfg_channel_mask     (1'b1),
        .cfg_num_beats        (cfg_num_beats),
        .cfg_beats_per_pkt    (cfg_beats_per_pkt),
        .cfg_interleave       (1'b0),
        .cfg_tdest            (4'h0),
        .cfg_last_bytes       (8'h0),
        .cfg_busy             (g_busy),
        .cfg_done             (g_done),
        .o_expected_crc       (g_crc),
        .o_expected_crc_valid (),
        .o_beat_count         (),
        .o_beat_count_total   (),
        .m_axis_tvalid        (g_valid),
        .m_axis_tready        (g_ready),
        .m_axis_tdata         (g_data),
        .m_axis_tstrb         (),
        .m_axis_tlast         (g_last),
        .m_axis_tid           (),
        .m_axis_tdest         (),
        .m_axis_tuser         ()
    );

    assign expected_crc = g_crc;

    // ---- the next packet's size -----------------------------------------
    logic [BCW-1:0] r_left;          // beats not yet sent in this run
    logic [BCW-1:0] w_pkt_beats;
    assign w_pkt_beats = ((cfg_beats_per_pkt == '0) || (cfg_beats_per_pkt > r_left))
                         ? r_left : cfg_beats_per_pkt;

    logic [BCW:0] w_pkt_flits;       // header included
    assign w_pkt_flits = {1'b0, w_pkt_beats} + 1'b1;

    // ---- header, then the beats -----------------------------------------
    logic r_in_pkt;                  // the header went; beats are passing
    logic w_fits, w_too_big, w_hdr_go, w_order_ok;
    assign w_order_ok = !cfg_ordered || (strap_free == STW'(LAND_FLITS));
    assign w_too_big  = w_pkt_flits > (BCW + 1)'(LAND_FLITS);
    assign w_fits     = !w_too_big && w_order_ok && ((BCW + 1)'(strap_free) >= w_pkt_flits);
    assign w_hdr_go  = !r_in_pkt && g_valid && w_fits && !err_pkt_too_big && m_ready;

    assign m_valid = r_in_pkt ? g_valid : (g_valid && w_fits && !err_pkt_too_big);
    assign m_data  = r_in_pkt ? g_data
                              : DW'(rapids_pkg::tile_hdr_pack(
                                    RAPIDS_COORD, cfg_coord, rapids_pkg::TILE_PTYPE_MEM, 1'b0,
                                    32'(w_pkt_beats) * 32'(SW), '0, cfg_channel));
    assign m_strb  = r_in_pkt ? {SW{1'b1}} : SW'({rapids_pkg::TILE_HDR_BYTES{1'b1}});
    assign m_last  = r_in_pkt && g_last;
    assign m_tid   = TIDW'(cfg_channel);
    assign g_ready = r_in_pkt && m_ready;

    logic w_beat;
    assign w_beat = r_in_pkt && g_valid && m_ready;

    // ---- the strap ---------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_in_pkt        <= 1'b0;
            r_left          <= '0;
            strap_free      <= STW'(LAND_FLITS);
            sent_flits      <= '0;
            returned_flits  <= '0;
            sent_pkts       <= '0;
            err_over_return <= 1'b0;
            err_pkt_too_big <= 1'b0;
        end else begin
            logic [STW+31:0] n;
            if (cfg_start) begin
                r_left     <= cfg_num_beats;
                sent_flits <= '0;
                returned_flits <= '0;
                sent_pkts  <= '0;
            end else if (w_beat) begin
                r_left <= r_left - 1'b1;
            end

            if (w_hdr_go) r_in_pkt <= 1'b1;
            else if (w_beat && g_last) r_in_pkt <= 1'b0;

            if (!r_in_pkt && g_valid && w_too_big) err_pkt_too_big <= 1'b1;

            // Charge at the header; a return lands the same cycle
            n = {{32{1'b0}}, strap_free};
            if (w_hdr_go) n = n - (STW + 32)'(w_pkt_flits);
            if (ret_valid) begin
                n = ret_set ? (STW + 32)'(ret_count) : n + (STW + 32)'(ret_count);
                if (!ret_set) returned_flits <= returned_flits + ret_count;
            end
            if (n > (STW + 32)'(LAND_FLITS)) begin
                err_over_return <= 1'b1;
                n = (STW + 32)'(LAND_FLITS);
            end
            strap_free <= STW'(n);

            if (w_hdr_go) begin
                sent_flits <= sent_flits + 32'(w_pkt_flits);
                sent_pkts  <= sent_pkts + 1'b1;
            end
        end
    )

    assign busy = g_busy || r_in_pkt;
    assign done = g_done;

endmodule : tile_cell_tx
