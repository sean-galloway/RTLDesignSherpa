// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_hdr_rx
// Purpose: Sink-port tile header decode (TILE_SPEC 11.5 / 11.11)
//
// Description:
//   Sits between the sink network plane and snk_data_path_axis when the core
//   is built with TILE_HDR = 1. Every packet on the sink port starts with one
//   header beat (bits [127:0], rapids_pkg tile_hdr_pack layout). Packets are
//   framed per stream, and a stream is a TID (= the channel, CXSSRCID on a
//   CXS plane), so the "next beat is a header" state is kept per stream.
//
//   By payload type and op of the header:
//     cfg / prog / mem, op = 0 (write)  header dropped; the payload beats go to
//                                       the sink data path unchanged (same TID)
//     desc, op = 0                      the first payload beat's [255:0] is a
//                                       source descriptor for the channel the
//                                       tag names: a desc_inj_* pulse into the
//                                       source half; never stored in the sink
//     credit                            consumed and counted; {source
//                                       coordinate, op, count, class} goes to
//                                       the source half's credit counters as a
//                                       credit_* pulse (TILE_SPEC 11.9, 11.10).
//                                       The sink port accepts them
//                                       unconditionally
//     anything else                     consumed, sticky sts_unsupported:
//                                       a read request to RAPIDS (op = 1), a
//                                       reserved ptype, a desc packet with no
//                                       payload or a tag past NUM_CHANNELS,
//                                       extra desc payload beats, or a desc
//                                       packet when DATA_WIDTH < 256
//
//   Only data payload ever waits on the sink data path (tready); header,
//   desc, credit and dropped beats are taken at once, so a full sink channel
//   never holds a descriptor or a credit behind it.
//
//   A data packet whose tag differs from its TID is still delivered by TID
//   (the channel the link names); sts_tag_mismatch records it.
//
//   Straps (STRAPS = 1, TILE_CREDITS; TILE_SPEC 11.9, rapids TASK-027): every
//   packet a cell or core sends is charged against a strap, and every beat
//   RAPIDS consumes must come back as a credit. The sender is the header's
//   source coordinate, as an external slot (rapids_pkg::tile_ext_slot). Data
//   payload goes on with its sender's cell slot (m_axis_tsender) to the
//   landing space, which returns it as it drains. What this block consumes
//   itself returns here, one ret_* pulse per credit:
//     class 0 (flits)   the header beat of every data packet, and every beat
//                       of a dropped packet, from a cell
//     class 1 (entries) a desc packet that is dropped at its header; one whose
//                       descriptor is taken returns when it leaves the intake
//                       queue (desc_inj_slot carries the sender)
//   Credit packets are never charged and return nothing. Data from a sender
//   with no landing space (not a cell) is dropped and sets sts_unsupported.
//   seen_* gives the coordinate of every sender with a slot, for addressing
//   the returns.
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_tile_hdr_rx #(
    parameter int NUM_CHANNELS    = 8,
    parameter int DATA_WIDTH      = 512,
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,
    parameter bit STRAPS          = 1'b0,
    parameter int NC  = NUM_CHANNELS,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW / 8,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // From the sink plane: every packet starts with its header beat
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    // To the sink data path: data packets' payload, headers removed
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,
    output logic [rapids_pkg::TILE_EXT_W-2:0] m_axis_tsender, // STRAPS: the sender's cell slot

    // Cell-issued descriptor to the source half (registered pulse)
    output logic                        desc_inj_valid,
    output logic [CIW-1:0]              desc_inj_ch,
    output logic [255:0]                desc_inj_data,
    output logic [rapids_pkg::TILE_EXT_W:0] desc_inj_slot,   // STRAPS: {ok, the sender's slot}

    // Straps (STRAPS): one credit to return to a sender (registered pulse),
    // and the coordinate of a sender that has a slot
    output logic                        ret_valid,
    output logic [rapids_pkg::TILE_EXT_W-1:0] ret_slot,
    output logic                        ret_class,          // 0 = flit, 1 = descriptor entry
    output logic                        seen_valid,
    output logic [rapids_pkg::TILE_EXT_W-1:0] seen_slot,
    output logic [rapids_pkg::TILE_COORD_W-1:0] seen_coord,

    // Credit packet to the source half's counters (registered pulse): the
    // sender's coordinate, op (0 = add, 1 = set), the count from the length
    // field and the class from target address bits [1:0]
    output logic                        credit_valid,
    output logic [rapids_pkg::TILE_COORD_W-1:0] credit_src,
    output logic                        credit_op,
    output logic [31:0]                 credit_count,
    output logic [1:0]                  credit_class,

    // Status. The two stickies clear on a one-cycle clr_* pulse (the CSR's
    // write-1-to-clear); an event in the same cycle wins.
    input  logic                        clr_unsupported,
    input  logic                        clr_tag_mismatch,
    output logic                        sts_unsupported,     // sticky
    output logic                        sts_tag_mismatch,    // sticky
    output logic [15:0]                 sts_desc_count,      // desc packets passed to the source half
    output logic [15:0]                 sts_credit_count     // credit packets received (consumed)
);

    initial begin
        if (DW < 128)
            $fatal(1, "rapids_tile_hdr_rx needs DATA_WIDTH >= 128 (the header is one 128-bit beat)");
        if (NC > 16)
            $fatal(1, "the tile header tag is 4 bits: NUM_CHANNELS <= 16");
    end

    localparam bit DESC_OK = (DW >= 256);   // a descriptor fits one payload beat

    typedef enum logic [1:0] {
        R_DATA = 2'd0,   // payload to the sink data path
        R_DESC = 2'd1,   // payload is a descriptor for the source half
        R_DROP = 2'd2    // consume and discard
    } route_t;

    // Per-stream state
    logic [NC-1:0]  r_in_pkt;      // 1: past the header of this stream's packet
    route_t         r_route  [NC];
    logic [CIW-1:0] r_tag    [NC]; // desc: the source channel
    logic [NC-1:0]  r_desc_got;    // desc: descriptor already taken from this packet
    logic [rapids_pkg::TILE_EXT_W-1:0] r_slot [NC];   // STRAPS: the sender's slot
    logic [NC-1:0]  r_chg;         // STRAPS: this packet's beats are charged in flits
    logic [NC-1:0]  r_desc_slot_ok; // STRAPS: a desc packet's sender has a slot

    // The current beat
    logic [CIW-1:0] w_s;
    logic           w_s_ok;        // TID names a real stream
    logic           w_is_hdr;
    logic [2:0]     w_ptype;
    logic           w_op;
    logic [3:0]     w_tag;
    logic           w_tag_ok;      // tag names a real channel
    route_t         w_hdr_route;
    logic           w_hdr_unsup;
    logic           w_fire;
    logic           w_fwd;         // a data payload beat, handed to the sink
    logic [rapids_pkg::TILE_EXT_W:0] w_hdr_slot;   // {ok, slot} of the header's source
    logic           w_hdr_cell;    // ...and it is a cell (has a landing space)
    logic           w_hdr_chg;     // the header's packet is charged in flits

    assign w_s      = s_axis_tid[CIW-1:0];
    assign w_s_ok   = (int'(w_s) < NC) && (s_axis_tid >> CIW == '0);
    assign w_is_hdr = !w_s_ok || !r_in_pkt[w_s];
    assign w_ptype  = s_axis_tdata[rapids_pkg::TILE_HDR_PTYPE_LO +: 3];
    assign w_op     = s_axis_tdata[rapids_pkg::TILE_HDR_OP];
    assign w_tag    = s_axis_tdata[rapids_pkg::TILE_HDR_TAG_LO +: 4];
    assign w_tag_ok = (int'(w_tag) < NC);
    assign w_hdr_slot = rapids_pkg::tile_ext_slot(s_axis_tdata[rapids_pkg::TILE_HDR_SRC_LO +: rapids_pkg::TILE_COORD_W]);
    assign w_hdr_cell = w_hdr_slot[rapids_pkg::TILE_EXT_W] &&
                        (w_hdr_slot[rapids_pkg::TILE_EXT_W-1:0] < rapids_pkg::TILE_EXT_W'(rapids_pkg::TILE_NUM_CELLS));
    // only a cell holds a flit strap (a landing space); a core's is entries
    assign w_hdr_chg  = STRAPS && w_hdr_cell &&
                        (w_ptype != rapids_pkg::TILE_PTYPE_CREDIT) && (w_ptype != rapids_pkg::TILE_PTYPE_DESC);

    // Route decided by a header beat
    always_comb begin
        w_hdr_route = R_DROP;
        w_hdr_unsup = 1'b0;
        if (!w_s_ok) begin
            w_hdr_unsup = 1'b1;
        end else begin
            case (w_ptype)
                rapids_pkg::TILE_PTYPE_CFG,
                rapids_pkg::TILE_PTYPE_PROG,
                rapids_pkg::TILE_PTYPE_MEM: begin
                    if (w_op)                          w_hdr_unsup = 1'b1;  // read request to RAPIDS
                    else if (STRAPS && !w_hdr_cell)    w_hdr_unsup = 1'b1;  // no landing space for it
                    else                               w_hdr_route = R_DATA;
                end
                rapids_pkg::TILE_PTYPE_CREDIT: begin
                    w_hdr_route = R_DROP;                   // header-only: to the counters
                end
                rapids_pkg::TILE_PTYPE_DESC: begin
                    if (!w_op && w_tag_ok && DESC_OK && !s_axis_tlast) w_hdr_route = R_DESC;
                    else                                               w_hdr_unsup = 1'b1;
                end
                default: w_hdr_unsup = 1'b1;
            endcase
        end
    end

    assign w_fwd         = s_axis_tvalid && !w_is_hdr && (r_route[w_s] == R_DATA);
    assign s_axis_tready = w_fwd ? m_axis_tready : 1'b1;
    assign w_fire        = s_axis_tvalid && s_axis_tready;

    assign m_axis_tvalid = w_fwd;
    assign m_axis_tdata  = s_axis_tdata;
    assign m_axis_tstrb  = s_axis_tstrb;
    assign m_axis_tlast  = s_axis_tlast;
    assign m_axis_tid    = s_axis_tid;
    assign m_axis_tdest  = s_axis_tdest;
    assign m_axis_tuser  = s_axis_tuser;
    assign m_axis_tsender = r_slot[w_s][rapids_pkg::TILE_EXT_W-2:0];

    // Payload beat of a desc packet. The descriptor is the beat's low 256
    // bits (a desc route is only taken when DW >= 256; the cast keeps a
    // narrower build elaborating).
    logic [255:0] w_beat_lo;
    assign w_beat_lo = 256'(s_axis_tdata);

    logic w_desc_beat, w_desc_take, w_desc_extra;
    assign w_desc_beat  = w_fire && !w_is_hdr && (r_route[w_s] == R_DESC);
    assign w_desc_take  = w_desc_beat && !r_desc_got[w_s];
    assign w_desc_extra = w_desc_beat &&  r_desc_got[w_s];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_in_pkt   <= '0;
            r_desc_got <= '0;
            r_chg      <= '0;
            for (int i = 0; i < NC; i++) begin
                r_route[i] <= R_DROP;
                r_tag[i]   <= '0;
                r_slot[i]  <= '0;
            end
        end else if (w_fire && w_s_ok) begin
            if (w_is_hdr) begin
                // a header-only packet (tlast on the header) leaves the
                // stream expecting the next header
                r_in_pkt[w_s]   <= !s_axis_tlast;
                r_route[w_s]    <= w_hdr_route;
                r_tag[w_s]      <= CIW'(w_tag);
                r_desc_got[w_s] <= 1'b0;
                r_slot[w_s]     <= w_hdr_slot[rapids_pkg::TILE_EXT_W-1:0];
                r_chg[w_s]      <= w_hdr_chg;
            end else begin
                if (w_desc_take)  r_desc_got[w_s] <= 1'b1;
                if (s_axis_tlast) r_in_pkt[w_s]   <= 1'b0;
            end
        end
    )

    // Injection pulse, registered
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            desc_inj_valid <= 1'b0;
            desc_inj_ch    <= '0;
            desc_inj_data  <= '0;
            desc_inj_slot  <= '0;
        end else begin
            desc_inj_valid <= w_desc_take;
            if (w_desc_take) begin
                desc_inj_ch   <= r_tag[w_s];
                desc_inj_data <= w_beat_lo;
                desc_inj_slot <= {r_desc_slot_ok[w_s], r_slot[w_s]};
            end
        end
    )

    // Straps: which consumed beat returns a credit. A desc packet's sender is
    // kept per stream so the intake queue can return its entry.
    logic          w_ret_flit, w_ret_entry;
    // the header beat of a charged packet, or a dropped payload beat of one
    assign w_ret_flit  = w_fire && w_s_ok &&
                         (w_is_hdr ? w_hdr_chg : (r_chg[w_s] && (r_route[w_s] != R_DATA)));
    // a desc packet from a sender with a slot, refused at its header
    assign w_ret_entry = STRAPS && w_fire && w_s_ok && w_is_hdr && w_hdr_slot[rapids_pkg::TILE_EXT_W] &&
                         (w_ptype == rapids_pkg::TILE_PTYPE_DESC) && (w_hdr_route != R_DESC);
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_desc_slot_ok <= '0;
            ret_valid      <= 1'b0;
            ret_slot       <= '0;
            ret_class      <= 1'b0;
            seen_valid     <= 1'b0;
            seen_slot      <= '0;
            seen_coord     <= '0;
        end else begin
            if (w_fire && w_s_ok && w_is_hdr)
                r_desc_slot_ok[w_s] <= STRAPS && w_hdr_slot[rapids_pkg::TILE_EXT_W];
            ret_valid  <= w_ret_flit || w_ret_entry;
            ret_slot   <= w_is_hdr ? w_hdr_slot[rapids_pkg::TILE_EXT_W-1:0] : r_slot[w_s];
            ret_class  <= w_ret_entry;
            seen_valid <= STRAPS && w_fire && w_s_ok && w_is_hdr && w_hdr_slot[rapids_pkg::TILE_EXT_W];
            seen_slot  <= w_hdr_slot[rapids_pkg::TILE_EXT_W-1:0];
            seen_coord <= s_axis_tdata[rapids_pkg::TILE_HDR_SRC_LO +: rapids_pkg::TILE_COORD_W];
        end
    )

    // Credit pulse, registered. A credit packet is header-only; its header
    // beat is all the counters need.
    logic w_credit_take;
    assign w_credit_take = w_fire && w_is_hdr && w_s_ok && (w_ptype == rapids_pkg::TILE_PTYPE_CREDIT);
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            credit_valid <= 1'b0;
            credit_src   <= '0;
            credit_op    <= 1'b0;
            credit_count <= '0;
            credit_class <= '0;
        end else begin
            credit_valid <= w_credit_take;
            if (w_credit_take) begin
                credit_src   <= s_axis_tdata[rapids_pkg::TILE_HDR_SRC_LO +: rapids_pkg::TILE_COORD_W];
                credit_op    <= w_op;
                credit_count <= s_axis_tdata[rapids_pkg::TILE_HDR_LEN_LO +: 32];
                credit_class <= s_axis_tdata[rapids_pkg::TILE_HDR_TGT_LO +: 2];
            end
        end
    )

    // Status
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            sts_unsupported  <= 1'b0;
            sts_tag_mismatch <= 1'b0;
            sts_desc_count   <= '0;
            sts_credit_count <= '0;
        end else begin
            if ((w_fire && w_is_hdr && w_hdr_unsup) || w_desc_extra) sts_unsupported <= 1'b1;
            else if (clr_unsupported)                               sts_unsupported <= 1'b0;
            if (w_fire && w_is_hdr && w_s_ok && (w_hdr_route == R_DATA) && (w_tag != 4'(w_s)))
                sts_tag_mismatch <= 1'b1;
            else if (clr_tag_mismatch)
                sts_tag_mismatch <= 1'b0;
            if (w_desc_take)                        sts_desc_count <= sts_desc_count + 16'd1;
            if (w_credit_take)                      sts_credit_count <= sts_credit_count + 16'd1;
        end
    )

endmodule : rapids_tile_hdr_rx
