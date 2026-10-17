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
//     credit                            consumed and counted (end-to-end
//                                       credits, TILE_SPEC 11.9, are not built
//                                       yet); the sink port accepts them
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

    // Cell-issued descriptor to the source half (registered pulse)
    output logic                        desc_inj_valid,
    output logic [CIW-1:0]              desc_inj_ch,
    output logic [255:0]                desc_inj_data,

    // Status
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

    assign w_s      = s_axis_tid[CIW-1:0];
    assign w_s_ok   = (int'(w_s) < NC) && (s_axis_tid >> CIW == '0);
    assign w_is_hdr = !w_s_ok || !r_in_pkt[w_s];
    assign w_ptype  = s_axis_tdata[rapids_pkg::TILE_HDR_PTYPE_LO +: 3];
    assign w_op     = s_axis_tdata[rapids_pkg::TILE_HDR_OP];
    assign w_tag    = s_axis_tdata[rapids_pkg::TILE_HDR_TAG_LO +: 4];
    assign w_tag_ok = (int'(w_tag) < NC);

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
                    if (!w_op) w_hdr_route = R_DATA;
                    else       w_hdr_unsup = 1'b1;          // read request to RAPIDS
                end
                rapids_pkg::TILE_PTYPE_CREDIT: begin
                    w_hdr_route = R_DROP;                   // counted, not yet acted on
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
            for (int i = 0; i < NC; i++) begin
                r_route[i] <= R_DROP;
                r_tag[i]   <= '0;
            end
        end else if (w_fire && w_s_ok) begin
            if (w_is_hdr) begin
                // a header-only packet (tlast on the header) leaves the
                // stream expecting the next header
                r_in_pkt[w_s]   <= !s_axis_tlast;
                r_route[w_s]    <= w_hdr_route;
                r_tag[w_s]      <= CIW'(w_tag);
                r_desc_got[w_s] <= 1'b0;
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
        end else begin
            desc_inj_valid <= w_desc_take;
            if (w_desc_take) begin
                desc_inj_ch   <= r_tag[w_s];
                desc_inj_data <= w_beat_lo;
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
            if (w_fire && w_is_hdr && w_hdr_unsup) sts_unsupported <= 1'b1;
            if (w_desc_extra)                       sts_unsupported <= 1'b1;
            if (w_fire && w_is_hdr && w_s_ok && (w_hdr_route == R_DATA) && (w_tag != 4'(w_s)))
                sts_tag_mismatch <= 1'b1;
            if (w_desc_take)                        sts_desc_count <= sts_desc_count + 16'd1;
            if (w_fire && w_is_hdr && w_s_ok && (w_ptype == rapids_pkg::TILE_PTYPE_CREDIT))
                sts_credit_count <= sts_credit_count + 16'd1;
        end
    )

endmodule : rapids_tile_hdr_rx
