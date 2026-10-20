// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_rx
// Purpose: Header parse / demux for the delta node's local port
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
//                projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md §11
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18
//
// NOTE: The tile packet header format is defined in TILE_SPEC §11.5.  Because
//       the instantiated delta node currently uses a 64-bit TUSER, slice 1
//       compacts the fields the cell consumes into the low 64 bits of TUSER:
//         [11:0]    dst {X[3:0], Y[3:0], Z[3:0]}   COORD_W=4
//         [13:12]   qos (must be 2'b01 for cell traffic so delta does not
//                   consume it as its own config class)
//         [14]      dst ext bit (unused by cell match in slice 1)
//         [29:15]   src_coord {ext, level, X, Y, Z}
//         [32:30]   ptype       0=cfg, 1=prog, 2=mem, 3=credit, ...
//         [33]      op          write/read or credit add/set
//         [49:34]   length      compacted to 16 bits
//         [59:50]   target_addr compacted to 10 bits (register offset or line idx)
//         [63:60]   tag         RAPIDS channel, echoed on replies
//       This packing is provisional and will be revisited when delta's head-flit
//       TUSER width grows or CXS transport lands.
//
// NOTE: Slice-1 stores one LINE_W line per 64-bit payload beat (low LINE_W
//       bits).  The eventual packing of two lines per flit lands in slice 3.
//
// NOTE: cfg read replies (ptype=cfg, op=1) are stubbed: they increment a
//       counted TODO drop and are documented for slice 2/3 completion.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cell_rx #(
    parameter int LINE_W   = 32,
    parameter int COORD_W  = 4,
    parameter int IN_DEPTH = 32,
    parameter int POS_X    = 0,
    parameter int POS_Y    = 0,
    parameter int POS_Z    = 0
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Local-port AXI4-Stream from delta_mesh_cell
    input  logic              s_valid,
    output logic              s_ready,
    input  logic [63:0]       s_data,
    input  logic              s_last,
    input  logic [63:0]       s_user,

    // Input-memory write port
    output logic              mem_wr_valid,
    input  logic              mem_wr_ready,
    output logic [$clog2(IN_DEPTH)-1:0] mem_wr_addr,
    output logic [LINE_W-1:0]           mem_wr_data,
    output logic [cell_pkg::COORD_BITS-1:0] mem_wr_src_coord,

    // Config-register write port
    output logic              cfg_wr_valid,
    input  logic              cfg_wr_ready,
    output logic [7:0]        cfg_wr_addr,
    output logic [31:0]       cfg_wr_data,

    // Config-register read port (slice-1 stub)
    output logic              cfg_rd_valid,
    output logic [7:0]        cfg_rd_addr,

    // Counter / error pulses to register file
    output logic              inc_lines_in,
    output logic              inc_err_drop,

    // Observability
    output logic [31:0]       o_todo_credit_drop_cnt,
    output logic [31:0]       o_todo_cfg_read_drop_cnt
);

    import cell_pkg::*;

    localparam int ADDR_W = $clog2(IN_DEPTH);
    localparam int COORD_BITS_LP = COORD_BITS;

    // -------------------------------------------------------------------------
    // Header parsing (combinational on the current beat)
    // -------------------------------------------------------------------------
    logic [COORD_W-1:0]       hdr_dst_x, hdr_dst_y, hdr_dst_z;
    logic [1:0]               hdr_qos;
    logic [COORD_BITS_LP-1:0] hdr_src_coord;
    logic [PTYPE_W-1:0]       hdr_ptype;
    logic                     hdr_op;
    logic [LENGTH_W-1:0]      hdr_length;
    logic [TARGET_ADDR_W-1:0] hdr_target;
    logic [TAG_W-1:0]         hdr_tag;

    assign hdr_dst_x     = s_user[HDR_DST_XYZ_LO +: COORD_W];
    assign hdr_dst_y     = s_user[HDR_DST_XYZ_LO + COORD_W +: COORD_W];
    assign hdr_dst_z     = s_user[HDR_DST_XYZ_LO + 2*COORD_W +: COORD_W];
    assign hdr_qos       = s_user[HDR_QOS_LO +: 2];
    assign hdr_src_coord = s_user[HDR_SRC_LO +: COORD_BITS_LP];
    assign hdr_ptype     = s_user[HDR_PTYPE_LO +: PTYPE_W];
    assign hdr_op        = s_user[HDR_OP_LO];
    assign hdr_length    = s_user[HDR_LENGTH_LO +: LENGTH_W];
    assign hdr_target    = s_user[HDR_TARGET_LO +: TARGET_ADDR_W];
    assign hdr_tag       = s_user[HDR_TAG_LO +: TAG_W];

    // -------------------------------------------------------------------------
    // Coordinate match: cell is level=0 at this X/Y/Z.  The ext bit and qos are
    // not part of the match; qos must be non-zero so delta did not consume the
    // packet as its own config traffic.
    // -------------------------------------------------------------------------
    logic coord_match;

    assign coord_match = (int'(hdr_dst_x) == POS_X) &&
                         (int'(hdr_dst_y) == POS_Y) &&
                         (int'(hdr_dst_z) == POS_Z);

    // -------------------------------------------------------------------------
    // Packet tracking
    // -------------------------------------------------------------------------
    logic in_pkt;
    logic [COORD_BITS_LP-1:0] pkt_src_coord;
    logic [PTYPE_W-1:0]       pkt_ptype;
    logic [TARGET_ADDR_W-1:0] pkt_target;
    logic [ADDR_W-1:0]        mem_wr_ptr;  // running line index inside packet

    // -------------------------------------------------------------------------
    // Transfer and drop controls
    // -------------------------------------------------------------------------
    logic accept_head;
    logic drop_head;
    logic todo_credit_drop;
    logic todo_cfg_read_drop;
    logic accept_mem_payload;
    logic accept_cfg_write;

    assign accept_head = s_valid && s_ready && !in_pkt;
    assign accept_mem_payload = in_pkt && (pkt_ptype == PTYPE_MEM) &&
                                s_valid && s_ready && mem_wr_ready;
    assign accept_cfg_write = !in_pkt && s_valid && s_ready &&
                              coord_match && (hdr_ptype == PTYPE_CFG) &&
                              (hdr_op == 1'b0);

    assign todo_credit_drop = !in_pkt && s_valid && s_ready &&
                              coord_match && (hdr_ptype == PTYPE_CREDIT);
    assign todo_cfg_read_drop = !in_pkt && s_valid && s_ready &&
                                coord_match && (hdr_ptype == PTYPE_CFG) &&
                                (hdr_op == 1'b1);

    assign drop_head = !in_pkt && s_valid && s_ready &&
                       (!coord_match ||
                        ((hdr_ptype != PTYPE_MEM) &&
                         (hdr_ptype != PTYPE_CFG)));

    // -------------------------------------------------------------------------
    // Ready backpressure: accept while input memory has space for mem payloads.
    // For non-mem heads we are always ready in slice 1.
    // -------------------------------------------------------------------------
    always_comb begin
        if (in_pkt && (pkt_ptype == PTYPE_MEM)) begin
            s_ready = mem_wr_ready;
        end else begin
            s_ready = 1'b1;
        end
    end

    // -------------------------------------------------------------------------
    // Output drive
    // -------------------------------------------------------------------------
    assign mem_wr_valid   = accept_mem_payload;
    assign mem_wr_data    = s_data[LINE_W-1:0];
    assign mem_wr_src_coord = pkt_src_coord;
    assign mem_wr_addr    = ADDR_W'(pkt_target) + mem_wr_ptr;

    assign cfg_wr_valid   = accept_cfg_write;
    assign cfg_wr_addr    = hdr_target[7:0];
    assign cfg_wr_data    = s_data[31:0];

    assign cfg_rd_valid   = todo_cfg_read_drop;
    assign cfg_rd_addr    = hdr_target[7:0];

    assign inc_lines_in   = accept_mem_payload;
    assign inc_err_drop   = drop_head;

    // -------------------------------------------------------------------------
    // Running packet state
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            in_pkt        <= 1'b0;
            pkt_src_coord <= '0;
            pkt_ptype     <= '0;
            pkt_target    <= '0;
            mem_wr_ptr    <= '0;
        end else begin
            if (accept_head) begin
                if (!s_last) begin
                    in_pkt        <= 1'b1;
                    pkt_src_coord <= hdr_src_coord;
                    pkt_ptype     <= hdr_ptype;
                    pkt_target    <= hdr_target;
                    mem_wr_ptr    <= '0;
                end
            end else if (accept_mem_payload) begin
                mem_wr_ptr <= mem_wr_ptr + 1'b1;
                if (s_last) begin
                    in_pkt <= 1'b0;
                end
            end else if ((accept_cfg_write || todo_cfg_read_drop ||
                          todo_credit_drop || drop_head) && s_last) begin
                in_pkt <= 1'b0;
            end else if ((accept_cfg_write || todo_cfg_read_drop ||
                          todo_credit_drop || drop_head) && !s_last) begin
                // Single-beat cfg/credit/drop heads close immediately.
                in_pkt <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Slice-2/3 counted TODO placeholders
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_todo_credit_drop_cnt   <= '0;
            o_todo_cfg_read_drop_cnt <= '0;
        end else begin
            if (todo_credit_drop &&
                (o_todo_credit_drop_cnt != 32'hFFFF_FFFF)) begin
                o_todo_credit_drop_cnt <= o_todo_credit_drop_cnt + 32'd1;
            end
            if (todo_cfg_read_drop &&
                (o_todo_cfg_read_drop_cnt != 32'hFFFF_FFFF)) begin
                o_todo_cfg_read_drop_cnt <= o_todo_cfg_read_drop_cnt + 32'd1;
            end
        end
    )

endmodule : cell_rx
