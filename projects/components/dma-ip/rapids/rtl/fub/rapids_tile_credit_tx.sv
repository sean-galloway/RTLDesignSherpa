// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_credit_tx
// Purpose: Credit returns from RAPIDS to the cells and cores (TILE_SPEC 11.9, 11.10)
//
// Description:
//   Every flit or descriptor entry RAPIDS consumes from a strap comes back to
//   its sender as a credit packet: header only, ptype = credit, op = add, the
//   count in the length field and the class in target bits [1:0]. They leave
//   on their own interface (m_credit_*), never behind data, so a return can
//   never wait on traffic that is itself waiting for credits.
//
//   Pending returns are kept per external slot and class (rapids_pkg
//   tile_ext_slot; class 0 = landing-space flits, class 1 = intake entries).
//   ev_* adds one per event, up to NUM_EV events a cycle. The output register
//   takes the next pending entry round-robin as soon as it is free and sends
//   all of it; whatever arrives while a packet waits is coalesced into that
//   slot's next return. Nothing is held back to build a batch.
//
//   A return is addressed to the sender's source coordinate as last seen in a
//   header (seen_*); a slot never seen falls back to rapids_pkg::tile_ext_coord
//   in this tile's layer.
//
//   Resync (TILE_SPEC 11.10, after a root failover): a resync_req pulse, taken
//   only while quiescent, queues one `set` per legal sender: every legal cell
//   gets class 0 = LAND_FLITS, every legal control core class 1 =
//   DESC_PER_CORE. A slot's set replaces its pending add (quiescent means
//   nothing of it is outstanding), and sets go before adds. A request while
//   not quiescent waits until the tile is quiescent. RAPIDS sends one set per
//   sender rather than a multicast: it has no multicast header to build.
//
// Parameters:
//   - LAND_FLITS:    landing space per cell (the class-0 strap)
//   - DESC_PER_CORE: intake entries per control core (the class-1 strap)
//   - SRC_COORD:     this RAPIDS's coordinate (the source of every return)
//   - NUM_EV:        return events per cycle
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_tile_credit_tx #(
    parameter int LAND_FLITS    = 16,
    parameter int DESC_PER_CORE = 2,
    parameter logic [rapids_pkg::TILE_COORD_W-1:0] SRC_COORD =
        {1'b0, rapids_pkg::TILE_LEVEL_IO, 12'h000},
    parameter int NUM_EV        = 3,
    parameter int CNT_W         = 16,
    parameter int XW  = rapids_pkg::TILE_EXT_W,
    parameter int NX  = rapids_pkg::TILE_EXT_SLOTS,
    parameter int CRW = rapids_pkg::TILE_COORD_W
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // One credit to return per event
    input  logic [NUM_EV-1:0]           ev_valid,
    input  logic [NUM_EV-1:0][XW-1:0]   ev_slot,
    input  logic [NUM_EV-1:0]           ev_class,   // 0 = flit, 1 = descriptor entry

    // A sender's coordinate, from its headers
    input  logic                        seen_valid,
    input  logic [XW-1:0]               seen_slot,
    input  logic [CRW-1:0]              seen_coord,

    // Resync (TILE_SPEC 11.10)
    input  logic                        resync_req,    // pulse
    input  logic                        quiescent,
    input  logic [NX-1:0]               ext_legal,     // the saved mask, external half (index 32-63)

    // Credit packets out: the 128-bit tile header, header only
    output logic                        m_credit_valid,
    input  logic                        m_credit_ready,
    output logic [127:0]                m_credit_data,

    // Status
    output logic                        sts_resync_busy, // requested or sending
    output logic [15:0]                 sts_ret_count    // credit packets sent
);

    localparam int NE  = 2 * NX;             // entries: {slot, class}
    localparam int EIW = $clog2(NE);

    logic [NE-1:0][CNT_W-1:0] r_pend;
    logic [NE-1:0]            r_set;          // a resync set is queued for this entry
    logic [NX-1:0][CRW-1:0]   r_coord;
    logic [NX-1:0]            r_known;
    logic                     r_rs_req;       // resync requested, waiting for quiescent
    logic [EIW-1:0]           r_rr;

    // Strap of an entry, and whether a resync covers it
    function automatic logic entry_is_strap(input int e);
        int slot;
        slot = e / 2;
        if (e % 2 == 0) return slot < rapids_pkg::TILE_NUM_CELLS;
        return (slot >= rapids_pkg::TILE_CORE_SLOT0) &&
               (slot <  rapids_pkg::TILE_CORE_SLOT0 + rapids_pkg::TILE_NUM_CORES);
    endfunction

    // Pick: sets first, then adds, round-robin within each
    logic           w_pick, w_pick_set;
    logic [EIW-1:0] w_pick_e;
    always_comb begin
        w_pick     = 1'b0;
        w_pick_set = 1'b0;
        w_pick_e   = '0;
        for (int k = 1; k <= NE; k++) begin
            int e;
            e = (int'(r_rr) + k) % NE;
            if (!w_pick && r_set[e]) begin
                w_pick = 1'b1; w_pick_set = 1'b1; w_pick_e = EIW'(e);
            end
        end
        for (int k = 1; k <= NE; k++) begin
            int e;
            e = (int'(r_rr) + k) % NE;
            if (!w_pick && (r_pend[e] != '0)) begin
                w_pick = 1'b1; w_pick_e = EIW'(e);
            end
        end
    end

    logic w_load;
    assign w_load = w_pick && (!m_credit_valid || m_credit_ready);

    logic [XW-1:0]  w_pk_slot;
    logic           w_pk_cls;
    logic [31:0]    w_pk_cnt;
    logic [CRW-1:0] w_pk_dst;
    assign w_pk_slot = w_pick_e[EIW-1:1];
    assign w_pk_cls  = w_pick_e[0];
    assign w_pk_cnt  = w_pick_set ? (w_pk_cls ? 32'(DESC_PER_CORE) : 32'(LAND_FLITS))
                                  : 32'(r_pend[w_pick_e]);
    assign w_pk_dst  = r_known[w_pk_slot] ? r_coord[w_pk_slot]
                                          : rapids_pkg::tile_ext_coord(w_pk_slot, SRC_COORD[3:0]);

    logic w_rs_go;
    assign w_rs_go = r_rs_req && quiescent;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pend         <= '{default:'0};
            r_set          <= '0;
            r_coord        <= '{default:'0};
            r_known        <= '0;
            r_rs_req       <= 1'b0;
            r_rr           <= EIW'(NE - 1);
            m_credit_valid <= 1'b0;
            m_credit_data  <= '0;
            sts_ret_count  <= '0;
        end else begin
            if (seen_valid) begin
                r_coord[seen_slot] <= seen_coord;
                r_known[seen_slot] <= 1'b1;
            end

            for (int e = 0; e < NE; e++) begin
                logic [CNT_W-1:0] n;
                n = r_pend[e];
                if (w_load && (w_pick_e == EIW'(e))) n = w_pick_set ? '0 : (n - CNT_W'(w_pk_cnt));
                for (int v = 0; v < NUM_EV; v++)
                    if (ev_valid[v] && (ev_slot[v] == XW'(e / 2)) && (ev_class[v] == (e % 2 == 1)))
                        n = n + CNT_W'(1);
                r_pend[e] <= n;
            end

            if (resync_req) r_rs_req <= 1'b1;
            if (w_rs_go) begin
                r_rs_req <= 1'b0;
                for (int e = 0; e < NE; e++)
                    if (entry_is_strap(e) && ext_legal[e / 2]) r_set[e] <= 1'b1;
            end
            if (w_load && w_pick_set) r_set[w_pick_e] <= 1'b0;

            if (m_credit_valid && m_credit_ready) m_credit_valid <= 1'b0;
            if (w_load) begin
                m_credit_valid <= 1'b1;
                m_credit_data  <= rapids_pkg::tile_hdr_pack(
                    w_pk_dst, SRC_COORD, rapids_pkg::TILE_PTYPE_CREDIT, w_pick_set, w_pk_cnt,
                    rapids_pkg::TILE_TARGET_W'(w_pk_cls), 4'h0);
                r_rr           <= w_pick_e;
                sts_ret_count  <= sts_ret_count + 16'd1;
            end
        end
    )

    assign sts_resync_busy = r_rs_req || (r_set != '0);

endmodule : rapids_tile_credit_tx
