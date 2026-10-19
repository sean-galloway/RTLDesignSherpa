// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: bridge_cdc_slave_arb
// Purpose: Slave-domain arbitration for a slave port on its own clock that
//          two or more masters share (bridge W9).
//
// Description:
//   Each master reaches the slave through its own lanes: one async FIFO each
//   for AW, W and AR, crossing from the fabric clock (aclk) to the slave
//   clock (s_aclk). AW and AR are arbitrated on s_aclk by arbiter_matrix in
//   ACK mode, so the pick is made where the slave is served and the
//   crossings hold only requests not yet granted. (With one crossing behind
//   a fabric-side arbiter, granted requests queued in it and a master's
//   share followed its outstanding count: 0.18-0.20 against 0.80.)
//
//   - The grant is a flop and holds until the slave-side handshake; the
//     payload is the granted lane's FIFO head, muxed by the registered
//     grant ID. On the handshake the arbiter hands the grant on in the same
//     cycle -- to the same lane when it is the only one requesting, so one
//     lane alone still issues one request per cycle. If that lane's FIFO
//     has just emptied, the grant is stale: VALID is masked by the lane's
//     own valid and the grant is released with an ack of its own.
//   - W follows the AW pick: an owner FIFO records the granted lane at each
//     AW handshake, and its head selects the W lane until WLAST.
//   - B and R cross back to aclk through one async FIFO each; the fabric
//     routes them by the master-index bits of their ID.
//   - At most MAX_OUTSTANDING writes and MAX_OUTSTANDING reads are in
//     flight at the slave. The limit counts the AW/AR being presented
//     (registered), so a same-cycle grant handoff can never exceed it; it
//     also bounds the owner FIFO, whose entries live from AW to WLAST.
//
// Parameters:
//   NM              - masters (lanes), >= 1
//   IW, ADDR_W, DW, UW - AXI4 ID / address / data / user widths
//   MAX_OUTSTANDING - per direction at the slave, >= 2
//   CDC_DEPTH       - entries per crossing FIFO (8 carries one beat per
//                     cycle across the crossing's round trip)
//   HAS_WR, HAS_RD  - which directions exist
//
// Lane payloads (fabric side), lane i at [i*PW +: PW]:
//   AW / AR: {id, addr, len, size, burst, lock, cache, prot, qos, region, user}
//   W:       {data, strb, last, user}
//   B:       {id, resp, user}           R: {id, data, resp, last, user}
//
// Dependencies: gaxi_fifo_async (rtl/cdc), gaxi_fifo_sync (rtl/amba/gaxi),
//               arbiter_matrix (rtl/common)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module bridge_cdc_slave_arb #(
    parameter int NM              = 2,
    parameter int IW              = 4,
    parameter int ADDR_W          = 32,
    parameter int DW              = 32,
    parameter int UW              = 1,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CDC_DEPTH       = 8,
    parameter int HAS_WR          = 1,
    parameter int HAS_RD          = 1,
    // Derived: do not override
    parameter int AXPW = IW + ADDR_W + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW,
    parameter int WPW  = DW + DW / 8 + 1 + UW,
    parameter int BPW  = IW + 2 + UW,
    parameter int RPW  = IW + DW + 2 + 1 + UW
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  s_aclk,
    input  logic                  s_aresetn,

    // ---- fabric side (aclk): per-master lanes ----
    input  logic [NM-1:0]         lane_awvalid,
    output logic [NM-1:0]         lane_awready,
    input  logic [NM*AXPW-1:0]    lane_aw,
    input  logic [NM-1:0]         lane_wvalid,
    output logic [NM-1:0]         lane_wready,
    input  logic [NM*WPW-1:0]     lane_w,
    output logic                  fab_bvalid,
    input  logic                  fab_bready,
    output logic [BPW-1:0]        fab_b,
    input  logic [NM-1:0]         lane_arvalid,
    output logic [NM-1:0]         lane_arready,
    input  logic [NM*AXPW-1:0]    lane_ar,
    output logic                  fab_rvalid,
    input  logic                  fab_rready,
    output logic [RPW-1:0]        fab_r,

    // ---- slave side (s_aclk): AXI4 ----
    output logic [IW-1:0]         m_axi_awid,
    output logic [ADDR_W-1:0]     m_axi_awaddr,
    output logic [7:0]            m_axi_awlen,
    output logic [2:0]            m_axi_awsize,
    output logic [1:0]            m_axi_awburst,
    output logic                  m_axi_awlock,
    output logic [3:0]            m_axi_awcache,
    output logic [2:0]            m_axi_awprot,
    output logic [3:0]            m_axi_awqos,
    output logic [3:0]            m_axi_awregion,
    output logic [UW-1:0]         m_axi_awuser,
    output logic                  m_axi_awvalid,
    input  logic                  m_axi_awready,
    output logic [DW-1:0]         m_axi_wdata,
    output logic [DW/8-1:0]       m_axi_wstrb,
    output logic                  m_axi_wlast,
    output logic [UW-1:0]         m_axi_wuser,
    output logic                  m_axi_wvalid,
    input  logic                  m_axi_wready,
    input  logic [IW-1:0]         m_axi_bid,
    input  logic [1:0]            m_axi_bresp,
    input  logic [UW-1:0]         m_axi_buser,
    input  logic                  m_axi_bvalid,
    output logic                  m_axi_bready,
    output logic [IW-1:0]         m_axi_arid,
    output logic [ADDR_W-1:0]     m_axi_araddr,
    output logic [7:0]            m_axi_arlen,
    output logic [2:0]            m_axi_arsize,
    output logic [1:0]            m_axi_arburst,
    output logic                  m_axi_arlock,
    output logic [3:0]            m_axi_arcache,
    output logic [2:0]            m_axi_arprot,
    output logic [3:0]            m_axi_arqos,
    output logic [3:0]            m_axi_arregion,
    output logic [UW-1:0]         m_axi_aruser,
    output logic                  m_axi_arvalid,
    input  logic                  m_axi_arready,
    input  logic [IW-1:0]         m_axi_rid,
    input  logic [DW-1:0]         m_axi_rdata,
    input  logic [1:0]            m_axi_rresp,
    input  logic                  m_axi_rlast,
    input  logic [UW-1:0]         m_axi_ruser,
    input  logic                  m_axi_rvalid,
    output logic                  m_axi_rready
);

    localparam int NB = (NM > 1) ? $clog2(NM) : 1;   // lane index width
    localparam int CW = $clog2(MAX_OUTSTANDING + 1) + 1;

    //==========================================================================
    // Write: AW and W lanes, slave-domain AW pick, W owner, B back
    //==========================================================================
    if (HAS_WR != 0) begin : gen_wr
        logic [NM-1:0]   aw_lv, aw_lr, w_lv, w_lr;
        logic [AXPW-1:0] aw_ld [NM];
        logic [WPW-1:0]  w_ld  [NM];

        for (genvar i = 0; i < NM; i++) begin : gen_lane
            gaxi_fifo_async #(
                .DATA_WIDTH (AXPW),
                .DEPTH      (CDC_DEPTH)
            ) u_aw (
                .axi_wr_aclk    (aclk),
                .axi_wr_aresetn (aresetn),
                .axi_rd_aclk    (s_aclk),
                .axi_rd_aresetn (s_aresetn),
                .wr_valid       (lane_awvalid[i]),
                .wr_ready       (lane_awready[i]),
                .wr_data        (lane_aw[i*AXPW +: AXPW]),
                .rd_ready       (aw_lr[i]),
                .rd_valid       (aw_lv[i]),
                .rd_data        (aw_ld[i])
            );
            gaxi_fifo_async #(
                .DATA_WIDTH (WPW),
                .DEPTH      (CDC_DEPTH)
            ) u_w (
                .axi_wr_aclk    (aclk),
                .axi_wr_aresetn (aresetn),
                .axi_rd_aclk    (s_aclk),
                .axi_rd_aresetn (s_aresetn),
                .wr_valid       (lane_wvalid[i]),
                .wr_ready       (lane_wready[i]),
                .wr_data        (lane_w[i*WPW +: WPW]),
                .rd_ready       (w_lr[i]),
                .rd_valid       (w_lv[i]),
                .rd_data        (w_ld[i])
            );
        end

        // Writes in flight at the slave: up at the AW handshake, down at B.
        // The AW being presented counts too, so the next grant only issues
        // when both it and the presented one fit.
        logic [CW-1:0] wr_cnt;
        logic          aw_gv, aw_hs, b_hs, aw_room;
        logic [NM-1:0] aw_g, aw_ack;
        logic [NB-1:0] aw_gid;
        assign aw_hs   = m_axi_awvalid && m_axi_awready;
        assign b_hs    = m_axi_bvalid && m_axi_bready;
        assign aw_room = (wr_cnt + CW'(aw_gv)) < CW'(MAX_OUTSTANDING);
        `ALWAYS_FF_RST(s_aclk, s_aresetn,
            if (`RST_ASSERTED(s_aresetn)) wr_cnt <= '0;
            else wr_cnt <= wr_cnt + CW'(aw_hs) - CW'(b_hs);
        )

        arbiter_matrix #(
            .CLIENTS      (NM),
            .WAIT_GNT_ACK (1)
        ) u_aw_arb (
            .clk         (s_aclk),
            .rst_n       (s_aresetn),
            .block_arb   (!aw_room),
            .request     (aw_lv),
            .grant_ack   (aw_ack),
            .grant_valid (aw_gv),
            .grant       (aw_g),
            .grant_id    (aw_gid),
            /* verilator lint_off PINCONNECTEMPTY */
            .last_grant  ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        // A lane's FIFO holds valid until its pop, so VALID never drops
        // under a live grant; a stale grant (lane empty) is released.
        assign m_axi_awvalid = aw_gv && aw_lv[aw_gid];
        assign aw_ack        = aw_lr | (aw_g & ~aw_lv);
        assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
                m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
                m_axi_awregion, m_axi_awuser} = aw_ld[aw_gid];
        assign aw_lr = aw_g & {NM{aw_hs}};

        // W owner: the granted lane at each AW handshake, in pick order.
        // Entries live from AW to WLAST, so MAX_OUTSTANDING bounds them.
        logic          own_v, own_wr_ready;
        logic [NB-1:0] own_id;
        logic          w_last_hs;
        assign w_last_hs = m_axi_wvalid && m_axi_wready && m_axi_wlast;
        gaxi_fifo_sync #(
            .DATA_WIDTH (NB),
            .DEPTH      (MAX_OUTSTANDING)
        ) u_owner (
            .axi_aclk    (s_aclk),
            .axi_aresetn (s_aresetn),
            .wr_valid    (aw_hs),
            .wr_ready    (own_wr_ready),
            .wr_data     (aw_gid),
            .rd_ready    (w_last_hs),
            /* verilator lint_off PINCONNECTEMPTY */
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .rd_valid    (own_v),
            .rd_data     (own_id)
        );
        /* verilator lint_off UNUSEDSIGNAL */
        logic unused_own_wr_ready;
        assign unused_own_wr_ready = own_wr_ready;   // never full: see above
        /* verilator lint_on UNUSEDSIGNAL */

        assign m_axi_wvalid = own_v && w_lv[own_id];
        assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser} = w_ld[own_id];
        for (genvar i = 0; i < NM; i++) begin : gen_wsel
            assign w_lr[i] = own_v && (own_id == NB'(i)) && m_axi_wready;
        end

        gaxi_fifo_async #(
            .DATA_WIDTH (BPW),
            .DEPTH      (CDC_DEPTH)
        ) u_b (
            .axi_wr_aclk    (s_aclk),
            .axi_wr_aresetn (s_aresetn),
            .axi_rd_aclk    (aclk),
            .axi_rd_aresetn (aresetn),
            .wr_valid       (m_axi_bvalid),
            .wr_ready       (m_axi_bready),
            .wr_data        ({m_axi_bid, m_axi_bresp, m_axi_buser}),
            .rd_ready       (fab_bready),
            .rd_valid       (fab_bvalid),
            .rd_data        (fab_b)
        );
    end else begin : gen_no_wr
        assign lane_awready = '0;
        assign lane_wready  = '0;
        assign fab_bvalid   = 1'b0;
        assign fab_b        = '0;
        assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
                m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
                m_axi_awregion, m_axi_awuser, m_axi_awvalid} = '0;
        assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser, m_axi_wvalid} = '0;
        assign m_axi_bready = 1'b1;
    end

    //==========================================================================
    // Read: AR lanes, slave-domain AR pick, R back
    //==========================================================================
    if (HAS_RD != 0) begin : gen_rd
        logic [NM-1:0]   ar_lv, ar_lr;
        logic [AXPW-1:0] ar_ld [NM];

        for (genvar i = 0; i < NM; i++) begin : gen_lane
            gaxi_fifo_async #(
                .DATA_WIDTH (AXPW),
                .DEPTH      (CDC_DEPTH)
            ) u_ar (
                .axi_wr_aclk    (aclk),
                .axi_wr_aresetn (aresetn),
                .axi_rd_aclk    (s_aclk),
                .axi_rd_aresetn (s_aresetn),
                .wr_valid       (lane_arvalid[i]),
                .wr_ready       (lane_arready[i]),
                .wr_data        (lane_ar[i*AXPW +: AXPW]),
                .rd_ready       (ar_lr[i]),
                .rd_valid       (ar_lv[i]),
                .rd_data        (ar_ld[i])
            );
        end

        // Reads in flight at the slave: up at AR, down at the last R beat.
        logic [CW-1:0] rd_cnt;
        logic          ar_gv, ar_hs, r_last_hs, ar_room;
        logic [NM-1:0] ar_g, ar_ack;
        logic [NB-1:0] ar_gid;
        assign ar_hs     = m_axi_arvalid && m_axi_arready;
        assign r_last_hs = m_axi_rvalid && m_axi_rready && m_axi_rlast;
        assign ar_room   = (rd_cnt + CW'(ar_gv)) < CW'(MAX_OUTSTANDING);
        `ALWAYS_FF_RST(s_aclk, s_aresetn,
            if (`RST_ASSERTED(s_aresetn)) rd_cnt <= '0;
            else rd_cnt <= rd_cnt + CW'(ar_hs) - CW'(r_last_hs);
        )

        arbiter_matrix #(
            .CLIENTS      (NM),
            .WAIT_GNT_ACK (1)
        ) u_ar_arb (
            .clk         (s_aclk),
            .rst_n       (s_aresetn),
            .block_arb   (!ar_room),
            .request     (ar_lv),
            .grant_ack   (ar_ack),
            .grant_valid (ar_gv),
            .grant       (ar_g),
            .grant_id    (ar_gid),
            /* verilator lint_off PINCONNECTEMPTY */
            .last_grant  ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        assign m_axi_arvalid = ar_gv && ar_lv[ar_gid];
        assign ar_ack        = ar_lr | (ar_g & ~ar_lv);
        assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
                m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
                m_axi_arregion, m_axi_aruser} = ar_ld[ar_gid];
        assign ar_lr = ar_g & {NM{ar_hs}};

        gaxi_fifo_async #(
            .DATA_WIDTH (RPW),
            .DEPTH      (CDC_DEPTH)
        ) u_r (
            .axi_wr_aclk    (s_aclk),
            .axi_wr_aresetn (s_aresetn),
            .axi_rd_aclk    (aclk),
            .axi_rd_aresetn (aresetn),
            .wr_valid       (m_axi_rvalid),
            .wr_ready       (m_axi_rready),
            .wr_data        ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
            .rd_ready       (fab_rready),
            .rd_valid       (fab_rvalid),
            .rd_data        (fab_r)
        );
    end else begin : gen_no_rd
        assign lane_arready = '0;
        assign fab_rvalid   = 1'b0;
        assign fab_r        = '0;
        assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
                m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
                m_axi_arregion, m_axi_aruser, m_axi_arvalid} = '0;
        assign m_axi_rready = 1'b1;
    end

endmodule : bridge_cdc_slave_arb
