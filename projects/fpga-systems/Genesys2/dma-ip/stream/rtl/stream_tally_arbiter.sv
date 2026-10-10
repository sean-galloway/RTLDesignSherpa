// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: stream_tally_arbiter
// Purpose: Round-robin arbiter between two AXIL write masters (an observer
//          monbus group and the interconnect bridge) and one shared record-
//          ingest slave (a monbus_tally_axil rec_* port), PIPELINED across
//          transfers (amba BUG-039).
//
//   Grant is released at the transfer's W handshake (not at B), and each B
//   response is routed back to its owner through a small in-order side
//   queue, so a new AW is accepted while the previous B is still returning.
//   The W window opens in the take cycle or later, NEVER before: both W
//   directions (master-side wready, slave-side wvalid) are gated on
//   (r_aw_taken || take-fires-this-cycle).  A master W skid can hold the
//   next transfer's beat while a grant is still waiting for its AW; an
//   early W at the slave duplicates (consumed without the master skid
//   popping) and an early W at the master releases the grant against the
//   wrong transfer -- both observed with the FSM-free group core's eager
//   W stream (chain test, BUG-039 2026-10-09).  When the take and the W
//   fire in the same cycle (both skid outputs primed) the transfer
//   completes in that cycle and the RELEASE wins the r_aw_taken race, so
//   the next grant starts clean -- that both-fire path is also what keeps
//   the structural rate at 2 cycles per transfer (grant, take+W).
//
//   AXIL ONLY: every transfer is exactly one W beat (no awlen on these
//   ports), so one W handshake completes the granted transfer.  An AXI4
//   version must forward the AW length and release on the last W beat
//   instead.
//
//   The valid side of the slave mux is GRANT-GATED: with no grant active the
//   slave sees awvalid=wvalid=0.  This is load-bearing -- the tally's rec
//   port accepts AW/W unconditionally (awready=1, beats 0/1 wready=1), so an
//   ungated default branch would let the idle cycle between transfers
//   phantom-consume a beat waiting in a master's skid buffer.  The skid
//   would not pop (its ready is grant-gated) and the slave would deliver the
//   SAME beat again under the next grant, misaligning every record after it.
//
// Subsystem: stream harness
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_tally_arbiter
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // ---- master 0: observer monbus group (direct) ----
    input  logic [ADDR_WIDTH-1:0]   obs_awaddr,
    input  logic [2:0]              obs_awprot,
    input  logic                    obs_awvalid,
    output logic                    obs_awready,
    input  logic [DATA_WIDTH-1:0]   obs_wdata,
    input  logic [DATA_WIDTH/8-1:0] obs_wstrb,
    input  logic                    obs_wvalid,
    output logic                    obs_wready,
    output logic [1:0]              obs_bresp,
    output logic                    obs_bvalid,
    input  logic                    obs_bready,

    // ---- master 1: interconnect bridge ----
    input  logic [ADDR_WIDTH-1:0]   br_awaddr,
    input  logic [2:0]              br_awprot,
    input  logic                    br_awvalid,
    output logic                    br_awready,
    input  logic [DATA_WIDTH-1:0]   br_wdata,
    input  logic [DATA_WIDTH/8-1:0] br_wstrb,
    input  logic                    br_wvalid,
    output logic                    br_wready,
    output logic [1:0]              br_bresp,
    output logic                    br_bvalid,
    input  logic                    br_bready,

    // ---- shared slave: monbus_tally_axil record ingest ----
    output logic [ADDR_WIDTH-1:0]   t_awaddr,
    output logic [2:0]              t_awprot,
    output logic                    t_awvalid,
    input  logic                    t_awready,
    output logic [DATA_WIDTH-1:0]   t_wdata,
    output logic [DATA_WIDTH/8-1:0] t_wstrb,
    output logic                    t_wvalid,
    input  logic                    t_wready,
    input  logic [1:0]              t_bresp,
    input  logic                    t_bvalid,
    output logic                    t_bready
);

    // Round-robin grant, released at W completion.  r_last_obs remembers who
    // won last; when both ask, the other side goes first, which bounds
    // either side's wait to one transfer.  The B-route queue holds one entry
    // per granted transfer, in grant order; Bs return in W-completion order
    // (single slave ID), which is grant order, so the head always names the
    // owner of the oldest outstanding B.
    //
    // ONE AW PER GRANT (r_aw_taken), and the W window opens in the take
    // cycle or later (never before): a W skid can be primed with the next
    // transfer's beat while a grant is still waiting for its AW, and an
    // early W in either direction breaks the grant <-> transfer pairing
    // (the group core's W stream runs fully decoupled from AW issue, so
    // this ordering is created on every back-to-back pair -- chain test
    // BUG-039 2026-10-09).  w_gr_wen is the W-window: r_aw_taken (take in
    // an earlier cycle) or w_aw_taken_fire (take THIS cycle).  When the
    // take and the W fire together (both skid outputs primed) the 1-beat
    // transfer completes in that cycle; the release below must then win
    // the r_aw_taken race, so the take-fire set is suppressed on w_w_hs.
    logic       r_gr_obs, r_gr_bridge, r_busy, r_last_obs, r_aw_taken;
    logic [1:0] r_bq [0:3];   // 0 = observer, 1 = bridge
    logic [1:0] r_bq_rd, r_bq_wr;
    logic [2:0] r_bq_cnt;
    logic       w_grant, w_w_hs, w_b_hs, w_aw_taken_fire, w_gr_wen;

    assign w_w_hs = t_wvalid & t_wready;
    assign w_b_hs = t_bvalid & t_bready;
    assign w_grant = !r_busy && (obs_awvalid || br_awvalid);
    assign w_gr_wen = r_aw_taken || w_aw_taken_fire;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_gr_obs    <= 1'b0; r_gr_bridge <= 1'b0; r_busy <= 1'b0;
            r_last_obs  <= 1'b0; r_aw_taken  <= 1'b0;
            r_bq_rd     <= 2'd0; r_bq_wr <= 2'd0; r_bq_cnt <= 3'd0;
        end else begin
            if (!r_busy) begin
                if (obs_awvalid && (!br_awvalid || !r_last_obs)) begin
                    r_gr_obs <= 1'b1; r_busy <= 1'b1; r_last_obs <= 1'b1;
                    r_bq[r_bq_wr] <= 2'd0;
                    r_bq_wr <= r_bq_wr + 2'd1;
                end else if (br_awvalid) begin
                    r_gr_bridge <= 1'b1; r_busy <= 1'b1; r_last_obs <= 1'b0;
                    r_bq[r_bq_wr] <= 2'd1;
                    r_bq_wr <= r_bq_wr + 2'd1;
                end
            end else if (w_w_hs) begin
                // W completes the granted transfer (AXIL: one beat).  If
                // the take fired the same cycle the transfer is complete
                // too -- the release's aw_taken<=0 stands and the
                // take-fire set below is suppressed on w_w_hs.
                r_gr_bridge <= 1'b0; r_gr_obs <= 1'b0; r_busy <= 1'b0;
                r_aw_taken  <= 1'b0;
            end
            if (w_aw_taken_fire && !w_w_hs) begin
                r_aw_taken <= 1'b1;
            end
            if (w_b_hs) begin
                r_bq_rd <= r_bq_rd + 2'd1;
            end
            case ({w_grant, w_b_hs})
                2'b10:   r_bq_cnt <= r_bq_cnt + 3'd1;
                2'b01:   r_bq_cnt <= r_bq_cnt - 3'd1;
                default: ;
            endcase
        end
    )

    // Grant-gated slave mux (see the header: an ungated default branch
    // phantom-consumes beats at the tally's always-ready rec port).  W is
    // additionally w_gr_wen-gated: the slave must not see a W beat before
    // the grant's AW is taken -- it would consume the beat while the
    // master skid (its wready is also wen-gated) does not pop, and the
    // same beat would be delivered again under the next grant.
    always_comb begin
        if (r_gr_bridge) begin
            t_awaddr  = br_awaddr;  t_awprot = br_awprot;
            t_awvalid = br_awvalid; t_wdata  = br_wdata;
            t_wstrb   = br_wstrb;
            t_wvalid  = w_gr_wen ? br_wvalid : 1'b0;
        end else if (r_gr_obs) begin
            t_awaddr  = obs_awaddr;  t_awprot = obs_awprot;
            t_awvalid = obs_awvalid; t_wdata  = obs_wdata;
            t_wstrb   = obs_wstrb;
            t_wvalid  = w_gr_wen ? obs_wvalid : 1'b0;
        end else begin
            t_awaddr  = '0;           t_awprot = 3'd0;
            t_awvalid = 1'b0;         t_wdata  = '0;
            t_wstrb   = '0;           t_wvalid = 1'b0;
        end
        // B ready routes by the oldest outstanding B's owner (the queue
        // head), not by the (already released) grant.
        t_bready  = (r_bq[r_bq_rd] == 2'd1) ? br_bready : obs_bready;
    end

    assign obs_awready = (r_gr_obs && !r_aw_taken) ? t_awready : 1'b0;
    assign obs_wready  = (r_gr_obs &&  w_gr_wen)   ? t_wready  : 1'b0;
    assign obs_bvalid  = (r_bq[r_bq_rd] == 2'd0) ? t_bvalid : 1'b0;
    assign obs_bresp   = t_bresp;
    assign br_awready  = (r_gr_bridge && !r_aw_taken) ? t_awready : 1'b0;
    assign br_wready   = (r_gr_bridge &&  w_gr_wen)   ? t_wready  : 1'b0;
    assign br_bvalid   = (r_bq[r_bq_rd] == 2'd1) ? t_bvalid : 1'b0;
    assign br_bresp    = t_bresp;

    assign w_aw_taken_fire = (r_gr_obs || r_gr_bridge) && !r_aw_taken
                           && t_awvalid && t_awready;

endmodule : stream_tally_arbiter
