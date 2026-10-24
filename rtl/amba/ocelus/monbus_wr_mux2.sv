// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_wr_mux2
// Purpose: Two AXI4-shaped write FUBs onto one, in AW order, FSM-free.
//
//   Merges two independent burst writers (monbus_burst_writer) onto a
//   single AXI4-shaped master-write port. AXI4 requires the W stream to
//   follow AW order and returns B in order per ID (both writers use the
//   same single ID), so the mux keeps two small order queues of source
//   tags, both pushed at every AW handshake:
//
//     W queue : the head names the source whose W beats go out next;
//               popped on the wlast handshake.
//     B queue : the head names the source the next B credit belongs to;
//               popped on the B handshake.
//
//   AW arbitration is fixed priority, port 0 over port 1, one AW per
//   cycle; once an AW is on the bus without awready the grant is locked
//   until the handshake, so the AW fields hold as AXI requires. Port 0 is
//   meant for the error writer: errors are rare and latency-sensitive,
//   the trace stream is bulk. A writer only raises awvalid for beats
//   already in its FIFO (monbus_burst_writer plans bursts from arrived
//   beats), so the W stream of a granted burst can always complete and
//   the ordering queues never deadlock.
//
//   Both ports MUST issue the same AWID: B is routed back by AW order,
//   not by ID, which is only correct while every write shares one ID
//   (AXI orders B per ID). monbus_burst_writer always issues ID 0.
//
//   AW is held when either queue is full. ORDER_DEPTH must cover the sum
//   of both writers' outstanding caps (WR_OS_CAP = 4 each), so the
//   default 8 is never actually the limiter.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_wr_mux2 #(
    parameter int ADDR_WIDTH    = 32,
    parameter int AXI_ID_WIDTH  = 1,
    parameter int ORDER_DEPTH   = 8        // entries per order queue (power of 2)
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    // ------------------------------------------------------------------
    // Port 0 (priority) -- AXI4-shaped write FUB in
    // ------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]       s0_awid,
    input  logic [ADDR_WIDTH-1:0]         s0_awaddr,
    input  logic [7:0]                    s0_awlen,
    input  logic [2:0]                    s0_awsize,
    input  logic [1:0]                    s0_awburst,
    input  logic                          s0_awvalid,
    output logic                          s0_awready,
    input  logic [63:0]                   s0_wdata,
    input  logic [7:0]                    s0_wstrb,
    input  logic                          s0_wlast,
    input  logic                          s0_wvalid,
    output logic                          s0_wready,
    output logic [AXI_ID_WIDTH-1:0]       s0_bid,
    output logic [1:0]                    s0_bresp,
    output logic                          s0_bvalid,
    input  logic                          s0_bready,

    // ------------------------------------------------------------------
    // Port 1 -- AXI4-shaped write FUB in
    // ------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]       s1_awid,
    input  logic [ADDR_WIDTH-1:0]         s1_awaddr,
    input  logic [7:0]                    s1_awlen,
    input  logic [2:0]                    s1_awsize,
    input  logic [1:0]                    s1_awburst,
    input  logic                          s1_awvalid,
    output logic                          s1_awready,
    input  logic [63:0]                   s1_wdata,
    input  logic [7:0]                    s1_wstrb,
    input  logic                          s1_wlast,
    input  logic                          s1_wvalid,
    output logic                          s1_wready,
    output logic [AXI_ID_WIDTH-1:0]       s1_bid,
    output logic [1:0]                    s1_bresp,
    output logic                          s1_bvalid,
    input  logic                          s1_bready,

    // ------------------------------------------------------------------
    // Merged AXI4-shaped write FUB out
    // ------------------------------------------------------------------
    output logic [AXI_ID_WIDTH-1:0]       m_awid,
    output logic [ADDR_WIDTH-1:0]         m_awaddr,
    output logic [7:0]                    m_awlen,
    output logic [2:0]                    m_awsize,
    output logic [1:0]                    m_awburst,
    output logic                          m_awvalid,
    input  logic                          m_awready,
    output logic [63:0]                   m_wdata,
    output logic [7:0]                    m_wstrb,
    output logic                          m_wlast,
    output logic                          m_wvalid,
    input  logic                          m_wready,
    input  logic [AXI_ID_WIDTH-1:0]       m_bid,
    input  logic [1:0]                    m_bresp,
    input  logic                          m_bvalid,
    output logic                          m_bready
);

    localparam int QAW = $clog2(ORDER_DEPTH);

    // Elaboration-time parameter check (the one sanctioned guard form):
    // the pointers wrap at 2**QAW, so a non-power-of-2 depth would index
    // past the tag store.
`ifndef SYNTHESIS
    initial begin : param_check
        if (ORDER_DEPTH < 2 || (ORDER_DEPTH & (ORDER_DEPTH - 1)) != 0)
            $fatal(1, "monbus_wr_mux2: ORDER_DEPTH must be a power of 2 >= 2 (got %0d)",
                   ORDER_DEPTH);
    end
`endif

    // Order queues: one tag bit per entry (0 = port 0, 1 = port 1).
    logic [ORDER_DEPTH-1:0] r_wq_tag;
    logic [QAW-1:0]         r_wq_rd, r_wq_wr;
    logic [QAW:0]           r_wq_count;
    logic [ORDER_DEPTH-1:0] r_bq_tag;
    logic [QAW-1:0]         r_bq_rd, r_bq_wr;
    logic [QAW:0]           r_bq_count;

    logic w_q_full;
    logic w_aw_sel;        // 0 = port 0 wins (fixed priority)
    logic r_aw_pend;       // an AW is on the bus, not yet accepted: grant locked
    logic r_aw_pend_sel;   // the locked grant
    logic w_aw_issue;
    logic w_wq_nonempty, w_bq_nonempty;
    logic w_w_sel, w_b_sel;
    logic w_w_issue, w_w_last_issue;
    logic w_b_issue;

    // ------------------------------------------------------------------
    // AW: fixed priority, port 0 first; held while an order queue is full.
    // The grant is decided while nothing is on the bus and LOCKED once
    // m_awvalid has been raised without m_awready (r_aw_pend): AXI requires
    // the AW fields to hold while awvalid is high, and re-deciding the grant
    // would swap them under a stalled slave. w_q_full cannot rise under a
    // stalled AW (the counts only rise on an AW handshake), so a raised
    // m_awvalid never drops without one.
    // ------------------------------------------------------------------
    assign w_q_full  = (r_wq_count == (QAW+1)'(ORDER_DEPTH))
                    || (r_bq_count == (QAW+1)'(ORDER_DEPTH));
    assign w_aw_sel  = r_aw_pend ? r_aw_pend_sel : !s0_awvalid;

    assign m_awvalid = (w_aw_sel ? s1_awvalid : s0_awvalid) && !w_q_full;
    assign m_awid    = w_aw_sel ? s1_awid    : s0_awid;
    assign m_awaddr  = w_aw_sel ? s1_awaddr  : s0_awaddr;
    assign m_awlen   = w_aw_sel ? s1_awlen   : s0_awlen;
    assign m_awsize  = w_aw_sel ? s1_awsize  : s0_awsize;
    assign m_awburst = w_aw_sel ? s1_awburst : s0_awburst;

    assign s0_awready = m_awready && !w_q_full && !w_aw_sel;
    assign s1_awready = m_awready && !w_q_full &&  w_aw_sel;
    assign w_aw_issue = m_awvalid && m_awready;

    // ------------------------------------------------------------------
    // W: follow the head of the W order queue; pop on the wlast handshake
    // ------------------------------------------------------------------
    assign w_wq_nonempty = (r_wq_count != '0);
    assign w_w_sel       = r_wq_tag[r_wq_rd];

    assign m_wvalid = w_wq_nonempty && (w_w_sel ? s1_wvalid : s0_wvalid);
    assign m_wdata  = w_w_sel ? s1_wdata : s0_wdata;
    assign m_wstrb  = w_w_sel ? s1_wstrb : s0_wstrb;
    assign m_wlast  = w_w_sel ? s1_wlast : s0_wlast;

    assign s0_wready = w_wq_nonempty && !w_w_sel && m_wready;
    assign s1_wready = w_wq_nonempty &&  w_w_sel && m_wready;
    assign w_w_issue      = m_wvalid && m_wready;
    assign w_w_last_issue = w_w_issue && m_wlast;

    // ------------------------------------------------------------------
    // B: route to the head of the B order queue; pop on the B handshake
    // ------------------------------------------------------------------
    assign w_bq_nonempty = (r_bq_count != '0);
    assign w_b_sel       = r_bq_tag[r_bq_rd];

    assign s0_bvalid = w_bq_nonempty && !w_b_sel && m_bvalid;
    assign s1_bvalid = w_bq_nonempty &&  w_b_sel && m_bvalid;
    assign s0_bid    = m_bid;
    assign s1_bid    = m_bid;
    assign s0_bresp  = m_bresp;
    assign s1_bresp  = m_bresp;
    assign m_bready  = w_bq_nonempty && (w_b_sel ? s1_bready : s0_bready);
    assign w_b_issue = m_bvalid && m_bready;

    // ------------------------------------------------------------------
    // Order queues: push both on AW issue; one combined count update per
    // queue so a same-cycle push and pop cannot clobber (NBA last-win).
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_aw_pend     <= 1'b0;
            r_aw_pend_sel <= 1'b0;
            r_wq_tag   <= '0;
            r_wq_rd    <= '0;
            r_wq_wr    <= '0;
            r_wq_count <= '0;
            r_bq_tag   <= '0;
            r_bq_rd    <= '0;
            r_bq_wr    <= '0;
            r_bq_count <= '0;
        end else begin
            // Grant lock: set on a stalled AW, cleared by its handshake
            // (or when nothing is on the bus).
            if (m_awvalid && !m_awready) begin
                r_aw_pend     <= 1'b1;
                r_aw_pend_sel <= w_aw_sel;
            end else begin
                r_aw_pend     <= 1'b0;
            end
            if (w_aw_issue) begin
                r_wq_tag[r_wq_wr] <= w_aw_sel;
                r_wq_wr           <= r_wq_wr + 1'b1;
                r_bq_tag[r_bq_wr] <= w_aw_sel;
                r_bq_wr           <= r_bq_wr + 1'b1;
            end
            if (w_w_last_issue) r_wq_rd <= r_wq_rd + 1'b1;
            if (w_b_issue)      r_bq_rd <= r_bq_rd + 1'b1;

            case ({w_aw_issue, w_w_last_issue})
                2'b10:   r_wq_count <= r_wq_count + 1'b1;
                2'b01:   r_wq_count <= r_wq_count - 1'b1;
                default: ;
            endcase
            case ({w_aw_issue, w_b_issue})
                2'b10:   r_bq_count <= r_bq_count + 1'b1;
                2'b01:   r_bq_count <= r_bq_count - 1'b1;
                default: ;
            endcase
        end
    )

endmodule : monbus_wr_mux2
