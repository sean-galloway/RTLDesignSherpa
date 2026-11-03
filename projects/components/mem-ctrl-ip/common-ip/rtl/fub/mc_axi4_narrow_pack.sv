// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_axi4_narrow_pack
// Purpose: Narrow-transfer support at the memory controller's host edge. The
//          controller below this block is full-width only: mc_axi_burst_chopper
//          steps every sub-command by AXI_BEATS_PER_BURST full beats and the
//          intakes treat one AXI beat as one full data word, whatever AxSIZE
//          says. A narrow INCR burst (AxSIZE below the bus width, two or more
//          beats per word) therefore read and wrote the wrong words (granite
//          TASK-007: 8-byte beats on the 128-bit host, 1020 of 1024 wrong).
//
//          This block rewrites a narrow INCR burst into the full-width INCR
//          burst that covers the same words, and converts the data beats:
//            AW/AR  a narrow INCR command leaves as AxSIZE = full width,
//                   AxADDR aligned down to the word, AxLEN = words spanned - 1
//                   (from the first beat's size-aligned offset in its word and
//                   (AxLEN+1) << AxSIZE bytes). Anything else is unchanged.
//            W      narrow beats are packed into their word by strobe; the
//                   word leaves on the beat that ends it (the next beat's
//                   offset wraps) or on WLAST. WLAST passes through.
//            R      each returned word is presented once per narrow beat that
//                   falls in it (the beat's bytes are already in their own
//                   lanes of the word); RLAST on the burst's last narrow beat.
//            B      one AW in, one AW out: B passes straight through.
//          Full-width commands, and narrow FIXED / WRAP (which the controller
//          does not support at any width), pass through unchanged and cost
//          no cycle: the converted beat of a full-width burst is the input
//          beat, combinationally.
//
//          Side queues (gaxi_fifo_sync, one record per issued command: conv,
//          the first beat's offset, AxSIZE, and for reads AxLEN) carry the
//          decision from AW to W and from AR to R in issue order. R replay
//          relies on the controller returning R bursts in AR order, which
//          mc_rd_return_ring guarantees.
//
//          W never waits on the controller's AW handshake. An AW is accepted
//          upstream whenever its W record and an AW-queue slot are free; with
//          the queue empty and the controller ready it passes straight
//          through in the same cycle, otherwise it waits in the queue (in
//          order, converted) and the controller sees exactly the AW stream it
//          would have seen without this block. W takes its record at upstream
//          acceptance, or from the AW being presented upstream (AXI holds a
//          valid AW stable), so a master whose W runs several bursts ahead of
//          the controller's AW acceptance -- the engine-runner pattern -- is
//          not stalled. W waits only when no AW has been presented for it.
//
//          FSM-free: per direction a first-beat flag, a word offset, a beat
//          count (R) and a partial-word accumulator (W).
//
// Parameters:
//   - AXI_DATA_WIDTH: host bus width, 16..1024 (a power of 2)
//   - AWQ_DEPTH: AWs held when the controller back-pressures AW, so their W
//     can run ahead into the controller as it does without this block
//   - REC_DEPTH: side-queue depth = commands in flight per direction; size it
//     at or above the plane's outstanding capacity or it throttles traffic
//
// Documentation: granite TASK-007 (vault/tracking/.../granite-ddr2-lpddr2/task).
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_axi4_narrow_pack
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,
    parameter int REC_DEPTH      = 32,
    parameter int AWQ_DEPTH      = 8,
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8
)
(
    input  logic            aclk,
    input  logic            aresetn,

    // ---- upstream (host) ----
    input  logic [IW-1:0]   fub_awid,    input  logic [AW-1:0] fub_awaddr,
    input  logic [7:0]      fub_awlen,   input  logic [2:0]    fub_awsize,
    input  logic [1:0]      fub_awburst, input  logic          fub_awlock,
    input  logic [3:0]      fub_awcache, input  logic [2:0]    fub_awprot,
    input  logic [3:0]      fub_awqos,   input  logic [3:0]    fub_awregion,
    input  logic [UW-1:0]   fub_awuser,  input  logic          fub_awvalid,
    output logic            fub_awready,
    input  logic [DW-1:0]   fub_wdata,   input  logic [SW-1:0] fub_wstrb,
    input  logic            fub_wlast,   input  logic [UW-1:0] fub_wuser,
    input  logic            fub_wvalid,  output logic          fub_wready,
    output logic [IW-1:0]   fub_bid,     output logic [1:0]    fub_bresp,
    output logic [UW-1:0]   fub_buser,   output logic          fub_bvalid,
    input  logic            fub_bready,
    input  logic [IW-1:0]   fub_arid,    input  logic [AW-1:0] fub_araddr,
    input  logic [7:0]      fub_arlen,   input  logic [2:0]    fub_arsize,
    input  logic [1:0]      fub_arburst, input  logic          fub_arlock,
    input  logic [3:0]      fub_arcache, input  logic [2:0]    fub_arprot,
    input  logic [3:0]      fub_arqos,   input  logic [3:0]    fub_arregion,
    input  logic [UW-1:0]   fub_aruser,  input  logic          fub_arvalid,
    output logic            fub_arready,
    output logic [IW-1:0]   fub_rid,     output logic [DW-1:0] fub_rdata,
    output logic [1:0]      fub_rresp,   output logic          fub_rlast,
    output logic [UW-1:0]   fub_ruser,   output logic          fub_rvalid,
    input  logic            fub_rready,

    // ---- downstream (the controller's splitters / ring) ----
    output logic [IW-1:0]   m_awid,      output logic [AW-1:0] m_awaddr,
    output logic [7:0]      m_awlen,     output logic [2:0]    m_awsize,
    output logic [1:0]      m_awburst,   output logic          m_awlock,
    output logic [3:0]      m_awcache,   output logic [2:0]    m_awprot,
    output logic [3:0]      m_awqos,     output logic [3:0]    m_awregion,
    output logic [UW-1:0]   m_awuser,    output logic          m_awvalid,
    input  logic            m_awready,
    output logic [DW-1:0]   m_wdata,     output logic [SW-1:0] m_wstrb,
    output logic            m_wlast,     output logic [UW-1:0] m_wuser,
    output logic            m_wvalid,    input  logic          m_wready,
    input  logic [IW-1:0]   m_bid,       input  logic [1:0]    m_bresp,
    input  logic [UW-1:0]   m_buser,     input  logic          m_bvalid,
    output logic            m_bready,
    output logic [IW-1:0]   m_arid,      output logic [AW-1:0] m_araddr,
    output logic [7:0]      m_arlen,     output logic [2:0]    m_arsize,
    output logic [1:0]      m_arburst,   output logic          m_arlock,
    output logic [3:0]      m_arcache,   output logic [2:0]    m_arprot,
    output logic [3:0]      m_arqos,     output logic [3:0]    m_arregion,
    output logic [UW-1:0]   m_aruser,    output logic          m_arvalid,
    input  logic            m_arready,
    input  logic [IW-1:0]   m_rid,       input  logic [DW-1:0] m_rdata,
    input  logic [1:0]      m_rresp,     input  logic          m_rlast,
    input  logic [UW-1:0]   m_ruser,     input  logic          m_rvalid,
    output logic            m_rready
);

    localparam int       OW        = $clog2(SW);           // byte offset within a word
    localparam [2:0]     FULL_SIZE = 3'(OW);
    localparam [1:0]     BURST_INCR = 2'b01;
    localparam int       WREC_W    = 1 + OW + 3;           // conv, offset, size
    localparam int       RREC_W    = WREC_W + 8;           // + AxLEN

    // ======================================================================
    // Command rewrite (shared by AW and AR)
    // ======================================================================
    // conv: a narrow INCR burst. off: the first beat's size-aligned offset in
    // its word. len: the full-width AxLEN covering the same words.
    function automatic logic is_conv(input logic [2:0] size, input logic [1:0] burst);
        return (burst == BURST_INCR) && (size < FULL_SIZE);
    endfunction

    function automatic logic [OW-1:0] first_off(input logic [OW-1:0] addr_lo, input logic [2:0] size);
        logic [OW-1:0] mask;
        mask = OW'((1 << size) - 1);
        return addr_lo & ~mask;
    endfunction

    function automatic logic [7:0] word_len(input logic [OW-1:0] off, input logic [7:0] len,
                                            input logic [2:0] size);
        logic [OW+9:0] bytes_end;                          // off + (len+1) << size, rounded up to a word
        logic [OW+9:0] words;
        bytes_end = (OW+10)'(off) + ((OW+10)'({1'b0, len} + 9'd1) << size) + (OW+10)'(SW - 1);
        words     = bytes_end >> OW;
        return 8'(words - (OW+10)'(1));
    endfunction

    // the next beat's offset, and whether this beat ends its word
    function automatic logic [OW:0] next_off(input logic [OW-1:0] off, input logic [2:0] size);
        return (OW+1)'(off) + ((OW+1)'(1) << size);
    endfunction

    // ======================================================================
    // AW: rewrite, record for W, queue behind a back-pressured controller
    // ======================================================================
    localparam int AWQ_W = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW;

    logic             w_aw_conv, w_aw_issue, w_wrec_ready;
    logic [OW-1:0]    w_aw_off;
    logic [AWQ_W-1:0] w_aw_cmd, w_awq_head;
    logic             w_awq_valid, w_awq_wr_ready, w_awq_push, w_awq_pop;

    assign w_aw_conv  = is_conv(fub_awsize, fub_awburst);
    assign w_aw_off   = first_off(fub_awaddr[OW-1:0], fub_awsize);

    // the converted command
    assign w_aw_cmd = {fub_awid,
                       w_aw_conv ? {fub_awaddr[AW-1:OW], {OW{1'b0}}} : fub_awaddr,
                       w_aw_conv ? word_len(w_aw_off, fub_awlen, fub_awsize) : fub_awlen,
                       w_aw_conv ? FULL_SIZE : fub_awsize,
                       fub_awburst, fub_awlock, fub_awcache, fub_awprot,
                       fub_awqos, fub_awregion, fub_awuser};

    // Upstream acceptance needs a W record slot and an AW-queue slot. It never
    // looks at the controller's AWREADY, so W can run ahead of it.
    assign fub_awready = w_wrec_ready && w_awq_wr_ready;
    assign w_aw_issue  = fub_awvalid  && fub_awready;      // accepted upstream

    // Downstream: the queue head, else the accepted AW in its own cycle. An
    // accepted AW the controller does not take this cycle is queued, so
    // m_awvalid stays up with the same command until it does.
    assign {m_awid, m_awaddr, m_awlen, m_awsize, m_awburst, m_awlock, m_awcache,
            m_awprot, m_awqos, m_awregion, m_awuser} = w_awq_valid ? w_awq_head : w_aw_cmd;
    assign m_awvalid  = w_awq_valid || w_aw_issue;
    assign w_awq_push = w_aw_issue && (w_awq_valid || !m_awready);
    assign w_awq_pop  = w_awq_valid && m_awready;

    gaxi_fifo_sync #(
        .DATA_WIDTH (AWQ_W),
        .DEPTH      (AWQ_DEPTH)
    ) u_awq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_awq_push),
        .wr_ready    (w_awq_wr_ready),
        .wr_data     (w_aw_cmd),
        .rd_ready    (w_awq_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_awq_valid),
        .rd_data     (w_awq_head)
    );

    // ======================================================================
    // W: pack narrow beats into their word by strobe
    // ======================================================================
    logic              w_wq_valid, w_wq_push, w_wq_pop;
    logic [WREC_W-1:0] w_wq_data, w_aw_rec;
    logic              w_wrec_valid, w_wrec_conv, w_w_from_aw, w_w_done_ahead;
    logic              r_w_ahead;                          // a W burst finished on the presented AW's record before that AW issued
    logic [OW-1:0]     w_wrec_off;
    logic [2:0]        w_wrec_size;

    logic              r_w_first;                          // next W beat is a burst's first
    logic [OW-1:0]     r_w_off;
    logic [DW-1:0]     r_w_acc;
    logic [SW-1:0]     r_w_acc_strb;
    logic [OW-1:0]     w_w_off;
    logic [OW:0]       w_w_next;
    logic              w_w_emit, w_w_hs;
    logic [DW-1:0]     w_w_merged;

    assign w_aw_rec = {w_aw_conv, w_aw_off, fub_awsize};

    // Record source, oldest first: the queue head (an accepted AW whose W is
    // not finished), else the AW presented upstream -- the next AW in order, held
    // stable by AXI until accepted -- unless its W burst has already finished
    // ahead of it (one at most: the next AW cannot be presented before this
    // one is accepted).
    assign w_w_from_aw  = !w_wq_valid && fub_awvalid && !r_w_ahead;
    assign w_wrec_valid = w_wq_valid || w_w_from_aw;
    assign {w_wrec_conv, w_wrec_off, w_wrec_size} = w_wq_valid ? w_wq_data : w_aw_rec;

    assign w_w_off  = r_w_first ? w_wrec_off : r_w_off;
    assign w_w_next = next_off(w_w_off, w_wrec_size);
    assign w_w_emit = !w_wrec_conv || w_w_next[OW] || fub_wlast;

    always_comb begin
        for (int b = 0; b < SW; b++)
            w_w_merged[b*8 +: 8] = fub_wstrb[b] ? fub_wdata[b*8 +: 8] : r_w_acc[b*8 +: 8];
    end

    assign m_wdata    = w_wrec_conv ? w_w_merged                   : fub_wdata;
    assign m_wstrb    = w_wrec_conv ? (r_w_acc_strb | fub_wstrb)   : fub_wstrb;
    assign m_wlast    = fub_wlast;
    assign m_wuser    = fub_wuser;
    assign m_wvalid   = fub_wvalid && w_wrec_valid && w_w_emit;
    assign fub_wready = w_wrec_valid && (w_w_emit ? m_wready : 1'b1);
    assign w_w_hs     = fub_wvalid && fub_wready;

    // An issuing AW is queued for its W unless that W burst already finished
    // (r_w_ahead) or finishes in this cycle on the presented record.
    assign w_w_done_ahead = w_w_from_aw && w_w_hs && fub_wlast;
    assign w_wq_push = w_aw_issue && !r_w_ahead && !w_w_done_ahead;
    assign w_wq_pop  = w_wq_valid && w_w_hs && fub_wlast;

    gaxi_fifo_sync #(
        .DATA_WIDTH (WREC_W),
        .DEPTH      (REC_DEPTH)
    ) u_wrec (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_wq_push),
        .wr_ready    (w_wrec_ready),
        .wr_data     (w_aw_rec),
        .rd_ready    (w_wq_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_wq_valid),
        .rd_data     (w_wq_data)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_w_ahead    <= 1'b0;
        end else begin
            if (w_w_done_ahead && !w_aw_issue) r_w_ahead <= 1'b1;
            else if (w_aw_issue)               r_w_ahead <= 1'b0;
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_w_first    <= 1'b1;
            r_w_off      <= '0;
            r_w_acc      <= '0;
            r_w_acc_strb <= '0;
        end else if (w_w_hs) begin
            r_w_first <= fub_wlast;
            r_w_off   <= w_w_next[OW-1:0];
            if (w_w_emit) begin
                r_w_acc_strb <= '0;
            end else begin
                r_w_acc      <= w_w_merged;
                r_w_acc_strb <= r_w_acc_strb | fub_wstrb;
            end
        end
    )

    // ======================================================================
    // B: one per AW either way
    // ======================================================================
    assign fub_bid    = m_bid;
    assign fub_bresp  = m_bresp;
    assign fub_buser  = m_buser;
    assign fub_bvalid = m_bvalid;
    assign m_bready   = fub_bready;

    // ======================================================================
    // AR: rewrite, record for R
    // ======================================================================
    logic          w_ar_conv, w_ar_issue, w_rrec_ready;
    logic [OW-1:0] w_ar_off;

    assign w_ar_conv  = is_conv(fub_arsize, fub_arburst);
    assign w_ar_off   = first_off(fub_araddr[OW-1:0], fub_arsize);

    assign m_arid     = fub_arid;
    assign m_araddr   = w_ar_conv ? {fub_araddr[AW-1:OW], {OW{1'b0}}} : fub_araddr;
    assign m_arlen    = w_ar_conv ? word_len(w_ar_off, fub_arlen, fub_arsize) : fub_arlen;
    assign m_arsize   = w_ar_conv ? FULL_SIZE : fub_arsize;
    assign m_arburst  = fub_arburst;
    assign m_arlock   = fub_arlock;
    assign m_arcache  = fub_arcache;
    assign m_arprot   = fub_arprot;
    assign m_arqos    = fub_arqos;
    assign m_arregion = fub_arregion;
    assign m_aruser   = fub_aruser;
    assign m_arvalid   = fub_arvalid && w_rrec_ready;
    assign fub_arready = m_arready   && w_rrec_ready;
    assign w_ar_issue  = m_arvalid   && m_arready;

    // ======================================================================
    // R: present each word once per narrow beat in it
    // ======================================================================
    logic              w_rq_valid, w_rq_pop;
    logic [RREC_W-1:0] w_rq_data;
    logic              w_rrec_conv;
    logic [OW-1:0]     w_rrec_off;
    logic [2:0]        w_rrec_size;
    logic [7:0]        w_rrec_len;

    logic              r_r_first;                          // next R beat is a burst's first
    logic [OW-1:0]     r_r_off;
    logic [7:0]        r_r_cnt;                            // narrow beats presented, this burst
    logic [OW-1:0]     w_r_off;
    logic [7:0]        w_r_cnt;
    logic [OW:0]       w_r_next;
    logic              w_r_last, w_r_word_done, w_r_hs;

    gaxi_fifo_sync #(
        .DATA_WIDTH (RREC_W),
        .DEPTH      (REC_DEPTH)
    ) u_rrec (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_issue),
        .wr_ready    (w_rrec_ready),
        .wr_data     ({w_ar_conv, w_ar_off, fub_arsize, fub_arlen}),
        .rd_ready    (w_rq_pop),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_rq_valid),
        .rd_data     (w_rq_data)
    );

    assign {w_rrec_conv, w_rrec_off, w_rrec_size, w_rrec_len} = w_rq_data;

    assign w_r_off       = r_r_first ? w_rrec_off : r_r_off;
    assign w_r_cnt       = r_r_first ? 8'd0       : r_r_cnt;
    assign w_r_next      = next_off(w_r_off, w_rrec_size);
    assign w_r_last      = w_rrec_conv ? (w_r_cnt == w_rrec_len) : m_rlast;
    // the downstream word is consumed with the last narrow beat that uses it
    assign w_r_word_done = !w_rrec_conv || w_r_next[OW] || w_r_last;

    assign fub_rid    = m_rid;
    assign fub_rdata  = m_rdata;
    assign fub_rresp  = m_rresp;
    assign fub_ruser  = m_ruser;
    assign fub_rlast  = w_r_last;
    assign fub_rvalid = m_rvalid && w_rq_valid;
    assign m_rready   = fub_rready && w_rq_valid && w_r_word_done;
    assign w_r_hs     = fub_rvalid && fub_rready;
    assign w_rq_pop   = w_r_hs && w_r_last;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_r_first <= 1'b1;
            r_r_off   <= '0;
            r_r_cnt   <= '0;
        end else if (w_r_hs) begin
            r_r_first <= w_r_last;
            r_r_off   <= w_r_next[OW-1:0];
            r_r_cnt   <= w_r_cnt + 8'd1;
        end
    )

endmodule : mc_axi4_narrow_pack
