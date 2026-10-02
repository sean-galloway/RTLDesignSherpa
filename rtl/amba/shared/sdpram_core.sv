// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_core
// Purpose: Protocol-agnostic Simple Dual-Port BRAM backend. Owns the
//          BRAM array, the burst-aware write/read trackers (with
//          axi_gen_addr), the per-direction burst command queues, and
//          the bulk-clear FSM. Exposes a single FUB-shaped slave
//          interface so the protocol-specific wrappers (axi4 / axil on
//          either side) drop straight on top without string-switch
//          generate plumbing.
//
// Role in the file family:
//          This is the shared compute kernel. It speaks one wire
//          format (a FUB-shaped AXI superset with id / addr / len /
//          size / burst on AW + AR and id / resp / last on B + R) and
//          nothing else. The four protocol permutations live in
//          thin wrapper modules:
//
//            sdpram_slave_axi4_axi4.sv  -- AXI4 wr, AXI4 rd
//            sdpram_slave_axi4_axil.sv  -- AXI4 wr, AXIL rd
//            sdpram_slave_axil_axi4.sv  -- AXIL wr, AXI4 rd
//            sdpram_slave_axil_axil.sv  -- AXIL wr, AXIL rd
//
//          Each wrapper instantiates the matching axi{4,l}_slave_wr /
//          axi{4,l}_slave_rd leaf module and bridges its FUB-side to
//          this core's FUB inputs. The AXIL side feeds defaults for
//          the AXI4-only fields (awlen=0, awsize=$clog2(STRB_W),
//          awburst=INCR, awid=0) so the burst tracker degenerates to
//          a single-beat path; AXI4 wrappers pass the real fields
//          straight through.
//
// Bursts:
//   - INCR (awburst/arburst = 2'b01) and FIXED (= 2'b00) of any length
//     up to AXI4's 256-beat max.
//   - WRAP (= 2'b10) address math is wrap-shaped via axi_gen_addr (its len
//     input is the LATCHED burst length -- feeding the decrementing remainder
//     shrank the wrap mask mid-burst and folded addresses early), but the
//     BRAM glue advances linearly; an assertion in the AXI4 wrappers
//     flags WRAP at the sim boundary until it's been exercised.
//
// Burst concurrency: TWO DEEP PER DIRECTION, AND THE BOUNDARY IS FREE.
//   Each direction has a small command queue (BURST_Q_DEPTH, default 2)
//   in front of its tracker. The tracker reloads from the queue the same
//   cycle the active burst completes, so the first beat of burst n+1
//   lands the cycle after the last beat of burst n:
//
//     fub_awready = AW queue not full (direct-load when idle AND empty)
//     fub_wready  = r_wr_active (the LAST beat also needs a free B slot)
//     fub_arready = AR queue not full (direct-load when idle AND empty)
//
//   Consequences a master author needs:
//
//   - A master's outstanding capacity up to BURST_Q_DEPTH + 1 per
//     direction is genuinely exercised against this slave. Deeper buys
//     nothing: the BRAM ports are the one-beat-per-cycle limit either
//     way, and the queue's only job is hiding the boundary.
//   - B and R return in command order per direction -- a legal subset
//     of AXI4's per-ID ordering (no completion interleaving across IDs).
//   - The B response has its own queue (same depth), so a master that
//     defers bready does not stall the W channel -- except exactly on a
//     burst's last beat with the B queue full, where wready holds off
//     until a response drains. That is resource backpressure, not a
//     protocol wait: B drains the moment bready rises.
//   - History: this core used to serialise bursts (one tracker per
//     direction, no queue), charging ~2.0 cycles per write burst and
//     ~1.6 per read burst at every boundary -- measured on the Nexys A7
//     RS loop harness 2026-10-01 and recorded in amba ISSUE-004, closed
//     no-action on the argument that the behaviour was the contract.
//     Sean overruled 2026-10-02: the serialisation WAS the bug. This
//     queue is the fix. The RS AXI4 harness's 97.0% / 98.5% codec seams
//     were this cost, not the codec's.
//
// Architecture:
//
//   fub_aw ──→ [ AW queue ] ──→ [ write tracker + axi_gen_addr ] ──→ BRAM port A
//   fub_w  ────────────────────── (gated by tracker + B-queue space)
//   fub_b  ←── [ B queue ] ←──── (burst completions, in order)
//   fub_ar ──→ [ AR queue ] ──→ [ read tracker  + axi_gen_addr ] ←── BRAM port B
//   fub_r  ←── [ inflight reg ] ← (1-cycle BRAM read latency)
//
//   Clear FSM owns BRAM port A while w_clearing is asserted (held off
//   until both trackers, all three queues and the inflight register are
//   empty so no glitch on fub_*_ready).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module sdpram_core #(
    parameter int    AXI_ID_WIDTH = 8,    // FUB id width (passthrough; tied 0 by AXIL wrappers)
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    MEM_DEPTH    = 2048,
    // 1 = honour fub_wstrb per byte (default; preserves every existing user).
    // 0 = full-word writes only, for a memory whose consumer never asserts a
    //     partial strobe. This is not a micro-optimisation: with byte enables
    //     the write block holds a FULL-WORD clear at one address and a
    //     BYTE-GRANULAR write at another inside the same always_ff, and that
    //     mixed granularity on a muxed address will not map to a single BRAM
    //     write port -- Vivado drops the whole array into distributed RAM. A
    //     64 KB instance cost ~23k LUTs that way (LUT-as-Memory 5,400 ->
    //     28,696, Block RAM idle at 2.6%). With USE_WSTRB=0 both branches are
    //     full-word writes and it infers block RAM.
    parameter bit    USE_WSTRB    = 1'b1,
    // Depth of the per-direction burst command queues (and the B response
    // queue). 2 is the smallest value that makes a burst boundary free:
    // one burst active, one waiting. Deeper adds outstanding coverage at
    // a few LUTs an entry; it cannot add throughput (see the header).
    parameter int    BURST_Q_DEPTH = 2
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // -------------------------------------------------------------------
    // FUB write side (AXI-shaped: id + addr + len + size + burst).
    // AXIL wrappers feed: awid=0, awlen=0, awsize=$clog2(STRB_W),
    // awburst=2'b01 (INCR) so the tracker collapses to single-beat.
    // -------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]     fub_awid,
    input  logic [ADDR_WIDTH-1:0]       fub_awaddr,
    input  logic [7:0]                  fub_awlen,
    input  logic [2:0]                  fub_awsize,
    input  logic [1:0]                  fub_awburst,
    input  logic                        fub_awvalid,
    output logic                        fub_awready,

    input  logic [DATA_WIDTH-1:0]       fub_wdata,
    input  logic [DATA_WIDTH/8-1:0]     fub_wstrb,
    input  logic                        fub_wvalid,
    output logic                        fub_wready,

    output logic [AXI_ID_WIDTH-1:0]     fub_bid,
    output logic [1:0]                  fub_bresp,
    output logic                        fub_bvalid,
    input  logic                        fub_bready,

    // -------------------------------------------------------------------
    // FUB read side (AXI-shaped, same convention as the write side).
    // -------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]     fub_arid,
    input  logic [ADDR_WIDTH-1:0]       fub_araddr,
    input  logic [7:0]                  fub_arlen,
    input  logic [2:0]                  fub_arsize,
    input  logic [1:0]                  fub_arburst,
    input  logic                        fub_arvalid,
    output logic                        fub_arready,

    output logic [AXI_ID_WIDTH-1:0]     fub_rid,
    output logic [DATA_WIDTH-1:0]       fub_rdata,
    output logic [1:0]                  fub_rresp,
    output logic                        fub_rlast,
    output logic                        fub_rvalid,
    input  logic                        fub_rready,

    // -------------------------------------------------------------------
    // Bulk-clear control
    // -------------------------------------------------------------------
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,

    // -------------------------------------------------------------------
    // Observation
    //   o_dbg_fub_vr  [9:0] fub-side valid/ready (AW,W,B,AR,R)
    //   o_dbg_bram_wr  1-cycle pulse on BRAM port-A write fire
    //   o_dbg_bram_rd  1-cycle pulse on BRAM port-B read fire
    // -------------------------------------------------------------------
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd
);

    // ---------------------------------------------------------------
    // Derived constants
    // ---------------------------------------------------------------
    localparam int STRB_W   = DATA_WIDTH / 8;
    localparam int ADDR_LSB = $clog2(STRB_W);
    localparam int MEM_AW   = $clog2(MEM_DEPTH);
    localparam int WORD_AW  = ADDR_WIDTH - ADDR_LSB;
    localparam int CMD_W    = AXI_ID_WIDTH + ADDR_WIDTH + 8 + 3 + 2;
    localparam int B_W      = AXI_ID_WIDTH + 2;

    // ---------------------------------------------------------------
    // Forward-declare tracker and queue flags so the clear FSM can
    // gate i_cfg_start_clear on "everything idle".
    // ---------------------------------------------------------------
    logic r_wr_active;
    logic r_rd_active;
    logic r_inflight;
    logic awq_rd_valid;
    logic bq_rd_valid;
    logic arq_rd_valid;

    // ---------------------------------------------------------------
    // Clear FSM -- owns BRAM port A while w_clearing is asserted.
    // ---------------------------------------------------------------
    typedef enum logic { CLR_IDLE = 1'b0, CLR_BUSY = 1'b1 } clr_state_e;
    clr_state_e        r_clr_state;
    logic [MEM_AW-1:0] r_clear_addr;
    logic              r_done_clear;
    wire               clr_last   = (r_clear_addr == MEM_AW'(MEM_DEPTH - 1));
    wire               w_clearing = (r_clr_state == CLR_BUSY);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_clr_state  <= CLR_IDLE;
            r_clear_addr <= '0;
            r_done_clear <= 1'b0;
        end else begin
            unique case (r_clr_state)
                CLR_IDLE: begin
                    if (i_cfg_start_clear && !r_wr_active && !awq_rd_valid
                                          && !bq_rd_valid
                                          && !r_rd_active && !arq_rd_valid
                                          && !r_inflight) begin
                        r_clr_state  <= CLR_BUSY;
                        r_clear_addr <= '0;
                        r_done_clear <= 1'b0;
                    end
                end
                CLR_BUSY: begin
                    if (clr_last) begin
                        r_clr_state  <= CLR_IDLE;
                        r_done_clear <= 1'b1;
                    end else begin
                        r_clear_addr <= r_clear_addr + 1'b1;
                    end
                end
            endcase
        end
    )

    assign o_cfg_done_clear = r_done_clear;

    // ---------------------------------------------------------------
    // Write path -- AW command queue + burst tracker + B queue.
    //
    // wr_reload fires the cycle the active burst completes (or while
    // the tracker sits idle with a queued command), so the tracker
    // never drops between bursts. The direct path (aw_direct) keeps
    // from-idle first-beat latency at the old single-tracker value
    // instead of paying a queue hop on every lonely burst.
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]    r_wr_id;
    logic [ADDR_WIDTH-1:0]      r_wr_addr;
    logic [7:0]                 r_wr_beats_left;
    logic [7:0]                 r_wr_len;       // latched awlen: axi_gen_addr's
                                                // wrap mask needs the CONSTANT
                                                // burst length, not the
                                                // decrementing remainder
    logic [2:0]                 r_wr_size;
    logic [1:0]                 r_wr_burst;

    logic                       awq_wr_ready;
    logic [CMD_W-1:0]           awq_rd_data;
    logic                       bq_wr_ready;
    logic [B_W-1:0]             bq_rd_data;

    wire [MEM_AW-1:0]  write_bram_addr     = r_wr_addr[ADDR_LSB +: MEM_AW];
    wire               write_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_aw_word_addr    = r_wr_addr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    wire aw_direct = !r_wr_active && !awq_rd_valid;
    wire aw_accept = fub_awvalid && fub_awready;
    wire awq_push  = aw_accept && !aw_direct;
    wire awq_pop;

    wire w_accept       = fub_wvalid && fub_wready;
    wire w_last_pending = (r_wr_beats_left == 8'd0);
    wire w_last_beat    = w_accept && w_last_pending;
    wire write_fire     = w_accept && !w_clearing;

    wire wr_reload  = (!r_wr_active || w_last_beat) && awq_rd_valid;
    assign awq_pop = wr_reload;

    wire wr_load    = wr_reload || (aw_accept && aw_direct);

    // Load source: the queue head when reloading, the AW pins on a
    // direct from-idle accept (mutually exclusive by construction).
    wire [AXI_ID_WIDTH-1:0] q_awid;
    wire [ADDR_WIDTH-1:0]   q_awaddr;
    wire [7:0]              q_awlen;
    wire [2:0]              q_awsize;
    wire [1:0]              q_awburst;
    assign {q_awid, q_awaddr, q_awlen, q_awsize, q_awburst} = awq_rd_data;

    wire [AXI_ID_WIDTH-1:0] ld_awid    = wr_reload ? q_awid    : fub_awid;
    wire [ADDR_WIDTH-1:0]   ld_awaddr  = wr_reload ? q_awaddr  : fub_awaddr;
    wire [7:0]              ld_awlen   = wr_reload ? q_awlen   : fub_awlen;
    wire [2:0]              ld_awsize  = wr_reload ? q_awsize  : fub_awsize;
    wire [1:0]              ld_awburst = wr_reload ? q_awburst : fub_awburst;

    assign fub_awready = (awq_wr_ready || aw_direct) && !w_clearing;
    assign fub_wready  = r_wr_active && !w_clearing
                         && !(w_last_pending && !bq_wr_ready);

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (CMD_W),
        .DEPTH      (BURST_Q_DEPTH)
    ) u_awq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (awq_push),
        .wr_ready    (awq_wr_ready),
        .wr_data     ({fub_awid, fub_awaddr, fub_awlen, fub_awsize, fub_awburst}),
        .rd_ready    (awq_pop),
        .count       (),
        .rd_valid    (awq_rd_valid),
        .rd_data     (awq_rd_data)
    );

    // B queue: one entry per completed burst, in completion (= command)
    // order. w_last_beat can only fire when bq has space (the wready
    // gate), so the push below never overflows.
    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (B_W),
        .DEPTH      (BURST_Q_DEPTH)
    ) u_bq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_last_beat),
        .wr_ready    (bq_wr_ready),
        .wr_data     ({r_wr_id, (write_addr_in_range ? 2'b00 : 2'b10)}),
        .rd_ready    (fub_bready),
        .count       (),
        .rd_valid    (bq_rd_valid),
        .rd_data     (bq_rd_data)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    assign fub_bvalid = bq_rd_valid;
    assign {fub_bid, fub_bresp} = bq_rd_data;

    logic [ADDR_WIDTH-1:0] w_wr_next_addr;
    axi_gen_addr #(
        .AW  (ADDR_WIDTH),
        .DW  (DATA_WIDTH),
        .ODW (DATA_WIDTH),
        .LEN (8)
    ) u_wr_addr_gen (
        .curr_addr       (r_wr_addr),
        .size            (r_wr_size),
        .burst           (r_wr_burst),
        .len             (r_wr_len),
        .next_addr       (w_wr_next_addr),
        .next_addr_align (/* unused */)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_active     <= 1'b0;
            r_wr_id         <= '0;
            r_wr_addr       <= '0;
            r_wr_beats_left <= 8'd0;
            r_wr_len        <= 8'd0;
            r_wr_size       <= 3'd0;
            r_wr_burst      <= 2'b01;
        end else begin
            if (w_accept && !w_last_beat) begin
                r_wr_addr       <= w_wr_next_addr;
                r_wr_beats_left <= r_wr_beats_left - 8'd1;
            end
            if (wr_load) begin
                r_wr_active     <= 1'b1;
                r_wr_id         <= ld_awid;
                r_wr_addr       <= ld_awaddr;
                r_wr_beats_left <= ld_awlen;
                r_wr_len        <= ld_awlen;
                r_wr_size       <= ld_awsize;
                r_wr_burst      <= ld_awburst;
            end else if (w_last_beat) begin
                r_wr_active <= 1'b0;
            end
        end
    )

    // ---------------------------------------------------------------
    // Read path -- AR command queue + burst tracker (same reload and
    // direct-load shape as the write side).
    // ---------------------------------------------------------------
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_ar_word_addr = fub_araddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    logic [AXI_ID_WIDTH-1:0]    r_rd_id;
    logic [ADDR_WIDTH-1:0]      r_rd_addr;
    logic [7:0]                 r_rd_beats_left;
    logic [7:0]                 r_rd_len;       // latched arlen (see r_wr_len)
    logic [2:0]                 r_rd_size;
    logic [1:0]                 r_rd_burst;

    logic                       arq_wr_ready;
    logic [CMD_W-1:0]           arq_rd_data;

    logic [AXI_ID_WIDTH-1:0]    r_inflight_rid;
    logic [1:0]                 r_inflight_rresp;
    logic                       r_inflight_rlast;

    wire ar_direct  = !r_rd_active && !arq_rd_valid;
    wire ar_accept  = fub_arvalid && fub_arready;
    wire arq_push   = ar_accept && !ar_direct;
    wire read_issue = r_rd_active && !w_clearing && (!r_inflight || fub_rready);
    wire is_last    = (r_rd_beats_left == 8'd0);
    wire read_in_range = 1'b1;

    wire rd_reload  = (!r_rd_active || (read_issue && is_last)) && arq_rd_valid;
    wire arq_pop    = rd_reload;
    wire rd_load    = rd_reload || (ar_accept && ar_direct);

    wire [AXI_ID_WIDTH-1:0] q_arid;
    wire [ADDR_WIDTH-1:0]   q_araddr;
    wire [7:0]              q_arlen;
    wire [2:0]              q_arsize;
    wire [1:0]              q_arburst;
    assign {q_arid, q_araddr, q_arlen, q_arsize, q_arburst} = arq_rd_data;

    wire [AXI_ID_WIDTH-1:0] ld_arid    = rd_reload ? q_arid    : fub_arid;
    wire [ADDR_WIDTH-1:0]   ld_araddr  = rd_reload ? q_araddr  : fub_araddr;
    wire [7:0]              ld_arlen   = rd_reload ? q_arlen   : fub_arlen;
    wire [2:0]              ld_arsize  = rd_reload ? q_arsize  : fub_arsize;
    wire [1:0]              ld_arburst = rd_reload ? q_arburst : fub_arburst;

    assign fub_arready = (arq_wr_ready || ar_direct) && !w_clearing;

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (CMD_W),
        .DEPTH      (BURST_Q_DEPTH)
    ) u_arq (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (arq_push),
        .wr_ready    (arq_wr_ready),
        .wr_data     ({fub_arid, fub_araddr, fub_arlen, fub_arsize, fub_arburst}),
        .rd_ready    (arq_pop),
        .count       (),
        .rd_valid    (arq_rd_valid),
        .rd_data     (arq_rd_data)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    logic [ADDR_WIDTH-1:0] w_rd_next_addr;
    axi_gen_addr #(
        .AW  (ADDR_WIDTH),
        .DW  (DATA_WIDTH),
        .ODW (DATA_WIDTH),
        .LEN (8)
    ) u_rd_addr_gen (
        .curr_addr       (r_rd_addr),
        .size            (r_rd_size),
        .burst           (r_rd_burst),
        .len             (r_rd_len),
        .next_addr       (w_rd_next_addr),
        .next_addr_align (/* unused */)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_active     <= 1'b0;
            r_rd_id         <= '0;
            r_rd_addr       <= '0;
            r_rd_beats_left <= 8'd0;
            r_rd_len        <= 8'd0;
            r_rd_size       <= 3'd0;
            r_rd_burst      <= 2'b01;
        end else begin
            if (read_issue && !is_last) begin
                r_rd_addr       <= w_rd_next_addr;
                r_rd_beats_left <= r_rd_beats_left - 8'd1;
            end
            if (rd_load) begin
                r_rd_active     <= 1'b1;
                r_rd_id         <= ld_arid;
                r_rd_addr       <= ld_araddr;
                r_rd_beats_left <= ld_arlen;
                r_rd_len        <= ld_arlen;
                r_rd_size       <= ld_arsize;
                r_rd_burst      <= ld_arburst;
            end else if (read_issue && is_last) begin
                r_rd_active <= 1'b0;
            end
        end
    )

    // ---------------------------------------------------------------
    // BRAM -- inferred dual-port.
    // ---------------------------------------------------------------
    (* ram_style = "auto" *)
    logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH];

    // Port A: clear FSM owns port while w_clearing, else byte-enabled
    // write at the active burst's r_wr_addr. The WIDTHTRUNC lint-off
    // covers a benign verilator analysis quirk: it computes the
    // required array-index width as MEM_AW+1 (one extra bit for the
    // never-taken wrap-to-MEM_DEPTH path inside the clear FSM) but
    // every index that reaches the array is provably in [0,MEM_DEPTH-1]
    // by tracker construction.
    /* verilator lint_off WIDTHTRUNC */
    if (USE_WSTRB) begin : g_wstrb
        always_ff @(posedge aclk) begin
            if (w_clearing) begin
                r_mem[r_clear_addr] <= '0;
            end else if (write_fire && write_addr_in_range) begin
                for (int b = 0; b < STRB_W; b++) begin
                    if (fub_wstrb[b]) begin
                        r_mem[write_bram_addr][8*b +: 8] <= fub_wdata[8*b +: 8];
                    end
                end
            end
        end
    end else begin : g_fullword
        // Single write port, one address mux, one full-word datum: the shape
        // block-RAM inference expects. fub_wstrb is ignored by construction.
        always_ff @(posedge aclk) begin
            if (w_clearing || (write_fire && write_addr_in_range)) begin
                r_mem[w_clearing ? r_clear_addr : write_bram_addr] <=
                    w_clearing ? '0 : fub_wdata;
            end
        end
    end
    /* verilator lint_on WIDTHTRUNC */

    // Port B: 1-cycle read latency at the active burst's r_rd_addr.
    wire [MEM_AW-1:0] read_bram_addr = r_rd_addr[ADDR_LSB +: MEM_AW];
    logic [DATA_WIDTH-1:0] r_bram_rdata;
    /* verilator lint_off WIDTHTRUNC */
    always_ff @(posedge aclk) begin
        if (read_issue) begin
            r_bram_rdata <= r_mem[read_bram_addr];
        end
    end
    /* verilator lint_on WIDTHTRUNC */

    // Inflight tracker: captures the (id, last, resp) for the beat
    // currently sitting on fub_r. Clears on handshake unless a new
    // issue refills it this cycle.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_inflight       <= 1'b0;
            r_inflight_rid   <= '0;
            r_inflight_rresp <= 2'b00;
            r_inflight_rlast <= 1'b0;
        end else begin
            if (r_inflight && fub_rready && !read_issue) begin
                r_inflight <= 1'b0;
            end else if (read_issue) begin
                r_inflight       <= 1'b1;
                r_inflight_rid   <= r_rd_id;
                r_inflight_rresp <= read_in_range ? 2'b00 : 2'b10;
                r_inflight_rlast <= is_last;
            end
        end
    )

    assign fub_rvalid = r_inflight;
    assign fub_rdata  = r_bram_rdata;
    assign fub_rresp  = r_inflight_rresp;
    assign fub_rid    = r_inflight_rid;
    assign fub_rlast  = r_inflight_rlast;

    // ---------------------------------------------------------------
    // Observation
    // ---------------------------------------------------------------
    assign o_dbg_fub_vr = {
        fub_rready,  fub_rvalid,
        fub_arready, fub_arvalid,
        fub_bready,  fub_bvalid,
        fub_wready,  fub_wvalid,
        fub_awready, fub_awvalid
    };

    assign o_dbg_bram_wr = write_fire && write_addr_in_range;
    assign o_dbg_bram_rd = read_issue;

endmodule : sdpram_core
