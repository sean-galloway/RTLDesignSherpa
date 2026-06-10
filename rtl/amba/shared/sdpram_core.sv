// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_core
// Purpose: Protocol-agnostic Simple Dual-Port BRAM backend. Owns the
//          BRAM array, the burst-aware write/read trackers (with
//          axi_gen_addr), and the bulk-clear FSM. Exposes a single
//          FUB-shaped slave interface so the protocol-specific
//          wrappers (axi4 / axil on either side) drop straight on top
//          without string-switch generate plumbing.
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
//   - WRAP (= 2'b10) is computed correctly by axi_gen_addr but the
//     BRAM glue advances linearly; an assertion in the AXI4 wrappers
//     flags WRAP at the sim boundary until it's been exercised.
//
// Architecture:
//
//   fub_aw/w/b ──→ [ write tracker + axi_gen_addr ] ──→ BRAM port A
//   fub_ar/r   ←── [ read tracker  + axi_gen_addr ] ←── BRAM port B
//
//   Clear FSM owns BRAM port A while w_clearing is asserted (held off
//   until both sides report idle so no glitch on fub_*_ready).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module sdpram_core #(
    parameter int    AXI_ID_WIDTH = 8,    // FUB id width (passthrough; tied 0 by AXIL wrappers)
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    MEM_DEPTH    = 2048
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

    // ---------------------------------------------------------------
    // Forward-declare burst-tracker flags so the clear FSM can gate
    // i_cfg_start_clear on "both sides idle".
    // ---------------------------------------------------------------
    logic r_wr_active;
    logic r_b_pending;
    logic r_rd_active;
    logic r_inflight;

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
                    if (i_cfg_start_clear && !r_wr_active && !r_b_pending
                                          && !r_rd_active && !r_inflight) begin
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
    // Write path -- burst-aware tracker.
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]    r_wr_id;
    logic [ADDR_WIDTH-1:0]      r_wr_addr;
    logic [7:0]                 r_wr_beats_left;
    logic [2:0]                 r_wr_size;
    logic [1:0]                 r_wr_burst;

    logic [AXI_ID_WIDTH-1:0]    r_b_id;
    logic [1:0]                 r_b_resp;

    wire [MEM_AW-1:0]  write_bram_addr     = r_wr_addr[ADDR_LSB +: MEM_AW];
    wire               write_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_aw_word_addr    = r_wr_addr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    wire aw_accept   = fub_awvalid && fub_awready;
    wire w_accept    = fub_wvalid  && fub_wready;
    wire w_last_beat = w_accept && (r_wr_beats_left == 8'd0);
    wire write_fire  = w_accept && !w_clearing;

    assign fub_awready = !r_wr_active && !r_b_pending && !w_clearing;
    assign fub_wready  =  r_wr_active && !w_clearing;
    assign fub_bvalid  =  r_b_pending;
    assign fub_bresp   =  r_b_resp;
    assign fub_bid     =  r_b_id;

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
        .len             (r_wr_beats_left),
        .next_addr       (w_wr_next_addr),
        .next_addr_align (/* unused */)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_active     <= 1'b0;
            r_wr_id         <= '0;
            r_wr_addr       <= '0;
            r_wr_beats_left <= 8'd0;
            r_wr_size       <= 3'd0;
            r_wr_burst      <= 2'b01;
            r_b_pending     <= 1'b0;
            r_b_id          <= '0;
            r_b_resp        <= 2'b00;
        end else begin
            if (r_b_pending && fub_bready) begin
                r_b_pending <= 1'b0;
            end
            if (aw_accept) begin
                r_wr_active     <= 1'b1;
                r_wr_id         <= fub_awid;
                r_wr_addr       <= fub_awaddr;
                r_wr_beats_left <= fub_awlen;
                r_wr_size       <= fub_awsize;
                r_wr_burst      <= fub_awburst;
            end
            if (w_accept) begin
                r_wr_addr <= w_wr_next_addr;
                if (r_wr_beats_left != 8'd0) begin
                    r_wr_beats_left <= r_wr_beats_left - 8'd1;
                end
                if (w_last_beat) begin
                    r_wr_active <= 1'b0;
                    r_b_pending <= 1'b1;
                    r_b_id      <= r_wr_id;
                    r_b_resp    <= write_addr_in_range ? 2'b00 : 2'b10;
                end
            end
        end
    )

    // ---------------------------------------------------------------
    // Read path -- burst-aware tracker.
    // ---------------------------------------------------------------
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_ar_word_addr = fub_araddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    logic [AXI_ID_WIDTH-1:0]    r_rd_id;
    logic [ADDR_WIDTH-1:0]      r_rd_addr;
    logic [7:0]                 r_rd_beats_left;
    logic [2:0]                 r_rd_size;
    logic [1:0]                 r_rd_burst;

    logic [AXI_ID_WIDTH-1:0]    r_inflight_rid;
    logic [1:0]                 r_inflight_rresp;
    logic                       r_inflight_rlast;

    wire ar_accept     = fub_arvalid && fub_arready;
    wire read_issue    = r_rd_active && !w_clearing && (!r_inflight || fub_rready);
    wire is_last       = (r_rd_beats_left == 8'd0);
    wire read_in_range = 1'b1;

    assign fub_arready = !r_rd_active && !w_clearing;

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
        .len             (r_rd_beats_left),
        .next_addr       (w_rd_next_addr),
        .next_addr_align (/* unused */)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_active     <= 1'b0;
            r_rd_id         <= '0;
            r_rd_addr       <= '0;
            r_rd_beats_left <= 8'd0;
            r_rd_size       <= 3'd0;
            r_rd_burst      <= 2'b01;
        end else begin
            if (ar_accept) begin
                r_rd_active     <= 1'b1;
                r_rd_id         <= fub_arid;
                r_rd_addr       <= fub_araddr;
                r_rd_beats_left <= fub_arlen;
                r_rd_size       <= fub_arsize;
                r_rd_burst      <= fub_arburst;
            end
            if (read_issue) begin
                r_rd_addr <= w_rd_next_addr;
                if (r_rd_beats_left != 8'd0) begin
                    r_rd_beats_left <= r_rd_beats_left - 8'd1;
                end
                if (is_last) begin
                    r_rd_active <= 1'b0;
                end
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
