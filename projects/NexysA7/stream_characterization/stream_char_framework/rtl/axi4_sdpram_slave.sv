// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axi4_sdpram_slave
// Purpose: Pipelined AXI4 slave backed by a Simple Dual-Port BRAM.
//
// Mirrors axil_sdpram_slave.sv but at the AXI4 protocol level (id, len,
// size, burst, lock, cache, qos, region, user). Reuses axi4_slave_wr /
// axi4_slave_rd as the protocol-side skid wrappers so this module owns
// only the BRAM glue + id pass-through.
//
// Architecture:
//
//   s_axi_aw/w/b ──→ [ axi4_slave_wr ] ──→ fub_aw/w/b ──→ BRAM port A
//                       (skid buffers + id carry)
//
//   s_axi_ar/r   ──→ [ axi4_slave_rd ] ──→ fub_ar/r   ──→ BRAM port B
//                       (skid buffers + id carry)
//
// Bursts: single-beat ONLY (arlen=awlen=0). Used by:
//   - STREAM's m_axi_desc (single-beat 256b descriptor reads)
//   - Bridge axil_to_axi4_wide_align_wr (single-beat aligned host writes)
// Multi-beat bursts will mis-handshake (no rlast walking, no addr stride).
// An assertion catches this in sim.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_sdpram_slave #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int ADDR_WIDTH     = 32,
    parameter int DATA_WIDTH     = 256,
    parameter int USER_WIDTH     = 1,
    parameter int MEM_DEPTH      = 2048,      // BRAM depth in DATA_WIDTH words

    parameter int SKID_DEPTH_AW  = 2,
    parameter int SKID_DEPTH_W   = 2,
    parameter int SKID_DEPTH_B   = 2,
    parameter int SKID_DEPTH_AR  = 2,
    parameter int SKID_DEPTH_R   = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // ---------------------------------------------------------------
    // AXI4 slave interface
    // ---------------------------------------------------------------
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [ADDR_WIDTH-1:0]       s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [USER_WIDTH-1:0]       s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write data channel (W)
    input  logic [DATA_WIDTH-1:0]       s_axi_wdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [USER_WIDTH-1:0]       s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [USER_WIDTH-1:0]       s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [ADDR_WIDTH-1:0]       s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [USER_WIDTH-1:0]       s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [DATA_WIDTH-1:0]       s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [USER_WIDTH-1:0]       s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    // ---------------------------------------------------------------
    // Bulk-clear control (same semantics as axil_sdpram_slave)
    // ---------------------------------------------------------------
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,

    // ---------------------------------------------------------------
    // Observation port (matches axil_sdpram_slave layout)
    //
    // o_dbg_vr      [9:0] external AXI4 valid/ready pairs (AW, W, B, AR, R)
    //                       [0] awvalid  [1] awready
    //                       [2] wvalid   [3] wready
    //                       [4] bvalid   [5] bready
    //                       [6] arvalid  [7] arready
    //                       [8] rvalid   [9] rready
    // o_dbg_fub_vr  [9:0] same shape but on the fub-side (between the
    //                       axi4_slave_* wrappers and the BRAM glue)
    // o_dbg_bram_wr  1-cycle pulse on BRAM port-A write fire
    // o_dbg_bram_rd  1-cycle pulse on BRAM port-B read fire
    // o_dbg_busy_wr  axi4_slave_wr busy
    // o_dbg_busy_rd  axi4_slave_rd busy
    // ---------------------------------------------------------------
    output logic [9:0]                  o_dbg_vr,
    output logic [9:0]                  o_dbg_fub_vr,
    output logic                        o_dbg_bram_wr,
    output logic                        o_dbg_bram_rd,
    output logic                        o_dbg_busy_wr,
    output logic                        o_dbg_busy_rd
);

    // ---------------------------------------------------------------
    // Derived constants
    // ---------------------------------------------------------------
    localparam int STRB_W   = DATA_WIDTH / 8;
    localparam int ADDR_LSB = $clog2(STRB_W);
    localparam int MEM_AW   = $clog2(MEM_DEPTH);
    localparam int WORD_AW  = ADDR_WIDTH - ADDR_LSB;

    // ---------------------------------------------------------------
    // Fub-side write nets (between axi4_slave_wr skid and BRAM glue)
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]   fub_awid;
    logic [ADDR_WIDTH-1:0]     fub_awaddr;
    /* verilator lint_off UNUSED */
    logic [7:0]                fub_awlen;
    logic [2:0]                fub_awsize;
    logic [1:0]                fub_awburst;
    logic                      fub_awlock;
    logic [3:0]                fub_awcache;
    logic [2:0]                fub_awprot;
    logic [3:0]                fub_awqos;
    logic [3:0]                fub_awregion;
    logic [USER_WIDTH-1:0]     fub_awuser;
    logic                      fub_wlast;
    logic [USER_WIDTH-1:0]     fub_wuser;
    /* verilator lint_on UNUSED */
    logic                      fub_awvalid, fub_awready;
    logic [DATA_WIDTH-1:0]     fub_wdata;
    logic [STRB_W-1:0]         fub_wstrb;
    logic                      fub_wvalid,  fub_wready;
    logic [AXI_ID_WIDTH-1:0]   fub_bid;
    logic [1:0]                fub_bresp;
    logic [USER_WIDTH-1:0]     fub_buser;
    logic                      fub_bvalid,  fub_bready;

    axi4_slave_wr #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH),
        .AXI_USER_WIDTH (USER_WIDTH),
        .SKID_DEPTH_AW  (SKID_DEPTH_AW),
        .SKID_DEPTH_W   (SKID_DEPTH_W),
        .SKID_DEPTH_B   (SKID_DEPTH_B)
    ) u_axi4_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awlock   (s_axi_awlock),
        .s_axi_awcache  (s_axi_awcache),
        .s_axi_awprot   (s_axi_awprot),
        .s_axi_awqos    (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser   (s_axi_awuser),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),

        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wuser    (s_axi_wuser),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),

        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_buser    (s_axi_buser),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),

        .fub_axi_awid     (fub_awid),
        .fub_axi_awaddr   (fub_awaddr),
        .fub_axi_awlen    (fub_awlen),
        .fub_axi_awsize   (fub_awsize),
        .fub_axi_awburst  (fub_awburst),
        .fub_axi_awlock   (fub_awlock),
        .fub_axi_awcache  (fub_awcache),
        .fub_axi_awprot   (fub_awprot),
        .fub_axi_awqos    (fub_awqos),
        .fub_axi_awregion (fub_awregion),
        .fub_axi_awuser   (fub_awuser),
        .fub_axi_awvalid  (fub_awvalid),
        .fub_axi_awready  (fub_awready),

        .fub_axi_wdata    (fub_wdata),
        .fub_axi_wstrb    (fub_wstrb),
        .fub_axi_wlast    (fub_wlast),
        .fub_axi_wuser    (fub_wuser),
        .fub_axi_wvalid   (fub_wvalid),
        .fub_axi_wready   (fub_wready),

        .fub_axi_bid      (fub_bid),
        .fub_axi_bresp    (fub_bresp),
        .fub_axi_buser    (fub_buser),
        .fub_axi_bvalid   (fub_bvalid),
        .fub_axi_bready   (fub_bready),

        .busy             (o_dbg_busy_wr)
    );

    // ---------------------------------------------------------------
    // Fub-side read nets (between axi4_slave_rd skid and BRAM glue)
    // ---------------------------------------------------------------
    logic [AXI_ID_WIDTH-1:0]   fub_arid;
    logic [ADDR_WIDTH-1:0]     fub_araddr;
    /* verilator lint_off UNUSED */
    logic [7:0]                fub_arlen;
    logic [2:0]                fub_arsize;
    logic [1:0]                fub_arburst;
    logic                      fub_arlock;
    logic [3:0]                fub_arcache;
    logic [2:0]                fub_arprot;
    logic [3:0]                fub_arqos;
    logic [3:0]                fub_arregion;
    logic [USER_WIDTH-1:0]     fub_aruser;
    /* verilator lint_on UNUSED */
    logic                      fub_arvalid, fub_arready;
    logic [AXI_ID_WIDTH-1:0]   fub_rid;
    logic [DATA_WIDTH-1:0]     fub_rdata;
    logic [1:0]                fub_rresp;
    logic                      fub_rlast;
    logic [USER_WIDTH-1:0]     fub_ruser;
    logic                      fub_rvalid,  fub_rready;

    axi4_slave_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH),
        .AXI_USER_WIDTH (USER_WIDTH),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_R   (SKID_DEPTH_R)
    ) u_axi4_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arlock   (s_axi_arlock),
        .s_axi_arcache  (s_axi_arcache),
        .s_axi_arprot   (s_axi_arprot),
        .s_axi_arqos    (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser   (s_axi_aruser),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),

        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        .s_axi_ruser    (s_axi_ruser),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        .fub_axi_arid     (fub_arid),
        .fub_axi_araddr   (fub_araddr),
        .fub_axi_arlen    (fub_arlen),
        .fub_axi_arsize   (fub_arsize),
        .fub_axi_arburst  (fub_arburst),
        .fub_axi_arlock   (fub_arlock),
        .fub_axi_arcache  (fub_arcache),
        .fub_axi_arprot   (fub_arprot),
        .fub_axi_arqos    (fub_arqos),
        .fub_axi_arregion (fub_arregion),
        .fub_axi_aruser   (fub_aruser),
        .fub_axi_arvalid  (fub_arvalid),
        .fub_axi_arready  (fub_arready),

        .fub_axi_rid      (fub_rid),
        .fub_axi_rdata    (fub_rdata),
        .fub_axi_rresp    (fub_rresp),
        .fub_axi_rlast    (fub_rlast),
        .fub_axi_ruser    (fub_ruser),
        .fub_axi_rvalid   (fub_rvalid),
        .fub_axi_rready   (fub_rready),

        .busy             (o_dbg_busy_rd)
    );

    // ---------------------------------------------------------------
    // Clear FSM (identical to axil_sdpram_slave)
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
                    if (i_cfg_start_clear) begin
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
    // Write fire — combinational handshake against BRAM port A.
    // Same as axil_sdpram_slave; bid echoes fub_awid.
    // ---------------------------------------------------------------
    wire [MEM_AW-1:0]  write_bram_addr     = fub_awaddr[ADDR_LSB +: MEM_AW];
    wire               write_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_aw_word_addr    = fub_awaddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    wire write_fire = fub_awvalid && fub_wvalid && fub_bready && !w_clearing;
    assign fub_awready = fub_wvalid  && fub_bready && !w_clearing;
    assign fub_wready  = fub_awvalid && fub_bready && !w_clearing;
    assign fub_bvalid  = write_fire;
    assign fub_bresp   = write_addr_in_range ? 2'b00 : 2'b10;  // OKAY / SLVERR
    assign fub_bid     = fub_awid;
    assign fub_buser   = '0;

    // ---------------------------------------------------------------
    // Read path — BRAM_READ_LAT = 1, id carried in flight.
    // Mirrors axil_sdpram_slave with arid latched into r_inflight_rid.
    // ---------------------------------------------------------------
    wire [MEM_AW-1:0]  read_bram_addr     = fub_araddr[ADDR_LSB +: MEM_AW];
    wire               read_addr_in_range = 1'b1;
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_ar_word_addr   = fub_araddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    logic                       r_inflight;
    logic [1:0]                 r_inflight_rresp;
    logic [AXI_ID_WIDTH-1:0]    r_inflight_rid;

    wire read_issue = fub_arvalid && fub_arready;
    assign fub_arready = !w_clearing && (!r_inflight || fub_rready);

    // ---------------------------------------------------------------
    // BRAM — inferred dual-port (same as axil_sdpram_slave).
    // ---------------------------------------------------------------
    (* ram_style = "auto" *)
    logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH];

    // Port A: clear FSM owns port while w_clearing, otherwise byte-enabled write.
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

    // Port B: 1-cycle read latency.
    logic [DATA_WIDTH-1:0] r_bram_rdata;
    always_ff @(posedge aclk) begin
        if (read_issue) begin
            r_bram_rdata <= r_mem[read_bram_addr];
        end
    end

    // In-flight tracking (single flop pair + id).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_inflight       <= 1'b0;
            r_inflight_rresp <= 2'b00;
            r_inflight_rid   <= '0;
        end else begin
            if (r_inflight && fub_rready && !read_issue) begin
                r_inflight <= 1'b0;
            end else if (read_issue) begin
                r_inflight       <= 1'b1;
                r_inflight_rresp <= read_addr_in_range ? 2'b00 : 2'b10;
                r_inflight_rid   <= fub_arid;
            end
        end
    )

    assign fub_rvalid = r_inflight;
    assign fub_rdata  = r_bram_rdata;
    assign fub_rresp  = r_inflight_rresp;
    assign fub_rid    = r_inflight_rid;
    assign fub_rlast  = r_inflight;   // single-beat: every R is the last
    assign fub_ruser  = '0;

    // ---------------------------------------------------------------
    // Observation wiring (matches axil_sdpram_slave shape)
    // ---------------------------------------------------------------
    assign o_dbg_vr = {
        s_axi_rready,  s_axi_rvalid,
        s_axi_arready, s_axi_arvalid,
        s_axi_bready,  s_axi_bvalid,
        s_axi_wready,  s_axi_wvalid,
        s_axi_awready, s_axi_awvalid
    };

    assign o_dbg_fub_vr = {
        fub_rready,  fub_rvalid,
        fub_arready, fub_arvalid,
        fub_bready,  fub_bvalid,
        fub_wready,  fub_wvalid,
        fub_awready, fub_awvalid
    };

    assign o_dbg_bram_wr = write_fire && write_addr_in_range;
    assign o_dbg_bram_rd = read_issue;

    // ---------------------------------------------------------------
    // Assertions (sim only): single-beat only, no bursts.
    // ---------------------------------------------------------------
    // synopsys translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && s_axi_arvalid && s_axi_arready) begin
            assert (s_axi_arlen == 8'h00)
                else $error("%m: AR burst (arlen=%0d) not supported; single-beat only", s_axi_arlen);
        end
        if (aresetn && s_axi_awvalid && s_axi_awready) begin
            assert (s_axi_awlen == 8'h00)
                else $error("%m: AW burst (awlen=%0d) not supported; single-beat only", s_axi_awlen);
        end
    end
    // synopsys translate_on

endmodule : axi4_sdpram_slave
