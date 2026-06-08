// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: sdpram_slave
// Purpose: Unified Simple Dual-Port BRAM AXI/AXIL slave. Replaces the
//          two parallel modules (axi4_sdpram_slave + axil_sdpram_slave)
//          with a single source where each side (write, read) picks its
//          protocol independently via the WR_PROTOCOL / RD_PROTOCOL
//          string parameters.
//
// Top-level ports are declared in full AXI4 shape so both protocols use
// the same module signature. In AXIL mode the AXI4-only signals on the
// configured side (id, len, size, burst, lock, cache, qos, region, user)
// are ignored on inputs and driven to 0 on outputs — callers can leave
// them disconnected or tie them off.
//
// Bursts:
//   - AXI4 mode supports INCR (arburst/awburst = 2'b01) and FIXED
//     (= 2'b00) of any length up to AXI4's 256-beat max. WRAP
//     (= 2'b10) is rejected by an assertion in sim and treated as
//     INCR in synth (the BRAM glue advances linearly).
//   - AXIL mode is single-beat by construction (the AXIL skid ties
//     awlen/arlen to 0 on the fub side, so the burst-aware backend
//     just produces one beat per AW/AR).
// Used by:
//   - desc_ram (256-bit, AXI4 wr + AXI4 rd)
//   - debug_sram (64-bit, AXIL wr + AXIL rd)
// Mixed configurations (e.g. AXI4 wr + AXIL rd) are supported by the
// architecture but not currently used.
//
// Architecture:
//
//   s_axi_aw/w/b ──→ [ axi{4,l}_slave_wr ] ──→ fub_aw/w/b ──→ BRAM port A
//                       (skid + protocol)
//
//   s_axi_ar/r   ──→ [ axi{4,l}_slave_rd ] ──→ fub_ar/r   ──→ BRAM port B
//                       (skid + protocol)
//
//   Clear FSM ─── owns port A while bulk-clearing
//
// AXI4-only fields on the chosen side (id, len, size, burst, lock,
// cache, qos, region, user) are routed through skid; AXIL sides tie
// them to 0 internally.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module sdpram_slave #(
    parameter string WR_PROTOCOL  = "AXI4",   // "AXI4" | "AXIL"
    parameter string RD_PROTOCOL  = "AXI4",   // "AXI4" | "AXIL"
    parameter int    AXI_ID_WIDTH = 8,
    parameter int    ADDR_WIDTH   = 32,
    parameter int    DATA_WIDTH   = 256,
    parameter int    USER_WIDTH   = 1,
    parameter int    MEM_DEPTH    = 2048,

    parameter int    SKID_DEPTH_AW = 2,
    parameter int    SKID_DEPTH_W  = 2,
    parameter int    SKID_DEPTH_B  = 2,
    parameter int    SKID_DEPTH_AR = 2,
    parameter int    SKID_DEPTH_R  = 4
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // ---------------------------------------------------------------
    // Slave AXI4-shaped interface (AXIL mode ignores id/len/size/burst/
    // lock/cache/qos/region/user inputs; outputs driven to 0).
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
    // Bulk-clear control
    // ---------------------------------------------------------------
    input  logic                        i_cfg_start_clear,
    output logic                        o_cfg_done_clear,

    // ---------------------------------------------------------------
    // Observation port
    //   o_dbg_vr      [9:0] external valid/ready (AW, W, B, AR, R)
    //   o_dbg_fub_vr  [9:0] fub-side valid/ready (between skid + BRAM)
    //   o_dbg_bram_wr  1-cycle pulse on BRAM port-A write fire
    //   o_dbg_bram_rd  1-cycle pulse on BRAM port-B read fire
    //   o_dbg_busy_wr  write-side skid busy
    //   o_dbg_busy_rd  read-side skid busy
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
    // Fub-side write nets (between protocol skid and BRAM glue).
    // Id/user always carried at full AXI4 width; AXIL skid ties to 0.
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

    // ---------------------------------------------------------------
    // Write-side protocol skid: AXI4 or AXIL
    // ---------------------------------------------------------------
    generate
        if (WR_PROTOCOL == "AXI4") begin : g_wr_axi4
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
        end else begin : g_wr_axil
            // AXIL skid — fub_awid / fub_awlen / etc tied to 0
            axil4_slave_wr #(
                .AXIL_ADDR_WIDTH (ADDR_WIDTH),
                .AXIL_DATA_WIDTH (DATA_WIDTH),
                .SKID_DEPTH_AW   (SKID_DEPTH_AW),
                .SKID_DEPTH_W    (SKID_DEPTH_W),
                .SKID_DEPTH_B    (SKID_DEPTH_B)
            ) u_axil_wr (
                .aclk           (aclk),
                .aresetn        (aresetn),

                .s_axil_awaddr  (s_axi_awaddr),
                .s_axil_awprot  (s_axi_awprot),
                .s_axil_awvalid (s_axi_awvalid),
                .s_axil_awready (s_axi_awready),

                .s_axil_wdata   (s_axi_wdata),
                .s_axil_wstrb   (s_axi_wstrb),
                .s_axil_wvalid  (s_axi_wvalid),
                .s_axil_wready  (s_axi_wready),

                .s_axil_bresp   (s_axi_bresp),
                .s_axil_bvalid  (s_axi_bvalid),
                .s_axil_bready  (s_axi_bready),

                .fub_awaddr     (fub_awaddr),
                .fub_awprot     (fub_awprot),
                .fub_awvalid    (fub_awvalid),
                .fub_awready    (fub_awready),

                .fub_wdata      (fub_wdata),
                .fub_wstrb      (fub_wstrb),
                .fub_wvalid     (fub_wvalid),
                .fub_wready     (fub_wready),

                .fub_bresp      (fub_bresp),
                .fub_bvalid     (fub_bvalid),
                .fub_bready     (fub_bready),

                .busy           (o_dbg_busy_wr)
            );

            // AXIL has no id/len/size/burst/lock/cache/qos/region/user/last
            // on the fub-side. BRAM glue still sees fub_awid (tied 0).
            assign fub_awid     = '0;
            assign fub_awlen    = 8'h00;
            assign fub_awsize   = 3'($clog2(STRB_W));
            assign fub_awburst  = 2'b01;        // INCR
            assign fub_awlock   = 1'b0;
            assign fub_awcache  = 4'h0;
            assign fub_awqos    = 4'h0;
            assign fub_awregion = 4'h0;
            assign fub_awuser   = '0;
            assign fub_wlast    = 1'b1;
            assign fub_wuser    = '0;

            // External AXI4-only outputs not driven by AXIL skid
            assign s_axi_bid   = '0;
            assign s_axi_buser = '0;
        end
    endgenerate

    // ---------------------------------------------------------------
    // Fub-side read nets
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

    // ---------------------------------------------------------------
    // Read-side protocol skid: AXI4 or AXIL
    // ---------------------------------------------------------------
    generate
        if (RD_PROTOCOL == "AXI4") begin : g_rd_axi4
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
        end else begin : g_rd_axil
            axil4_slave_rd #(
                .AXIL_ADDR_WIDTH (ADDR_WIDTH),
                .AXIL_DATA_WIDTH (DATA_WIDTH),
                .SKID_DEPTH_AR   (SKID_DEPTH_AR),
                .SKID_DEPTH_R    (SKID_DEPTH_R)
            ) u_axil_rd (
                .aclk           (aclk),
                .aresetn        (aresetn),

                .s_axil_araddr  (s_axi_araddr),
                .s_axil_arprot  (s_axi_arprot),
                .s_axil_arvalid (s_axi_arvalid),
                .s_axil_arready (s_axi_arready),

                .s_axil_rdata   (s_axi_rdata),
                .s_axil_rresp   (s_axi_rresp),
                .s_axil_rvalid  (s_axi_rvalid),
                .s_axil_rready  (s_axi_rready),

                .fub_araddr     (fub_araddr),
                .fub_arprot     (fub_arprot),
                .fub_arvalid    (fub_arvalid),
                .fub_arready    (fub_arready),

                .fub_rdata      (fub_rdata),
                .fub_rresp      (fub_rresp),
                .fub_rvalid     (fub_rvalid),
                .fub_rready     (fub_rready),

                .busy           (o_dbg_busy_rd)
            );

            // AXIL has no id/len/size/burst/lock/cache/qos/region/user/last
            // on the fub-side. BRAM glue still sees fub_arid (tied 0).
            assign fub_arid     = '0;
            assign fub_arlen    = 8'h00;
            assign fub_arsize   = 3'($clog2(STRB_W));
            assign fub_arburst  = 2'b01;        // INCR
            assign fub_arlock   = 1'b0;
            assign fub_arcache  = 4'h0;
            assign fub_arqos    = 4'h0;
            assign fub_arregion = 4'h0;
            assign fub_aruser   = '0;

            // External AXI4-only outputs not driven by AXIL skid
            assign s_axi_rid   = '0;
            assign s_axi_rlast = 1'b1;          // every R is the last
            assign s_axi_ruser = '0;
        end
    endgenerate

    // ---------------------------------------------------------------
    // Clear FSM — owns BRAM port A while w_clearing is asserted.
    // Walks r_clear_addr 0..MEM_DEPTH-1 writing zeros each cycle, then
    // drops back to IDLE and asserts the sticky done flag.
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
    // Write path — burst-aware tracker.
    //
    // Flow:
    //   1. AW latched into r_wr_* when slot is empty.
    //   2. Each cycle W is asserted, write_fire pulses; BRAM port A
    //      takes the byte-strobed write at r_wr_addr.
    //   3. r_wr_addr advances per beat (INCR / FIXED).
    //   4. When the last beat fires, B is queued; held until B
    //      handshake.
    //
    // bid echoes the original awid; AXIL skid ties awid to 0 so AXIL
    // mode just returns bid=0.
    //
    // The AW slot stays held until B is consumed so we never have
    // two outstanding B responses; this trades a tiny bit of W→AW
    // pipelining for simpler bookkeeping.
    // ---------------------------------------------------------------
    logic                       r_wr_active;
    logic [AXI_ID_WIDTH-1:0]    r_wr_id;
    logic [ADDR_WIDTH-1:0]      r_wr_addr;
    logic [7:0]                 r_wr_beats_left;
    logic [2:0]                 r_wr_size;
    logic [1:0]                 r_wr_burst;

    logic                       r_b_pending;
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

    // AW ready only when no active burst AND no B response pending.
    assign fub_awready = !r_wr_active && !r_b_pending && !w_clearing;
    // W ready while a burst is active (W beats consumed in lockstep).
    assign fub_wready  =  r_wr_active && !w_clearing;
    assign fub_bvalid  =  r_b_pending;
    assign fub_bresp   =  r_b_resp;
    assign fub_bid     =  r_b_id;
    assign fub_buser   =  '0;

    // Combinational next-address for the active write burst — shared
    // INCR / FIXED / WRAP semantics via axi_gen_addr.
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
            // Drain pending B first so a new AW can land same cycle.
            if (r_b_pending && fub_bready) begin
                r_b_pending <= 1'b0;
            end
            // Latch AW.
            if (aw_accept) begin
                r_wr_active     <= 1'b1;
                r_wr_id         <= fub_awid;
                r_wr_addr       <= fub_awaddr;
                r_wr_beats_left <= fub_awlen;
                r_wr_size       <= fub_awsize;
                r_wr_burst      <= fub_awburst;
            end
            // Walk a W beat.
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
    // Read path — burst-aware tracker mirroring the write side.
    //
    // Flow:
    //   1. AR latched into r_rd_* when slot is empty.
    //   2. Each cycle a beat can be issued (BRAM port B captures
    //      r_mem[r_rd_addr]), one inflight register pair holds the
    //      metadata for the beat currently on fub_r.
    //   3. r_rd_addr advances per beat via axi_gen_addr (INCR /
    //      FIXED / WRAP).
    //   4. r_inflight_last is asserted on the final beat, then r_rd_
    //      active drops so the next AR can land.
    //
    // BRAM read latency is 1 cycle, so the inflight slot is
    // single-deep — back-to-back issues are gated by fub_rready.
    // AXIL mode (arlen=0) is just a 1-beat case of this path.
    // ---------------------------------------------------------------
    /* verilator lint_off UNUSED */
    wire [WORD_AW-1:0] fub_ar_word_addr = fub_araddr[ADDR_LSB +: WORD_AW];
    /* verilator lint_on UNUSED */

    logic                       r_rd_active;
    logic [AXI_ID_WIDTH-1:0]    r_rd_id;
    logic [ADDR_WIDTH-1:0]      r_rd_addr;
    logic [7:0]                 r_rd_beats_left;
    logic [2:0]                 r_rd_size;
    logic [1:0]                 r_rd_burst;

    // Inflight (this-beat-on-fub_r) registers
    logic                       r_inflight;
    logic [AXI_ID_WIDTH-1:0]    r_inflight_rid;
    logic [1:0]                 r_inflight_rresp;
    logic                       r_inflight_rlast;

    wire ar_accept   = fub_arvalid && fub_arready;
    wire read_issue  = r_rd_active && !w_clearing && (!r_inflight || fub_rready);
    wire is_last     = (r_rd_beats_left == 8'd0);
    wire read_in_range = 1'b1;

    // AR accepted only when no active burst.
    assign fub_arready = !r_rd_active && !w_clearing;

    // Combinational next-address for the active read burst.
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
    // BRAM — inferred dual-port.
    // ---------------------------------------------------------------
    (* ram_style = "auto" *)
    logic [DATA_WIDTH-1:0] r_mem [MEM_DEPTH];

    // Port A: clear FSM owns port while w_clearing, else byte-enabled
    // write at the active burst's r_wr_addr.
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

    // Port B: 1-cycle read latency at the active burst's r_rd_addr.
    wire [MEM_AW-1:0] read_bram_addr = r_rd_addr[ADDR_LSB +: MEM_AW];
    logic [DATA_WIDTH-1:0] r_bram_rdata;
    always_ff @(posedge aclk) begin
        if (read_issue) begin
            r_bram_rdata <= r_mem[read_bram_addr];
        end
    end

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
    assign fub_ruser  = '0;

    // ---------------------------------------------------------------
    // Observation wiring
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
    // Assertions (sim only). Bursts (INCR / FIXED) of any length are
    // supported on the AXI4 sides; WRAP is computed correctly by
    // axi_gen_addr but the BRAM glue treats every beat as linear, so
    // we flag WRAP at the sim boundary until it's been exercised.
    // ---------------------------------------------------------------
    // synopsys translate_off
    generate
        if (WR_PROTOCOL == "AXI4") begin : g_assert_wr
            always_ff @(posedge aclk) begin
                if (aresetn && s_axi_awvalid && s_axi_awready) begin
                    assert (s_axi_awburst != 2'b10)
                        else $warning("%m: AW WRAP burst (awburst=%b) supported by axi_gen_addr but not yet validated", s_axi_awburst);
                end
            end
        end
        if (RD_PROTOCOL == "AXI4") begin : g_assert_rd
            always_ff @(posedge aclk) begin
                if (aresetn && s_axi_arvalid && s_axi_arready) begin
                    assert (s_axi_arburst != 2'b10)
                        else $warning("%m: AR WRAP burst (arburst=%b) supported by axi_gen_addr but not yet validated", s_axi_arburst);
                end
            end
        end
    endgenerate
    // synopsys translate_on

endmodule : sdpram_slave
