// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: debug_sram
// Purpose: 256 KB dual-port debug trace buffer for STREAM characterization.
//
// Asymmetric dual-port BRAM: 64-bit write port from STREAM's m_axil_mon
// master, 32-bit read port for the host UART AXIL bridge. The internal
// storage is 64 bits wide; each host read returns one 32-bit half of a
// 64-bit BRAM word, selected by rd_araddr[2].
//
// Every external AXI4-Lite channel is isolated by a gaxi_skid_buffer for
// timing closure.
//
// Features:
//   - 64-bit AXIL writes from monbus_axil_group's m_axil_mon master.
//     Each beat of a monbus record (24 bytes / 3 × 64-bit beats) lands
//     in one 64-bit BRAM word.
//   - 32-bit AXIL reads from the host. Address bits [2:0] = byte offset
//     within the host's 32-bit word; bit [2] selects low (0) or high
//     (1) half of the underlying 64-bit BRAM word.
//   - Byte-addressed at both ports. The mapping from byte address to
//     internal BRAM word index strips bits [2:0] on writes (8-byte
//     align) and bits [1:0] on reads (4-byte align).
//   - wr_ptr counter tracks 32-bit-word-equivalents written (each 64-bit
//     write bumps it by 2) so the host's UART-side view of how much
//     capture has happened stays in 32-bit-word units.
//   - "freeze" gates writes (read port is always live).
//   - "overflow" sticky bit if a write happens at the last word slot.
//   - "clear_pulse" zeros wr_ptr/overflow AND wipes the BRAM at FPGA
//     speed. The clear engine walks DEPTH_WORDS/2 64-bit words one per
//     cycle; for the default 64 K 32-bit words (= 32 K 64-bit words)
//     at 100 MHz that's ~328 us. Software issues the pulse, polls
//     o_clear_busy, then starts the next capture.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module debug_sram #(
    // DEPTH_WORDS is in 32-bit-word units (legacy parameter naming kept
    // for backward compat with the harness's DEBUG_SRAM_WORDS parameter
    // and the host's "how many 32-bit words can I address" view). The
    // internal BRAM stores DEPTH_WORDS/2 64-bit words; both AXI ports
    // are 64-bit symmetric, so the host issues DEPTH_WORDS/2 64-bit
    // reads to drain the trace.
    parameter int DEPTH_WORDS = 65536,    // 64K x 32b = 256 KB = 32K x 64b BRAM

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4
) (
    input  logic            aclk,
    input  logic            aresetn,

    input  logic            i_freeze,           // latch: stop writes when high
    input  logic            i_clear_pulse,      // one-cycle: kick off a wipe

    output logic [31:0]     o_wr_ptr,           // 32-bit-word-equiv count since clear
    output logic            o_overflow,         // sticky
    output logic            o_clear_busy,       // 1 while clear engine running

    // =====================================================================
    // Write-only AXI4-Lite slave (from STREAM m_axil_mon, 64-bit data)
    // =====================================================================
    input  logic [31:0]     wr_awaddr,
    input  logic [2:0]      wr_awprot,
    input  logic            wr_awvalid,
    output logic            wr_awready,

    input  logic [63:0]     wr_wdata,
    input  logic [7:0]      wr_wstrb,
    input  logic            wr_wvalid,
    output logic            wr_wready,

    output logic [1:0]      wr_bresp,
    output logic            wr_bvalid,
    input  logic            wr_bready,

    // Read side tied off with DECERR (this AXIL slot is write-only)
    input  logic [31:0]     wr_araddr,
    input  logic [2:0]      wr_arprot,
    input  logic            wr_arvalid,
    output logic            wr_arready,
    output logic [63:0]     wr_rdata,
    output logic [1:0]      wr_rresp,
    output logic            wr_rvalid,
    input  logic            wr_rready,

    // =====================================================================
    // Read-only AXI4-Lite slave (64-bit, from host via the bridge fanout)
    // -- both AXI ports on this SRAM are 64-bit per the monbus-on-AXI rule:
    // every path that collects monbus packets or lets the host read them
    // carries 64-bit beats. The integrator widens upstream as needed
    // (the bridge auto-inserts a 32->64 width converter at the slave port).
    // =====================================================================
    input  logic [31:0]     rd_awaddr,
    input  logic [2:0]      rd_awprot,
    input  logic            rd_awvalid,
    output logic            rd_awready,
    input  logic [63:0]     rd_wdata,
    input  logic [7:0]      rd_wstrb,
    input  logic            rd_wvalid,
    output logic            rd_wready,
    output logic [1:0]      rd_bresp,
    output logic            rd_bvalid,
    input  logic            rd_bready,

    input  logic [31:0]     rd_araddr,
    input  logic [2:0]      rd_arprot,
    input  logic            rd_arvalid,
    output logic            rd_arready,

    output logic [63:0]     rd_rdata,
    output logic [1:0]      rd_rresp,
    output logic            rd_rvalid,
    input  logic            rd_rready
);

    // Internal storage is 64-bit-wide. DEPTH_WORDS_64 = DEPTH_WORDS / 2.
    localparam int DEPTH_WORDS_64 = DEPTH_WORDS / 2;
    localparam int ADDR_BITS_64   = $clog2(DEPTH_WORDS_64);

    // Skid packet widths
    localparam int AW_PKT_W = 32 + 3;             // wr_awaddr + wr_awprot
    localparam int W_PKT_W  = 64 + 8;             // wr_wdata + wr_wstrb
    localparam int B_PKT_W  = 2;                  // wr_bresp
    localparam int AR_PKT_W = 32 + 3;             // rd_araddr + rd_arprot
    localparam int R_PKT_W  = 64 + 2;             // rd_rdata + rd_rresp (64-bit symmetric)

    // =========================================================================
    // BRAM storage (true dual-port, symmetric 64-bit on every AXI port)
    // =========================================================================
    (* ram_style = "block" *)
    logic [63:0] r_mem [DEPTH_WORDS_64];

    // =========================================================================
    // Clear engine: zeros every 64-bit word of r_mem at one word per cycle
    // =========================================================================
    logic                     r_clear_busy;
    logic [ADDR_BITS_64-1:0]  r_clr_idx;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_clear_busy <= 1'b0;
            r_clr_idx    <= '0;
        end else begin
            if (i_clear_pulse) begin
                r_clear_busy <= 1'b1;
                r_clr_idx    <= '0;
            end else if (r_clear_busy) begin
                if (r_clr_idx == ADDR_BITS_64'(DEPTH_WORDS_64 - 1)) begin
                    r_clear_busy <= 1'b0;
                end
                r_clr_idx <= r_clr_idx + 1'b1;
            end
        end
    )

    assign o_clear_busy = r_clear_busy;

    // =========================================================================
    // Write port: AW / W / B skid buffers
    // =========================================================================
    logic                 wfub_awvalid, wfub_awready;
    logic [AW_PKT_W-1:0]  wfub_aw_pkt;
    logic [31:0]          wfub_awaddr;
    logic [2:0]           wfub_awprot;
    assign {wfub_awaddr, wfub_awprot} = wfub_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AW_PKT_W)
    ) u_wr_skid_aw (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (wr_awvalid),
        .wr_ready   (wr_awready),
        .wr_data    ({wr_awaddr, wr_awprot}),
        .count      (),
        .rd_valid   (wfub_awvalid),
        .rd_ready   (wfub_awready),
        .rd_count   (),
        .rd_data    (wfub_aw_pkt)
    );

    logic                wfub_wvalid, wfub_wready;
    logic [W_PKT_W-1:0]  wfub_w_pkt;
    logic [63:0]         wfub_wdata;
    logic [7:0]          wfub_wstrb;
    assign {wfub_wdata, wfub_wstrb} = wfub_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(W_PKT_W)
    ) u_wr_skid_w (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (wr_wvalid),
        .wr_ready   (wr_wready),
        .wr_data    ({wr_wdata, wr_wstrb}),
        .count      (),
        .rd_valid   (wfub_wvalid),
        .rd_ready   (wfub_wready),
        .rd_count   (),
        .rd_data    (wfub_w_pkt)
    );

    logic                wfub_bvalid, wfub_bready;
    logic [B_PKT_W-1:0]  wfub_b_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_B),
        .DATA_WIDTH(B_PKT_W)
    ) u_wr_skid_b (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (wfub_bvalid),
        .wr_ready   (wfub_bready),
        .wr_data    (wfub_b_pkt),
        .count      (),
        .rd_valid   (wr_bvalid),
        .rd_ready   (wr_bready),
        .rd_count   (),
        .rd_data    (wr_bresp)
    );

    // =========================================================================
    // Write engine: consume AW+W, optionally write BRAM, emit B
    //
    // Byte address -> 64-bit BRAM index: strip bits [2:0] (8-byte align).
    // wfub_awaddr[ADDR_BITS_64+2:3] is the BRAM word index.
    // =========================================================================
    typedef enum logic [1:0] {
        WS_IDLE  = 2'd0,
        WS_WRITE = 2'd1,
        WS_BRESP = 2'd2
    } w_state_t;

    w_state_t                 r_wstate;
    logic [ADDR_BITS_64-1:0]  r_w_idx;
    logic [63:0]              r_w_data;
    logic [7:0]               r_w_strb;
    logic                     r_w_did_write;

    // FSM bookkeeping only -- the BRAM write itself moves into its own
    // process below so Vivado can infer block RAM (one write port per
    // always block).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wstate      <= WS_IDLE;
            r_w_idx       <= '0;
            r_w_data      <= '0;
            r_w_strb      <= '0;
            r_w_did_write <= 1'b0;
        end else begin
            case (r_wstate)
                WS_IDLE: begin
                    if (!r_clear_busy && wfub_awvalid && wfub_wvalid) begin
                        r_w_idx       <= wfub_awaddr[ADDR_BITS_64+2:3];
                        r_w_data      <= wfub_wdata;
                        r_w_strb      <= wfub_wstrb;
                        r_w_did_write <= ~i_freeze;
                        r_wstate      <= WS_WRITE;
                    end
                end
                WS_WRITE: r_wstate <= WS_BRESP;
                WS_BRESP: if (wfub_bready) r_wstate <= WS_IDLE;
                default:  r_wstate <= WS_IDLE;
            endcase
        end
    )

    // ---------------------------------------------------------------------
    // BRAM write port -- single always_ff with a muxed input, per Xilinx
    // BRAM inference rules. AXIL backpressure (see wfub_awready /
    // wfub_wready below) keeps the FSM in WS_IDLE during a wipe, so
    // r_clear_busy and (r_wstate == WS_WRITE && r_w_did_write) are
    // mutually exclusive.
    // ---------------------------------------------------------------------
    logic                     w_bram_we;
    logic [ADDR_BITS_64-1:0]  w_bram_addr;
    logic [63:0]              w_bram_data;
    logic [7:0]               w_bram_strb;

    always_comb begin
        if (r_clear_busy) begin
            w_bram_we   = 1'b1;
            w_bram_addr = r_clr_idx;
            w_bram_data = 64'h0;
            w_bram_strb = 8'hFF;
        end else if ((r_wstate == WS_WRITE) && r_w_did_write) begin
            w_bram_we   = 1'b1;
            w_bram_addr = r_w_idx;
            w_bram_data = r_w_data;
            w_bram_strb = r_w_strb;
        end else begin
            w_bram_we   = 1'b0;
            w_bram_addr = '0;
            w_bram_data = '0;
            w_bram_strb = '0;
        end
    end

    always_ff @(posedge aclk) begin
        if (w_bram_we) begin
            for (int b = 0; b < 8; b++) begin
                if (w_bram_strb[b]) r_mem[w_bram_addr][8*b +: 8] <= w_bram_data[8*b +: 8];
            end
        end
    end

    // AXIL backpressure during clear.
    assign wfub_awready = !r_clear_busy && (r_wstate == WS_IDLE) && wfub_wvalid;
    assign wfub_wready  = !r_clear_busy && (r_wstate == WS_IDLE) && wfub_awvalid;
    assign wfub_bvalid  = (r_wstate == WS_BRESP);
    assign wfub_b_pkt   = 2'b00;  // OKAY

    // =========================================================================
    // Write port read side: tie off with DECERR (write-only slot)
    // =========================================================================
    assign wr_arready = 1'b1;
    logic r_wr_ar_latch;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_ar_latch <= 1'b0;
        end else begin
            if (wr_arvalid && wr_arready) r_wr_ar_latch <= 1'b1;
            else if (wr_rvalid && wr_rready) r_wr_ar_latch <= 1'b0;
        end
    )
    assign wr_rvalid = r_wr_ar_latch;
    assign wr_rdata  = 64'hDEAD_DEAD_DEAD_DEAD;
    assign wr_rresp  = 2'b11;

    // =========================================================================
    // Pointer/overflow bookkeeping. Counts 32-bit-word-equivalents so the
    // host can compare against its 32-bit-word view of the trace. Each
    // 64-bit AXIL write bumps the counter by 2.
    // =========================================================================
    logic [31:0] r_wr_ptr;
    logic        r_overflow;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_ptr   <= '0;
            r_overflow <= 1'b0;
        end else begin
            if (i_clear_pulse) begin
                r_wr_ptr   <= '0;
                r_overflow <= 1'b0;
            end else if ((r_wstate == WS_WRITE) && r_w_did_write) begin
                if (r_wr_ptr >= 32'(DEPTH_WORDS - 2)) begin
                    r_overflow <= 1'b1;
                end else begin
                    r_wr_ptr <= r_wr_ptr + 32'd2;
                end
            end
        end
    )

    assign o_wr_ptr   = r_wr_ptr;
    assign o_overflow = r_overflow;

    // =========================================================================
    // Read port: AR / R skid buffers (32-bit host-facing data)
    // =========================================================================
    logic                 rfub_arvalid, rfub_arready;
    logic [AR_PKT_W-1:0]  rfub_ar_pkt;
    logic [31:0]          rfub_araddr;
    logic [2:0]           rfub_arprot;
    assign {rfub_araddr, rfub_arprot} = rfub_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR_PKT_W)
    ) u_rd_skid_ar (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (rd_arvalid),
        .wr_ready   (rd_arready),
        .wr_data    ({rd_araddr, rd_arprot}),
        .count      (),
        .rd_valid   (rfub_arvalid),
        .rd_ready   (rfub_arready),
        .rd_count   (),
        .rd_data    (rfub_ar_pkt)
    );

    logic                rfub_rvalid, rfub_rready;
    logic [R_PKT_W-1:0]  rfub_r_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_R),
        .DATA_WIDTH(R_PKT_W)
    ) u_rd_skid_r (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (rfub_rvalid),
        .wr_ready   (rfub_rready),
        .wr_data    (rfub_r_pkt),
        .count      (),
        .rd_valid   (rd_rvalid),
        .rd_ready   (rd_rready),
        .rd_count   (),
        .rd_data    ({rd_rdata, rd_rresp})
    );

    // =========================================================================
    // Read engine: 1-cycle BRAM read returning the full 64-bit word per beat
    // (symmetric with the 64-bit write side -- no slice counter, no half-word
    // muxing). The host-side byte address bits [ADDR_BITS_64+3-1:3] select
    // the 64-bit BRAM word; bits [2:0] within the word are don't-care for
    // aligned AXIL reads.
    // =========================================================================
    typedef enum logic [1:0] {
        RS_IDLE  = 2'd0,
        RS_RD1   = 2'd1,
        RS_RRESP = 2'd2
    } r_state_t;

    r_state_t                 r_rstate;
    logic [63:0]              r_r_data;       // full 64-bit BRAM word
    logic [ADDR_BITS_64-1:0]  r_r_idx;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= RS_IDLE;
            r_r_data <= '0;
            r_r_idx  <= '0;
        end else begin
            case (r_rstate)
                RS_IDLE: begin
                    if (rfub_arvalid) begin
                        // Bits [ADDR_BITS_64+2:3] of the byte address index
                        // the 64-bit BRAM word.
                        r_r_idx  <= rfub_araddr[ADDR_BITS_64+2:3];
                        r_rstate <= RS_RD1;
                    end
                end
                RS_RD1: begin
                    r_r_data <= r_mem[r_r_idx];
                    r_rstate <= RS_RRESP;
                end
                RS_RRESP: begin
                    if (rfub_rready) r_rstate <= RS_IDLE;
                end
                default: r_rstate <= RS_IDLE;
            endcase
        end
    )

    assign rfub_arready = !r_clear_busy && (r_rstate == RS_IDLE);
    assign rfub_rvalid  = (r_rstate == RS_RRESP);
    assign rfub_r_pkt   = {r_r_data, 2'b00};  // {64-bit data, OKAY}

    // =========================================================================
    // Read port write side: DECERR (host cannot write via this slot)
    // =========================================================================
    assign rd_awready = 1'b1;
    assign rd_wready  = 1'b1;
    logic r_rd_bvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_bvalid <= 1'b0;
        end else begin
            if (rd_awvalid && rd_wvalid && !r_rd_bvalid) r_rd_bvalid <= 1'b1;
            else if (rd_bready && r_rd_bvalid)            r_rd_bvalid <= 1'b0;
        end
    )
    assign rd_bvalid = r_rd_bvalid;
    assign rd_bresp  = 2'b11;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, wfub_awprot, rfub_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : debug_sram
