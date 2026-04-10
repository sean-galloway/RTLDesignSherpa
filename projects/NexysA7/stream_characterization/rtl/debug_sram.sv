// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: debug_sram
// Purpose: 256 KB dual-port debug trace buffer for STREAM characterization.
//
// One port is a write-only AXI4-Lite slave fed by STREAM's m_axil_mon
// master. The other port is a read-only AXI4-Lite slave used by the host
// (via the UART AXIL bridge) to read the captured trace. Because writes
// and reads come from different masters on different ports, no arbitration
// is needed. The underlying BRAM is inferred as dual-port.
//
// Every external AXI4-Lite channel is isolated by a gaxi_skid_buffer for
// timing closure. Six skid buffers total:
//   - Write port: AW, W, B  (to/from STREAM monbus master)
//   - Read port:  AR, R     (to/from host AXIL bridge)
//   - (B response on the read port is tied off with DECERR; no skid needed)
//
// Features:
//   - Byte-addressed 32-bit AXIL interface, 64K x 32-bit = 256 KB
//   - wr_ptr counter tracks number of captured packets since last clear
//   - "freeze" input gates writes (but read port is always live)
//   - "overflow" sticky bit if a write occurs when wr_ptr is saturated

`timescale 1ns / 1ps

`include "reset_defs.svh"

module debug_sram #(
    parameter int DEPTH_WORDS = 65536,    // 64K x 32b = 256 KB

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4
) (
    input  logic            aclk,
    input  logic            aresetn,

    input  logic            i_freeze,           // latch: stop writes when high
    input  logic            i_clear_pulse,      // one-cycle: clear wr_ptr/overflow

    output logic [31:0]     o_wr_ptr,           // words written since last clear
    output logic            o_overflow,         // sticky

    // =====================================================================
    // Write-only AXI4-Lite slave (from STREAM m_axil_mon)
    // =====================================================================
    input  logic [31:0]     wr_awaddr,
    input  logic [2:0]      wr_awprot,
    input  logic            wr_awvalid,
    output logic            wr_awready,

    input  logic [31:0]     wr_wdata,
    input  logic [3:0]      wr_wstrb,
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
    output logic [31:0]     wr_rdata,
    output logic [1:0]      wr_rresp,
    output logic            wr_rvalid,
    input  logic            wr_rready,

    // =====================================================================
    // Read-only AXI4-Lite slave (from host via axil_decode_5s)
    // =====================================================================
    input  logic [31:0]     rd_awaddr,
    input  logic [2:0]      rd_awprot,
    input  logic            rd_awvalid,
    output logic            rd_awready,
    input  logic [31:0]     rd_wdata,
    input  logic [3:0]      rd_wstrb,
    input  logic            rd_wvalid,
    output logic            rd_wready,
    output logic [1:0]      rd_bresp,
    output logic            rd_bvalid,
    input  logic            rd_bready,

    input  logic [31:0]     rd_araddr,
    input  logic [2:0]      rd_arprot,
    input  logic            rd_arvalid,
    output logic            rd_arready,

    output logic [31:0]     rd_rdata,
    output logic [1:0]      rd_rresp,
    output logic            rd_rvalid,
    input  logic            rd_rready
);

    localparam int ADDR_BITS  = $clog2(DEPTH_WORDS);
    localparam int AW_PKT_W   = 32 + 3;           // awaddr + awprot
    localparam int W_PKT_W    = 32 + 4;           // wdata + wstrb
    localparam int B_PKT_W    = 2;                // bresp
    localparam int AR_PKT_W   = 32 + 3;           // araddr + arprot
    localparam int R_PKT_W    = 32 + 2;           // rdata + rresp

    // =========================================================================
    // BRAM storage (true dual-port: write port A, read port B)
    // =========================================================================
    (* ram_style = "block" *)
    logic [31:0] r_mem [DEPTH_WORDS];

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
    logic [31:0]         wfub_wdata;
    logic [3:0]          wfub_wstrb;
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
    // =========================================================================
    typedef enum logic [1:0] {
        WS_IDLE  = 2'd0,
        WS_WRITE = 2'd1,
        WS_BRESP = 2'd2
    } w_state_t;

    w_state_t r_wstate;
    logic [ADDR_BITS-1:0] r_w_idx;
    logic [31:0]          r_w_data;
    logic [3:0]           r_w_strb;
    logic                 r_w_did_write;

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
                    if (wfub_awvalid && wfub_wvalid) begin
                        r_w_idx       <= wfub_awaddr[ADDR_BITS+1:2];
                        r_w_data      <= wfub_wdata;
                        r_w_strb      <= wfub_wstrb;
                        r_w_did_write <= ~i_freeze;
                        r_wstate      <= WS_WRITE;
                    end
                end
                WS_WRITE: begin
                    if (r_w_did_write) begin
                        for (int b = 0; b < 4; b++) begin
                            if (r_w_strb[b]) r_mem[r_w_idx][8*b +: 8] <= r_w_data[8*b +: 8];
                        end
                    end
                    r_wstate <= WS_BRESP;
                end
                WS_BRESP: begin
                    if (wfub_bready) r_wstate <= WS_IDLE;
                end
                default: r_wstate <= WS_IDLE;
            endcase
        end
    )

    assign wfub_awready = (r_wstate == WS_IDLE) && wfub_wvalid;
    assign wfub_wready  = (r_wstate == WS_IDLE) && wfub_awvalid;
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
    assign wr_rdata  = 32'hDEAD_DEAD;
    assign wr_rresp  = 2'b11;

    // =========================================================================
    // Pointer/overflow bookkeeping
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
                if (r_wr_ptr == 32'(DEPTH_WORDS - 1)) begin
                    r_overflow <= 1'b1;
                end else begin
                    r_wr_ptr <= r_wr_ptr + 32'd1;
                end
            end
        end
    )

    assign o_wr_ptr   = r_wr_ptr;
    assign o_overflow = r_overflow;

    // =========================================================================
    // Read port: AR / R skid buffers
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
    // Read engine: 1-cycle BRAM read, 1-cycle response register
    // =========================================================================
    typedef enum logic [1:0] {
        RS_IDLE  = 2'd0,
        RS_RD1   = 2'd1,
        RS_RRESP = 2'd2
    } r_state_t;

    r_state_t r_rstate;
    logic [31:0] r_r_data;
    logic [ADDR_BITS-1:0] r_r_idx;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= RS_IDLE;
            r_r_data <= '0;
            r_r_idx  <= '0;
        end else begin
            case (r_rstate)
                RS_IDLE: begin
                    if (rfub_arvalid) begin
                        r_r_idx  <= rfub_araddr[ADDR_BITS+1:2];
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

    assign rfub_arready = (r_rstate == RS_IDLE);
    assign rfub_rvalid  = (r_rstate == RS_RRESP);
    assign rfub_r_pkt   = {r_r_data, 2'b00};  // OKAY

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
