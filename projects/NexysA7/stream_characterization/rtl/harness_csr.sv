// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: harness_csr
// Purpose: Control/status registers for the STREAM characterization harness.
//
// Host-visible AXI4-Lite slave with a small set of registers for driving
// and observing the test flow. Separate from the STREAM config registers
// (which live in the STREAM APB space).
//
// Every external AXI4-Lite channel is isolated with a gaxi_skid_buffer
// for timing closure.
//
// Register map (byte offsets from S1 base = 0x0001_0000):
//
//   0x00  CTRL            RW  Control bits
//                              [0]   start           (self-clearing pulse)
//                              [1]   clear_stats     (self-clearing pulse)
//                              [2]   freeze_trace    (latch; stops debug_sram writes)
//                              [3]   soft_reset      (self-clearing pulse)
//
//   0x04  STATUS          R   Status bits
//                              [0]   stream_irq      (latched)
//                              [1]   any_error       (sticky; cleared by clear_stats)
//                              [2]   trace_overflow  (sticky)
//
//   0x08  DBG_WR_PTR      R   Number of 32-bit words written to debug_sram
//   0x0C  DBG_OVERFLOW    R   Sticky overflow flag as a full word
//   0x10  CRC_RD_EXPECTED R   Pseudo-random source CRC (from pattern gen)
//   0x14  CRC_WR_EXPECTED R   Expected CRC at write sink
//   0x18  CRC_WR_COMPUTED R   Actual CRC computed by write sink
//   0x1C  CRC_MATCH       R   [0] = CRC match, [1] = CRC valid
//   0x20  SCRATCH         RW  Free scratchpad for host bring-up / ping test
//   0x24  BUILD_ID        R   Parameter-driven build ID (for host handshake)
//
//   0x28 - 0xFF           --  Reserved (read as 0)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module harness_csr #(
    parameter int AW = 32,
    parameter int DW = 32,
    parameter logic [31:0] BUILD_ID = 32'h5354_5243,  // "STRC"

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2
) (
    input  logic            aclk,
    input  logic            aresetn,

    // =====================================================================
    // AXI4-Lite slave
    // =====================================================================
    input  logic [AW-1:0]   s_awaddr,
    input  logic [2:0]      s_awprot,
    input  logic            s_awvalid,
    output logic            s_awready,

    input  logic [DW-1:0]   s_wdata,
    input  logic [DW/8-1:0] s_wstrb,
    input  logic            s_wvalid,
    output logic            s_wready,

    output logic [1:0]      s_bresp,
    output logic            s_bvalid,
    input  logic            s_bready,

    input  logic [AW-1:0]   s_araddr,
    input  logic [2:0]      s_arprot,
    input  logic            s_arvalid,
    output logic            s_arready,

    output logic [DW-1:0]   s_rdata,
    output logic [1:0]      s_rresp,
    output logic            s_rvalid,
    input  logic            s_rready,

    // =====================================================================
    // Control outputs (to harness)
    // =====================================================================
    output logic            o_start_pulse,
    output logic            o_clear_stats_pulse,
    output logic            o_freeze_trace,
    output logic            o_soft_reset_pulse,

    // =====================================================================
    // Status/statistics inputs (from harness)
    // =====================================================================
    input  logic            i_stream_irq,
    input  logic            i_any_error,
    input  logic [31:0]     i_dbg_wr_ptr,
    input  logic            i_dbg_overflow,
    input  logic [31:0]     i_crc_rd_expected,
    input  logic [31:0]     i_crc_wr_expected,
    input  logic [31:0]     i_crc_wr_computed,
    input  logic            i_crc_valid,
    input  logic            i_crc_match
);

    localparam int AW_PKT_W = AW + 3;
    localparam int W_PKT_W  = DW + (DW/8);
    localparam int B_PKT_W  = 2;
    localparam int AR_PKT_W = AW + 3;
    localparam int R_PKT_W  = DW + 2;

    // =========================================================================
    // AW / W / B skid buffers
    // =========================================================================
    logic                 int_awvalid, int_awready;
    logic [AW_PKT_W-1:0]  int_aw_pkt;
    logic [AW-1:0]        int_awaddr;
    logic [2:0]           int_awprot;
    assign {int_awaddr, int_awprot} = int_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AW_PKT_W)
    ) u_skid_aw (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_awvalid), .wr_ready(s_awready),
        .wr_data ({s_awaddr, s_awprot}),
        .count   (),
        .rd_valid(int_awvalid), .rd_ready(int_awready),
        .rd_count(), .rd_data(int_aw_pkt)
    );

    logic                int_wvalid, int_wready;
    logic [W_PKT_W-1:0]  int_w_pkt;
    logic [DW-1:0]       int_wdata;
    logic [DW/8-1:0]     int_wstrb;
    assign {int_wdata, int_wstrb} = int_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(W_PKT_W)
    ) u_skid_w (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_wvalid), .wr_ready(s_wready),
        .wr_data ({s_wdata, s_wstrb}),
        .count   (),
        .rd_valid(int_wvalid), .rd_ready(int_wready),
        .rd_count(), .rd_data(int_w_pkt)
    );

    logic                int_bvalid, int_bready;
    logic [B_PKT_W-1:0]  int_b_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_B),
        .DATA_WIDTH(B_PKT_W)
    ) u_skid_b (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_bvalid), .wr_ready(int_bready),
        .wr_data (int_b_pkt),
        .count   (),
        .rd_valid(s_bvalid), .rd_ready(s_bready),
        .rd_count(), .rd_data(s_bresp)
    );

    // =========================================================================
    // AR / R skid buffers
    // =========================================================================
    logic                 int_arvalid, int_arready;
    logic [AR_PKT_W-1:0]  int_ar_pkt;
    logic [AW-1:0]        int_araddr;
    logic [2:0]           int_arprot;
    assign {int_araddr, int_arprot} = int_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR_PKT_W)
    ) u_skid_ar (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_arvalid), .wr_ready(s_arready),
        .wr_data ({s_araddr, s_arprot}),
        .count   (),
        .rd_valid(int_arvalid), .rd_ready(int_arready),
        .rd_count(), .rd_data(int_ar_pkt)
    );

    logic                int_rvalid, int_rready;
    logic [R_PKT_W-1:0]  int_r_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_R),
        .DATA_WIDTH(R_PKT_W)
    ) u_skid_r (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_rvalid), .wr_ready(int_rready),
        .wr_data (int_r_pkt),
        .count   (),
        .rd_valid(s_rvalid), .rd_ready(s_rready),
        .rd_count(), .rd_data({s_rdata, s_rresp})
    );

    // =========================================================================
    // Register storage
    // =========================================================================
    logic r_freeze_trace;
    logic r_irq_latched;
    logic r_any_error_sticky;
    logic [31:0] r_scratch;

    logic r_start_pulse;
    logic r_clear_stats_pulse;
    logic r_soft_reset_pulse;

    // =========================================================================
    // Write channel FSM (operates on skid-buffer outputs)
    // =========================================================================
    typedef enum logic [1:0] {
        W_IDLE  = 2'd0,
        W_BRESP = 2'd1
    } w_state_t;

    w_state_t r_wstate;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wstate            <= W_IDLE;
            r_freeze_trace      <= 1'b0;
            r_scratch           <= '0;
            r_start_pulse       <= 1'b0;
            r_clear_stats_pulse <= 1'b0;
            r_soft_reset_pulse  <= 1'b0;
        end else begin
            r_start_pulse       <= 1'b0;
            r_clear_stats_pulse <= 1'b0;
            r_soft_reset_pulse  <= 1'b0;

            case (r_wstate)
                W_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        case (int_awaddr[7:0])
                            8'h00: begin
                                r_start_pulse       <= int_wdata[0];
                                r_clear_stats_pulse <= int_wdata[1];
                                r_freeze_trace      <= int_wdata[2];
                                r_soft_reset_pulse  <= int_wdata[3];
                            end
                            8'h20: r_scratch <= int_wdata;
                            default: ; // ignore
                        endcase
                        r_wstate <= W_BRESP;
                    end
                end
                W_BRESP: begin
                    if (int_bready) r_wstate <= W_IDLE;
                end
                default: r_wstate <= W_IDLE;
            endcase
        end
    )

    assign int_awready = (r_wstate == W_IDLE) && int_wvalid;
    assign int_wready  = (r_wstate == W_IDLE) && int_awvalid;
    assign int_bvalid  = (r_wstate == W_BRESP);
    assign int_b_pkt   = 2'b00;

    // =========================================================================
    // Sticky status bits
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_irq_latched      <= 1'b0;
            r_any_error_sticky <= 1'b0;
        end else begin
            if (r_clear_stats_pulse) begin
                r_irq_latched      <= 1'b0;
                r_any_error_sticky <= 1'b0;
            end else begin
                if (i_stream_irq) r_irq_latched      <= 1'b1;
                if (i_any_error)  r_any_error_sticky <= 1'b1;
            end
        end
    )

    // =========================================================================
    // Read channel FSM
    // =========================================================================
    typedef enum logic [0:0] {
        R_IDLE  = 1'b0,
        R_RRESP = 1'b1
    } r_state_t;

    r_state_t r_rstate;
    logic [31:0] r_rdata;

    logic [7:0] w_raddr;
    assign w_raddr = int_araddr[7:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= R_IDLE;
            r_rdata  <= '0;
        end else begin
            case (r_rstate)
                R_IDLE: begin
                    if (int_arvalid) begin
                        case (w_raddr)
                            8'h00: r_rdata <= {28'd0, 1'b0, r_freeze_trace, 2'b00};
                            8'h04: r_rdata <= {28'd0, 1'b0, i_dbg_overflow, r_any_error_sticky, r_irq_latched};
                            8'h08: r_rdata <= i_dbg_wr_ptr;
                            8'h0C: r_rdata <= {31'd0, i_dbg_overflow};
                            8'h10: r_rdata <= i_crc_rd_expected;
                            8'h14: r_rdata <= i_crc_wr_expected;
                            8'h18: r_rdata <= i_crc_wr_computed;
                            8'h1C: r_rdata <= {30'd0, i_crc_valid, i_crc_match};
                            8'h20: r_rdata <= r_scratch;
                            8'h24: r_rdata <= BUILD_ID;
                            default: r_rdata <= 32'h0000_0000;
                        endcase
                        r_rstate <= R_RRESP;
                    end
                end
                R_RRESP: if (int_rready) r_rstate <= R_IDLE;
                default: r_rstate <= R_IDLE;
            endcase
        end
    )

    assign int_arready = (r_rstate == R_IDLE);
    assign int_rvalid  = (r_rstate == R_RRESP);
    assign int_r_pkt   = {r_rdata, 2'b00};  // rdata + OKAY

    // =========================================================================
    // Outputs
    // =========================================================================
    assign o_start_pulse       = r_start_pulse;
    assign o_clear_stats_pulse = r_clear_stats_pulse;
    assign o_freeze_trace      = r_freeze_trace;
    assign o_soft_reset_pulse  = r_soft_reset_pulse;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_wstrb, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : harness_csr
