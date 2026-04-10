// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: axil2apb
// Purpose: AXI4-Lite slave to APB4 master bridge.
//
// Receives AXI4-Lite read or write transactions and issues them as APB4
// transactions on the downstream APB master interface. Handles one
// transaction at a time (blocking); sufficient for the STREAM config path
// driven from a slow UART host.
//
// Every external AXI4-Lite channel is isolated with a gaxi_skid_buffer
// for timing closure. The APB master port is not buffered (APB is a
// non-pipelined setup/access protocol; skid semantics don't apply).
//
// Only one channel (read OR write) is active at a time. A simple FSM
// executes the APB setup -> access phases and emits the AXIL B/R response
// when the APB slave completes.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil2apb #(
    parameter int AXIL_AW = 32,
    parameter int AXIL_DW = 32,
    parameter int APB_AW  = 12,
    parameter int APB_DW  = 32,

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2
) (
    input  logic              aclk,
    input  logic              aresetn,

    // =====================================================================
    // AXI4-Lite Slave
    // =====================================================================
    input  logic [AXIL_AW-1:0]   s_axil_awaddr,
    input  logic [2:0]           s_axil_awprot,
    input  logic                 s_axil_awvalid,
    output logic                 s_axil_awready,

    input  logic [AXIL_DW-1:0]   s_axil_wdata,
    input  logic [AXIL_DW/8-1:0] s_axil_wstrb,
    input  logic                 s_axil_wvalid,
    output logic                 s_axil_wready,

    output logic [1:0]           s_axil_bresp,
    output logic                 s_axil_bvalid,
    input  logic                 s_axil_bready,

    input  logic [AXIL_AW-1:0]   s_axil_araddr,
    input  logic [2:0]           s_axil_arprot,
    input  logic                 s_axil_arvalid,
    output logic                 s_axil_arready,

    output logic [AXIL_DW-1:0]   s_axil_rdata,
    output logic [1:0]           s_axil_rresp,
    output logic                 s_axil_rvalid,
    input  logic                 s_axil_rready,

    // =====================================================================
    // APB4 Master
    // =====================================================================
    output logic [APB_AW-1:0]    m_apb_paddr,
    output logic                 m_apb_psel,
    output logic                 m_apb_penable,
    output logic                 m_apb_pwrite,
    output logic [APB_DW-1:0]    m_apb_pwdata,
    output logic [APB_DW/8-1:0]  m_apb_pstrb,
    input  logic [APB_DW-1:0]    m_apb_prdata,
    input  logic                 m_apb_pready,
    input  logic                 m_apb_pslverr
);

    localparam int AW_PKT_W = AXIL_AW + 3;
    localparam int W_PKT_W  = AXIL_DW + (AXIL_DW/8);
    localparam int B_PKT_W  = 2;
    localparam int AR_PKT_W = AXIL_AW + 3;
    localparam int R_PKT_W  = AXIL_DW + 2;

    // =========================================================================
    // AW / W / B skid buffers
    // =========================================================================
    logic                 int_awvalid, int_awready;
    logic [AW_PKT_W-1:0]  int_aw_pkt;
    logic [AXIL_AW-1:0]   int_awaddr;
    logic [2:0]           int_awprot;
    assign {int_awaddr, int_awprot} = int_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AW_PKT_W)
    ) u_skid_aw (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_axil_awvalid), .wr_ready(s_axil_awready),
        .wr_data ({s_axil_awaddr, s_axil_awprot}),
        .count   (),
        .rd_valid(int_awvalid), .rd_ready(int_awready),
        .rd_count(), .rd_data(int_aw_pkt)
    );

    logic                int_wvalid, int_wready;
    logic [W_PKT_W-1:0]  int_w_pkt;
    logic [AXIL_DW-1:0]  int_wdata;
    logic [AXIL_DW/8-1:0] int_wstrb;
    assign {int_wdata, int_wstrb} = int_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(W_PKT_W)
    ) u_skid_w (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_axil_wvalid), .wr_ready(s_axil_wready),
        .wr_data ({s_axil_wdata, s_axil_wstrb}),
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
        .rd_valid(s_axil_bvalid), .rd_ready(s_axil_bready),
        .rd_count(), .rd_data(s_axil_bresp)
    );

    // =========================================================================
    // AR / R skid buffers
    // =========================================================================
    logic                 int_arvalid, int_arready;
    logic [AR_PKT_W-1:0]  int_ar_pkt;
    logic [AXIL_AW-1:0]   int_araddr;
    logic [2:0]           int_arprot;
    assign {int_araddr, int_arprot} = int_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR_PKT_W)
    ) u_skid_ar (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_axil_arvalid), .wr_ready(s_axil_arready),
        .wr_data ({s_axil_araddr, s_axil_arprot}),
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
        .rd_valid(s_axil_rvalid), .rd_ready(s_axil_rready),
        .rd_count(), .rd_data({s_axil_rdata, s_axil_rresp})
    );

    // =========================================================================
    // APB FSM (operates on skid-buffer outputs)
    // =========================================================================
    typedef enum logic [2:0] {
        S_IDLE   = 3'd0,
        S_CAPW   = 3'd1,   // AW seen, waiting for W
        S_SETUP  = 3'd2,
        S_ACCESS = 3'd3,
        S_BRESP  = 3'd4,
        S_RRESP  = 3'd5
    } state_t;

    state_t r_state;
    logic          r_is_write;
    logic [APB_AW-1:0]    r_paddr;
    logic [APB_DW-1:0]    r_pwdata;
    logic [APB_DW/8-1:0]  r_pstrb;
    logic [APB_DW-1:0]    r_prdata;
    logic [1:0]           r_resp;

    wire [APB_AW-1:0] w_wr_paddr = int_awaddr[APB_AW-1:0];
    wire [APB_AW-1:0] w_rd_paddr = int_araddr[APB_AW-1:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state    <= S_IDLE;
            r_is_write <= 1'b0;
            r_paddr    <= '0;
            r_pwdata   <= '0;
            r_pstrb    <= '0;
            r_prdata   <= '0;
            r_resp     <= 2'b00;
        end else begin
            case (r_state)
                S_IDLE: begin
                    if (int_awvalid) begin
                        r_is_write <= 1'b1;
                        r_paddr    <= w_wr_paddr;
                        if (int_wvalid) begin
                            r_pwdata <= int_wdata;
                            r_pstrb  <= int_wstrb;
                            r_state  <= S_SETUP;
                        end else begin
                            r_state <= S_CAPW;
                        end
                    end else if (int_arvalid) begin
                        r_is_write <= 1'b0;
                        r_paddr    <= w_rd_paddr;
                        r_state    <= S_SETUP;
                    end
                end

                S_CAPW: begin
                    if (int_wvalid) begin
                        r_pwdata <= int_wdata;
                        r_pstrb  <= int_wstrb;
                        r_state  <= S_SETUP;
                    end
                end

                S_SETUP: begin
                    r_state <= S_ACCESS;
                end

                S_ACCESS: begin
                    if (m_apb_pready) begin
                        r_resp   <= m_apb_pslverr ? 2'b10 : 2'b00;
                        r_prdata <= m_apb_prdata;
                        r_state  <= r_is_write ? S_BRESP : S_RRESP;
                    end
                end

                S_BRESP: begin
                    if (int_bready) r_state <= S_IDLE;
                end

                S_RRESP: begin
                    if (int_rready) r_state <= S_IDLE;
                end

                default: r_state <= S_IDLE;
            endcase
        end
    )

    // Skid-side handshakes (operate on int_* wires)
    assign int_awready = (r_state == S_IDLE);
    assign int_wready  = (r_state == S_IDLE && int_awvalid) || (r_state == S_CAPW);
    assign int_bvalid  = (r_state == S_BRESP);
    assign int_b_pkt   = r_resp;

    assign int_arready = (r_state == S_IDLE) && !int_awvalid;
    assign int_rvalid  = (r_state == S_RRESP);
    assign int_r_pkt   = {r_prdata, r_resp};

    // APB master drive
    assign m_apb_paddr    = r_paddr;
    assign m_apb_psel     = (r_state == S_SETUP) || (r_state == S_ACCESS);
    assign m_apb_penable  = (r_state == S_ACCESS);
    assign m_apb_pwrite   = r_is_write;
    assign m_apb_pwdata   = r_pwdata;
    assign m_apb_pstrb    = r_pstrb;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : axil2apb
