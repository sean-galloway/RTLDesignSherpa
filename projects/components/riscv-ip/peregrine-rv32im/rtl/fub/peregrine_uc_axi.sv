// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_uc_axi
// Purpose: peregrine's uncached data port (PRD P7, §4.5): one 32-bit load
//          or store at a time, as a single-beat AXI4 transaction on the
//          fabric's data width.  It serves the uncached I/O window (the
//          tohost mailbox, the board UART); the cacheable window goes to amber
//          (TASK-001 stage 4).  In the cacheless build (CACHE_EN=0) the
//          TBs drive the Harvard ports directly.
//
//          Request: req_valid / req_ready, ready only when idle, so the
//          port holds exactly one transaction.  Response: rsp_valid is a
//          one-cycle pulse, for a load with rsp_rdata, for a store once B
//          has returned (stores are not posted: a store that retires has
//          reached the fabric).  The consumer always takes it; rsp_rdata
//          is 0 outside the rsp_valid cycle (a consumer that held it
//          longer would be relying on this port, not on the contract a D$
//          also meets).  rsp_err, valid with rsp_valid, is the response's
//          RRESP[1] / BRESP[1]: SLVERR or DECERR (TASK-005).
//
//          A load is AxSIZE 4 bytes at the word address; a store drives its
//          byte strobes on the word's lanes of the AXI_DW beat.  AW and W
//          are presented together and may complete in either order.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - AXI_DW: fabric data width, 32 or 64.
//   - AXI_IW: AXI id width; the port always uses id 0.
//
// Notes:
//   - rresp / bresp: bit 1 is reported on rsp_err (the core's load / store
//     access fault, TASK-005); bit 0 (EXOKAY vs OKAY, SLVERR vs DECERR) is
//     not, since both pairs mean the same here (no exclusive accesses).
//
// Related Modules:
//   - peregrine_top, peregrine_axi4_arb (port 2)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_uc_axi #(
    parameter int AXI_DW = 64,
    parameter int AXI_IW = 4,
    localparam int STRBW = AXI_DW / 8
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                req_valid,
    output logic                req_ready,
    input  logic [31:0]         req_addr,
    input  logic                req_we,
    input  logic [3:0]          req_wstrb,
    input  logic [31:0]         req_wdata,
    output logic                rsp_valid,
    output logic [31:0]         rsp_rdata,
    output logic                rsp_err,

    output logic [AXI_IW-1:0]   m_axi_arid,
    output logic [31:0]         m_axi_araddr,
    output logic [7:0]          m_axi_arlen,
    output logic [2:0]          m_axi_arsize,
    output logic [1:0]          m_axi_arburst,
    output logic                m_axi_arvalid,
    input  logic                m_axi_arready,
    input  logic [AXI_IW-1:0]   m_axi_rid,
    input  logic [AXI_DW-1:0]   m_axi_rdata,
    input  logic [1:0]          m_axi_rresp,
    input  logic                m_axi_rlast,
    input  logic                m_axi_rvalid,
    output logic                m_axi_rready,
    output logic [AXI_IW-1:0]   m_axi_awid,
    output logic [31:0]         m_axi_awaddr,
    output logic [7:0]          m_axi_awlen,
    output logic [2:0]          m_axi_awsize,
    output logic [1:0]          m_axi_awburst,
    output logic                m_axi_awvalid,
    input  logic                m_axi_awready,
    output logic [AXI_DW-1:0]   m_axi_wdata,
    output logic [STRBW-1:0]    m_axi_wstrb,
    output logic                m_axi_wlast,
    output logic                m_axi_wvalid,
    input  logic                m_axi_wready,
    input  logic [AXI_IW-1:0]   m_axi_bid,
    input  logic [1:0]          m_axi_bresp,
    input  logic                m_axi_bvalid,
    output logic                m_axi_bready
);

    localparam int LANES  = AXI_DW / 32;
    localparam int LANE_W = (LANES > 1) ? $clog2(LANES) : 1;
    localparam logic [2:0] SIZE_WORD  = 3'd2;
    localparam logic [1:0] BURST_INCR = 2'b01;

    initial begin
        if (AXI_DW != 32 && AXI_DW != 64)
            $error("peregrine_uc_axi: AXI_DW must be 32 or 64");
    end

    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_RD   = 2'd1,      // AR outstanding or R awaited
        S_WR   = 2'd2       // AW / W outstanding or B awaited
    } state_e;

    state_e      r_state;
    logic [31:0] r_addr;
    logic [3:0]  r_wstrb;
    logic [31:0] r_wdata;
    logic        r_ar_done;
    logic        r_aw_done;
    logic        r_w_done;
    logic        w_req_hs;
    logic [LANE_W-1:0] w_lane;

    assign req_ready = (r_state == S_IDLE);
    assign w_req_hs  = req_valid & req_ready;

    if (LANES > 1) begin : g_lane
        assign w_lane = r_addr[2 +: LANE_W];
    end else begin : g_nolane
        assign w_lane = '0;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state   <= S_IDLE;
            r_addr    <= '0;
            r_wstrb   <= '0;
            r_wdata   <= '0;
            r_ar_done <= 1'b0;
            r_aw_done <= 1'b0;
            r_w_done  <= 1'b0;
            rsp_valid <= 1'b0;
            rsp_rdata <= '0;
            rsp_err   <= 1'b0;
        end else begin
            rsp_valid <= 1'b0;
            rsp_rdata <= '0;        // data only with rsp_valid
            rsp_err   <= 1'b0;
            unique case (r_state)
                S_IDLE: begin
                    if (w_req_hs) begin
                        r_addr    <= {req_addr[31:2], 2'b00};
                        r_wstrb   <= req_wstrb;
                        r_wdata   <= req_wdata;
                        r_ar_done <= 1'b0;
                        r_aw_done <= 1'b0;
                        r_w_done  <= 1'b0;
                        r_state   <= req_we ? S_WR : S_RD;
                    end
                end
                S_RD: begin
                    if (m_axi_arvalid && m_axi_arready) r_ar_done <= 1'b1;
                    if (m_axi_rvalid) begin
                        rsp_valid <= 1'b1;
                        rsp_rdata <= m_axi_rdata[w_lane * 32 +: 32];
                        rsp_err   <= m_axi_rresp[1];
                        r_state   <= S_IDLE;
                    end
                end
                S_WR: begin
                    if (m_axi_awvalid && m_axi_awready) r_aw_done <= 1'b1;
                    if (m_axi_wvalid && m_axi_wready)   r_w_done  <= 1'b1;
                    if (m_axi_bvalid) begin
                        rsp_valid <= 1'b1;
                        rsp_rdata <= '0;
                        rsp_err   <= m_axi_bresp[1];
                        r_state   <= S_IDLE;
                    end
                end
                default: r_state <= S_IDLE;
            endcase
        end
    )

    assign m_axi_arid    = '0;
    assign m_axi_araddr  = r_addr;
    assign m_axi_arlen   = 8'd0;
    assign m_axi_arsize  = SIZE_WORD;
    assign m_axi_arburst = BURST_INCR;
    assign m_axi_arvalid = (r_state == S_RD) & ~r_ar_done;
    assign m_axi_rready  = (r_state == S_RD);

    assign m_axi_awid    = '0;
    assign m_axi_awaddr  = r_addr;
    assign m_axi_awlen   = 8'd0;
    assign m_axi_awsize  = SIZE_WORD;
    assign m_axi_awburst = BURST_INCR;
    assign m_axi_awvalid = (r_state == S_WR) & ~r_aw_done;
    assign m_axi_wvalid  = (r_state == S_WR) & ~r_w_done;
    assign m_axi_wlast   = 1'b1;
    assign m_axi_bready  = (r_state == S_WR);

    always_comb begin
        m_axi_wdata = '0;
        m_axi_wstrb = '0;
        for (int l = 0; l < LANES; l++) begin
            m_axi_wdata[l * 32 +: 32] = r_wdata;
            if (w_lane == LANE_W'(l)) m_axi_wstrb[l * 4 +: 4] = r_wstrb;
        end
    end

    logic w_unused;
    assign w_unused = &{1'b0, m_axi_rid, m_axi_rresp[0], m_axi_rlast, m_axi_bid, m_axi_bresp[0]};

endmodule : peregrine_uc_axi
