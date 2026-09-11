// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// apb_cmdrsp_to_axi4: APB command/response stream -> AXI4 requester.
//
// The requester half of an APB-in / AXI4-out converter. apb4_slave and
// apb5_slave already turn the APB completer surface into a one-outstanding
// cmd/rsp pair (PSEL/PENABLE/PREADY handshake, skid buffers, orphan-response
// guard); this module turns each command into exactly one single-beat AXI4
// transaction and its response back into one rsp beat:
//
//   pwrite=1 : AW + W (awlen=0, wlast=1)  ->  B    -> rsp (pslverr = bresp[1])
//   pwrite=0 : AR      (arlen=0)          ->  R    -> rsp (prdata, pslverr = rresp[1])
//
// APB is strictly one-outstanding, so there is never more than one AXI
// transaction in flight and the response needs no ID matching: the AXI ID
// is a constant (DEFAULT_ID). AW and W are presented together and each is
// held until its own handshake, so the requester is legal against a slave
// that accepts W before AW or AW before W.
//
// Both SLVERR and DECERR fold to PSLVERR -- APB has one error bit. The
// USER fields ride through unchanged at AXI_USER_WIDTH; the APB4 wrapper
// ties them to zero, the APB5 wrapper carries PAUSER/PWUSER/PRUSER/PBUSER.
//
// R is drained to RLAST even though every request is one beat, so a slave
// that answers with more beats than asked cannot wedge the port; only the
// first beat's data is returned.

`include "reset_defs.svh"

module apb_cmdrsp_to_axi4 #(
    parameter int AXI_ID_WIDTH    = 1,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int AXI_DATA_WIDTH  = 32,
    parameter int AXI_USER_WIDTH  = 1,
    // Constant ID on every request. APB carries no ID, so one value is
    // enough; the bridge prepends its own master index anyway.
    parameter logic [AXI_ID_WIDTH-1:0] DEFAULT_ID = '0,
    // AxCACHE for every request. Device non-bufferable, the natural
    // attribute for a peripheral-bus requester.
    parameter logic [3:0] DEFAULT_CACHE = 4'b0000,
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic            aclk,
    input  logic            aresetn,

    // Command stream from apb4_slave / apb5_slave
    input  logic            cmd_valid,
    output logic            cmd_ready,
    input  logic            cmd_pwrite,
    input  logic [AW-1:0]   cmd_paddr,
    input  logic [DW-1:0]   cmd_pwdata,
    input  logic [SW-1:0]   cmd_pstrb,
    input  logic [2:0]      cmd_pprot,
    input  logic [UW-1:0]   cmd_auser,
    input  logic [UW-1:0]   cmd_wuser,

    // Response stream back to it
    output logic            rsp_valid,
    input  logic            rsp_ready,
    output logic [DW-1:0]   rsp_prdata,
    output logic            rsp_pslverr,
    output logic [UW-1:0]   rsp_ruser,
    output logic [UW-1:0]   rsp_buser,

    // AXI4 master
    output logic [IW-1:0]   m_axi_awid,
    output logic [AW-1:0]   m_axi_awaddr,
    output logic [7:0]      m_axi_awlen,
    output logic [2:0]      m_axi_awsize,
    output logic [1:0]      m_axi_awburst,
    output logic            m_axi_awlock,
    output logic [3:0]      m_axi_awcache,
    output logic [2:0]      m_axi_awprot,
    output logic [3:0]      m_axi_awqos,
    output logic [3:0]      m_axi_awregion,
    output logic [UW-1:0]   m_axi_awuser,
    output logic            m_axi_awvalid,
    input  logic            m_axi_awready,

    output logic [DW-1:0]   m_axi_wdata,
    output logic [SW-1:0]   m_axi_wstrb,
    output logic            m_axi_wlast,
    output logic [UW-1:0]   m_axi_wuser,
    output logic            m_axi_wvalid,
    input  logic            m_axi_wready,

    input  logic [IW-1:0]   m_axi_bid,
    input  logic [1:0]      m_axi_bresp,
    input  logic [UW-1:0]   m_axi_buser,
    input  logic            m_axi_bvalid,
    output logic            m_axi_bready,

    output logic [IW-1:0]   m_axi_arid,
    output logic [AW-1:0]   m_axi_araddr,
    output logic [7:0]      m_axi_arlen,
    output logic [2:0]      m_axi_arsize,
    output logic [1:0]      m_axi_arburst,
    output logic            m_axi_arlock,
    output logic [3:0]      m_axi_arcache,
    output logic [2:0]      m_axi_arprot,
    output logic [3:0]      m_axi_arqos,
    output logic [3:0]      m_axi_arregion,
    output logic [UW-1:0]   m_axi_aruser,
    output logic            m_axi_arvalid,
    input  logic            m_axi_arready,

    input  logic [IW-1:0]   m_axi_rid,
    input  logic [DW-1:0]   m_axi_rdata,
    input  logic [1:0]      m_axi_rresp,
    input  logic            m_axi_rlast,
    input  logic [UW-1:0]   m_axi_ruser,
    input  logic            m_axi_rvalid,
    output logic            m_axi_rready
);

    // One AXI beat per APB transfer: AxSIZE is the full data width.
    localparam logic [2:0] AXSIZE = 3'($clog2(SW));

    typedef enum logic [2:0] {
        IDLE    = 3'd0,
        WR_REQ  = 3'd1,   // AW and W each held until its handshake
        WR_RESP = 3'd2,   // waiting for B
        RD_REQ  = 3'd3,   // AR held until its handshake
        RD_RESP = 3'd4,   // draining R to RLAST
        RSP     = 3'd5    // rsp beat held until apb slave takes it
    } state_t;

    state_t          r_state;
    logic [AW-1:0]   r_addr;
    logic [DW-1:0]   r_wdata;
    logic [SW-1:0]   r_strb;
    logic [2:0]      r_prot;
    logic [UW-1:0]   r_auser;
    logic [UW-1:0]   r_wuser;
    logic            r_aw_done;
    logic            r_w_done;
    logic            r_first_beat;   // next R beat is the one whose data we keep
    logic [DW-1:0]   r_rdata;
    logic            r_err;
    logic [UW-1:0]   r_ruser;
    logic [UW-1:0]   r_buser;

    // ------------------------------------------------------------------
    // Request payload: constant fields plus the captured command.
    // ------------------------------------------------------------------
    assign m_axi_awid     = DEFAULT_ID;
    assign m_axi_awaddr   = r_addr;
    assign m_axi_awlen    = 8'd0;
    assign m_axi_awsize   = AXSIZE;
    assign m_axi_awburst  = 2'b01;          // INCR
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = DEFAULT_CACHE;
    assign m_axi_awprot   = r_prot;
    assign m_axi_awqos    = 4'd0;
    assign m_axi_awregion = 4'd0;
    assign m_axi_awuser   = r_auser;
    assign m_axi_awvalid  = (r_state == WR_REQ) && !r_aw_done;

    assign m_axi_wdata    = r_wdata;
    assign m_axi_wstrb    = r_strb;
    assign m_axi_wlast    = 1'b1;
    assign m_axi_wuser    = r_wuser;
    assign m_axi_wvalid   = (r_state == WR_REQ) && !r_w_done;

    assign m_axi_bready   = (r_state == WR_RESP);

    assign m_axi_arid     = DEFAULT_ID;
    assign m_axi_araddr   = r_addr;
    assign m_axi_arlen    = 8'd0;
    assign m_axi_arsize   = AXSIZE;
    assign m_axi_arburst  = 2'b01;
    assign m_axi_arlock   = 1'b0;
    assign m_axi_arcache  = DEFAULT_CACHE;
    assign m_axi_arprot   = r_prot;
    assign m_axi_arqos    = 4'd0;
    assign m_axi_arregion = 4'd0;
    assign m_axi_aruser   = r_auser;
    assign m_axi_arvalid  = (r_state == RD_REQ);

    assign m_axi_rready   = (r_state == RD_RESP);

    // A command is taken the cycle it is seen in IDLE.
    assign cmd_ready      = (r_state == IDLE);

    assign rsp_valid      = (r_state == RSP);
    assign rsp_prdata     = r_rdata;
    assign rsp_pslverr    = r_err;
    assign rsp_ruser      = r_ruser;
    assign rsp_buser      = r_buser;

    // The response IDs are not checked: with one transaction outstanding
    // the only response that can arrive is ours. Only the error bit of a
    // response matters to APB (OKAY/EXOKAY both mean success).
    wire unused_resp = &{1'b0, m_axi_bid, m_axi_rid, m_axi_bresp[0], m_axi_rresp[0]};

    // ------------------------------------------------------------------
    // Sequencer
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state      <= IDLE;
            r_addr       <= '0;
            r_wdata      <= '0;
            r_strb       <= '0;
            r_prot       <= '0;
            r_auser      <= '0;
            r_wuser      <= '0;
            r_aw_done    <= 1'b0;
            r_w_done     <= 1'b0;
            r_first_beat <= 1'b1;
            r_rdata      <= '0;
            r_err        <= 1'b0;
            r_ruser      <= '0;
            r_buser      <= '0;
        end else begin
            case (r_state)
                IDLE: begin
                    if (cmd_valid) begin
                        r_addr       <= cmd_paddr;
                        r_wdata      <= cmd_pwdata;
                        r_strb       <= cmd_pstrb;
                        r_prot       <= cmd_pprot;
                        r_auser      <= cmd_auser;
                        r_wuser      <= cmd_wuser;
                        r_aw_done    <= 1'b0;
                        r_w_done     <= 1'b0;
                        r_first_beat <= 1'b1;
                        r_err        <= 1'b0;
                        r_state      <= cmd_pwrite ? WR_REQ : RD_REQ;
                    end
                end

                WR_REQ: begin
                    if (m_axi_awvalid && m_axi_awready) r_aw_done <= 1'b1;
                    if (m_axi_wvalid  && m_axi_wready)  r_w_done  <= 1'b1;
                    if ((r_aw_done || (m_axi_awvalid && m_axi_awready)) &&
                        (r_w_done  || (m_axi_wvalid  && m_axi_wready)))
                        r_state <= WR_RESP;
                end

                WR_RESP: begin
                    if (m_axi_bvalid) begin
                        r_err   <= m_axi_bresp[1];
                        r_buser <= m_axi_buser;
                        r_state <= RSP;
                    end
                end

                RD_REQ: begin
                    if (m_axi_arready) r_state <= RD_RESP;
                end

                RD_RESP: begin
                    if (m_axi_rvalid) begin
                        if (r_first_beat) begin
                            r_rdata      <= m_axi_rdata;
                            r_err        <= m_axi_rresp[1];
                            r_ruser      <= m_axi_ruser;
                            r_first_beat <= 1'b0;
                        end
                        if (m_axi_rlast) r_state <= RSP;
                    end
                end

                RSP: begin
                    if (rsp_ready) r_state <= IDLE;
                end

                // verilator coverage_off
                default: r_state <= IDLE;
                // verilator coverage_on
            endcase
        end
    )

endmodule : apb_cmdrsp_to_axi4
