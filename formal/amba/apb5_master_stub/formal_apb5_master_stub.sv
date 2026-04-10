// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_master_stub -- packed wrapper around apb5_master
//
// Properties verified:
//   P1: Reset clears APB outputs
//   P2: APB protocol compliance (PENABLE requires PSEL, ACCESS held)

`include "reset_defs.svh"

module formal_apb5_master_stub (
    input logic clk,
    input logic rst_n
);

    localparam int AW  = 12;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int PW  = 3;
    localparam int AUW = 2;
    localparam int WUW = 2;
    localparam int RUW = 2;
    localparam int BUW = 2;
    localparam int CPW = AW + DW + SW + PW + AUW + WUW + 1 + 1 + 1;
    localparam int RPW = DW + RUW + BUW + 1 + 1 + 1 + 1;

    (* anyseq *) reg              cmd_valid;
    (* anyseq *) reg [CPW-1:0]    cmd_data;
    (* anyseq *) reg              rsp_ready;
    (* anyseq *) reg [DW-1:0]     m_apb_PRDATA;
    (* anyseq *) reg              m_apb_PSLVERR;
    (* anyseq *) reg              m_apb_PREADY;
    (* anyseq *) reg              m_apb_PWAKEUP;
    (* anyseq *) reg [RUW-1:0]    m_apb_PRUSER;
    (* anyseq *) reg [BUW-1:0]    m_apb_PBUSER;
    (* anyseq *) reg [SW-1:0]     m_apb_PRDATAPARITY;
    (* anyseq *) reg              m_apb_PREADYPARITY;
    (* anyseq *) reg              m_apb_PSLVERRPARITY;

    wire             cmd_ready;
    wire             rsp_valid;
    wire [RPW-1:0]   rsp_data;
    wire             m_apb_PSEL, m_apb_PENABLE, m_apb_PWRITE;
    wire [AW-1:0]    m_apb_PADDR;
    wire [DW-1:0]    m_apb_PWDATA;
    wire [SW-1:0]    m_apb_PSTRB;
    wire [PW-1:0]    m_apb_PPROT;
    wire [AUW-1:0]   m_apb_PAUSER;
    wire [WUW-1:0]   m_apb_PWUSER;
    wire [SW-1:0]    m_apb_PWDATAPARITY;
    wire             m_apb_PADDRPARITY, m_apb_PCTRLPARITY;
    wire             parity_error_rdata, parity_error_ctrl, wakeup_pending;

    apb5_master_stub #(
        .CMD_DEPTH(2),
        .RSP_DEPTH(2),
        .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW),
        .PROT_WIDTH(PW),
        .AUSER_WIDTH(AUW),
        .WUSER_WIDTH(WUW),
        .RUSER_WIDTH(RUW),
        .BUSER_WIDTH(BUW),
        .ENABLE_PARITY(0)
    ) dut (
        .pclk           (clk),
        .presetn        (rst_n),
        .m_apb_PSEL     (m_apb_PSEL),
        .m_apb_PENABLE  (m_apb_PENABLE),
        .m_apb_PADDR    (m_apb_PADDR),
        .m_apb_PWRITE   (m_apb_PWRITE),
        .m_apb_PWDATA   (m_apb_PWDATA),
        .m_apb_PSTRB    (m_apb_PSTRB),
        .m_apb_PPROT    (m_apb_PPROT),
        .m_apb_PAUSER   (m_apb_PAUSER),
        .m_apb_PWUSER   (m_apb_PWUSER),
        .m_apb_PRDATA   (m_apb_PRDATA),
        .m_apb_PSLVERR  (m_apb_PSLVERR),
        .m_apb_PREADY   (m_apb_PREADY),
        .m_apb_PWAKEUP  (m_apb_PWAKEUP),
        .m_apb_PRUSER   (m_apb_PRUSER),
        .m_apb_PBUSER   (m_apb_PBUSER),
        .m_apb_PWDATAPARITY (m_apb_PWDATAPARITY),
        .m_apb_PADDRPARITY  (m_apb_PADDRPARITY),
        .m_apb_PCTRLPARITY  (m_apb_PCTRLPARITY),
        .m_apb_PRDATAPARITY (m_apb_PRDATAPARITY),
        .m_apb_PREADYPARITY (m_apb_PREADYPARITY),
        .m_apb_PSLVERRPARITY(m_apb_PSLVERRPARITY),
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_data       (cmd_data),
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_data       (rsp_data),
        .parity_error_rdata(parity_error_rdata),
        .parity_error_ctrl (parity_error_ctrl),
        .wakeup_pending    (wakeup_pending)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel: assert (!m_apb_PSEL);
            ap_reset_pen:  assert (!m_apb_PENABLE);
        end
    end

    // P2a: PENABLE requires PSEL
    always @(posedge clk) begin
        if (rst_n)
            ap_pen_needs_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    // P2b: ACCESS held until PREADY
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_setup:    cover (m_apb_PSEL && !m_apb_PENABLE);
            cp_access:   cover (m_apb_PSEL && m_apb_PENABLE);
            cp_complete: cover (m_apb_PSEL && m_apb_PENABLE && m_apb_PREADY);
            cp_rsp:      cover (rsp_valid);
        end
    end

endmodule
