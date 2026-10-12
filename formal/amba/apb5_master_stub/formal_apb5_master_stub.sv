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
    // Parity check-signal widths (IHI 0024E Table 5-1)
    localparam int ACW  = (AW + 7) / 8;
    localparam int DCW  = DW / 8;
    localparam int AUCW = (AUW + 7) / 8;
    localparam int WUCW = (WUW + 7) / 8;
    localparam int RUCW = (RUW + 7) / 8;
    localparam int BUCW = (BUW + 7) / 8;
    localparam int CPW = AW + DW + SW + PW + AUW + WUW + 1 + 1 + 1;
    localparam int RPW = DW + RUW + BUW + 1 + 1 + 1;   // data, ruser, buser, pslverr, first, last

    (* anyseq *) reg              cmd_valid;
    (* anyseq *) reg [CPW-1:0]    cmd_data;
    (* anyseq *) reg              rsp_ready;
    (* anyseq *) reg [DW-1:0]     m_apb_PRDATA;
    (* anyseq *) reg              m_apb_PSLVERR;
    (* anyseq *) reg              m_apb_PREADY;
    wire              m_apb_PWAKEUP;        // Requester output (IHI 0024E 3.7.2)
    (* anyseq *) reg [RUW-1:0]    m_apb_PRUSER;
    (* anyseq *) reg [BUW-1:0]    m_apb_PBUSER;
    (* anyseq *) reg [DCW-1:0]    m_apb_PRDATACHK;
    (* anyseq *) reg              m_apb_PREADYCHK;
    (* anyseq *) reg              m_apb_PSLVERRCHK;
    wire              m_apb_PWAKEUPCHK;
    (* anyseq *) reg [RUCW-1:0]   m_apb_PRUSERCHK;
    (* anyseq *) reg [BUCW-1:0]   m_apb_PBUSERCHK;

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
    wire [ACW-1:0]   m_apb_PADDRCHK;
    wire             m_apb_PCTRLCHK;
    wire             m_apb_PSELCHK;
    wire             m_apb_PENABLECHK;
    wire [DCW-1:0]   m_apb_PWDATACHK;
    wire             m_apb_PSTRBCHK;
    wire [AUCW-1:0]  m_apb_PAUSERCHK;
    wire [WUCW-1:0]  m_apb_PWUSERCHK;
    wire             parity_error_rdata, parity_error_ctrl;

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
        .m_apb_PADDRCHK      (m_apb_PADDRCHK),
        .m_apb_PCTRLCHK      (m_apb_PCTRLCHK),
        .m_apb_PSELCHK       (m_apb_PSELCHK),
        .m_apb_PENABLECHK    (m_apb_PENABLECHK),
        .m_apb_PWDATACHK     (m_apb_PWDATACHK),
        .m_apb_PSTRBCHK      (m_apb_PSTRBCHK),
        .m_apb_PAUSERCHK     (m_apb_PAUSERCHK),
        .m_apb_PWUSERCHK     (m_apb_PWUSERCHK),
        .m_apb_PRDATACHK     (m_apb_PRDATACHK),
        .m_apb_PREADYCHK     (m_apb_PREADYCHK),
        .m_apb_PSLVERRCHK    (m_apb_PSLVERRCHK),
        .m_apb_PWAKEUPCHK    (m_apb_PWAKEUPCHK),
        .m_apb_PRUSERCHK     (m_apb_PRUSERCHK),
        .m_apb_PBUSERCHK     (m_apb_PBUSERCHK),
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_data       (cmd_data),
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_data       (rsp_data),
        .parity_error_rdata(parity_error_rdata),
        .parity_error_ctrl (parity_error_ctrl)
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
