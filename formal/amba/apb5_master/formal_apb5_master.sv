// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_master — APB5 protocol compliance plus interface
// parity protection (IHI 0024E ch. 5, issue #102 item 1).
//
// Parity properties are restated independently of the RTL (per byte, as
// "payload plus check bit holds an odd number of ones") and checked:
//   - every requester *CHK the master drives, while its Table 5-1 Check
//     Enable term holds;
//   - each error flag EQUALS the spec-level "an enabled completer check is
//     wrong" condition, so both missed and spurious errors fail the proof.
// AW = 12 and AUW = WUW = RUW = BUW = 4 leave a short top byte, so the
// partial-byte rule is part of the proof.

`include "reset_defs.svh"

module formal_apb5_master #(
    parameter int AW = 12,
    parameter int DW = 32
) (
    input logic clk, input logic rst_n,
    input logic cmd_valid, input logic rsp_ready,
    input logic cmd_pwrite,
    input logic [AW-1:0] cmd_paddr,
    input logic [DW-1:0] cmd_pwdata,
    input logic [DW/8-1:0] cmd_pstrb,
    input logic [2:0] cmd_pprot,
    input logic [3:0] cmd_pauser,
    input logic [3:0] cmd_pwuser,
    input logic m_apb_PREADY, input logic [DW-1:0] m_apb_PRDATA,
    input logic m_apb_PSLVERR,
    input logic [3:0] m_apb_PRUSER,
    input logic [3:0] m_apb_PBUSER,
    // Completer-driven check signals: free, so the flags see every value
    input logic [DW/8-1:0] m_apb_PRDATACHK,
    input logic m_apb_PREADYCHK,
    input logic m_apb_PSLVERRCHK,
    input logic m_apb_PRUSERCHK,
    input logic m_apb_PBUSERCHK
);

    localparam int SW = DW / 8;
    localparam int PW = 3;
    localparam int AUW = 4;
    localparam int WUW = 4;
    localparam int RUW = 4;
    localparam int BUW = 4;
    localparam int ACW = (AW + 7) / 8;

    logic m_apb_PSEL, m_apb_PENABLE, m_apb_PWRITE;
    logic [AW-1:0] m_apb_PADDR;
    logic [DW-1:0] m_apb_PWDATA;
    logic [SW-1:0] m_apb_PSTRB;
    logic [PW-1:0] m_apb_PPROT;
    logic [AUW-1:0] m_apb_PAUSER;
    logic [WUW-1:0] m_apb_PWUSER;
    logic [ACW-1:0] m_apb_PADDRCHK;
    logic m_apb_PCTRLCHK, m_apb_PSELCHK, m_apb_PENABLECHK, m_apb_PSTRBCHK;
    logic [SW-1:0] m_apb_PWDATACHK;
    logic m_apb_PAUSERCHK, m_apb_PWUSERCHK;
    logic m_apb_PWAKEUP, m_apb_PWAKEUPCHK;   // Requester outputs (IHI 0024E 3.7.2)
    logic parity_error_rdata, parity_error_ctrl;
    logic cmd_ready, rsp_valid;

    apb5_master #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .CMD_DEPTH(2), .RSP_DEPTH(2),
        .AUSER_WIDTH(AUW), .WUSER_WIDTH(WUW), .RUSER_WIDTH(RUW), .BUSER_WIDTH(BUW),
        .ENABLE_PARITY(1)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready),
        .cmd_paddr(cmd_paddr), .cmd_pwrite(cmd_pwrite),
        .cmd_pwdata(cmd_pwdata), .cmd_pstrb(cmd_pstrb),
        .cmd_pprot(cmd_pprot), .cmd_pauser(cmd_pauser), .cmd_pwuser(cmd_pwuser),
        .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
        .rsp_prdata(), .rsp_pslverr(), .rsp_pruser(), .rsp_pbuser(),
        .m_apb_PSEL(m_apb_PSEL), .m_apb_PENABLE(m_apb_PENABLE),
        .m_apb_PADDR(m_apb_PADDR), .m_apb_PWRITE(m_apb_PWRITE),
        .m_apb_PWDATA(m_apb_PWDATA), .m_apb_PSTRB(m_apb_PSTRB),
        .m_apb_PPROT(m_apb_PPROT),
        .m_apb_PAUSER(m_apb_PAUSER), .m_apb_PWUSER(m_apb_PWUSER),
        .m_apb_PREADY(m_apb_PREADY), .m_apb_PRDATA(m_apb_PRDATA),
        .m_apb_PSLVERR(m_apb_PSLVERR),
        .m_apb_PRUSER(m_apb_PRUSER), .m_apb_PBUSER(m_apb_PBUSER),
        .m_apb_PWAKEUP(m_apb_PWAKEUP),
        .m_apb_PADDRCHK(m_apb_PADDRCHK), .m_apb_PCTRLCHK(m_apb_PCTRLCHK),
        .m_apb_PSELCHK(m_apb_PSELCHK), .m_apb_PENABLECHK(m_apb_PENABLECHK),
        .m_apb_PWDATACHK(m_apb_PWDATACHK), .m_apb_PSTRBCHK(m_apb_PSTRBCHK),
        .m_apb_PAUSERCHK(m_apb_PAUSERCHK), .m_apb_PWUSERCHK(m_apb_PWUSERCHK),
        .m_apb_PRDATACHK(m_apb_PRDATACHK), .m_apb_PREADYCHK(m_apb_PREADYCHK),
        .m_apb_PSLVERRCHK(m_apb_PSLVERRCHK), .m_apb_PWAKEUPCHK(m_apb_PWAKEUPCHK),
        .m_apb_PRUSERCHK(m_apb_PRUSERCHK), .m_apb_PBUSERCHK(m_apb_PBUSERCHK),
        .parity_error_rdata(parity_error_rdata), .parity_error_ctrl(parity_error_ctrl)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Same APB protocol properties as apb4_master
    always @(posedge clk) begin
        if (rst_n) ap_pen_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel: assert (!m_apb_PSEL);
            ap_reset_pen: assert (!m_apb_PENABLE);
        end
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && !m_apb_PENABLE))
                ap_psel_continues: assert (m_apb_PSEL);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // ------------------------------------------------------------------
    // Interface parity, IHI 0024E 5.3 / Table 5-1. "Odd" here means the
    // payload slice and its check bit together hold an odd number of ones.
    // ------------------------------------------------------------------
    wire [15:0] f_paddr  = {{(16 - AW){1'b0}}, m_apb_PADDR};
    wire f_paddr_ok  = (^{f_paddr[7:0],  m_apb_PADDRCHK[0]}) &&
                       (^{f_paddr[15:8], m_apb_PADDRCHK[1]});
    wire f_pwdata_ok = (^{m_apb_PWDATA[7:0],   m_apb_PWDATACHK[0]}) &&
                       (^{m_apb_PWDATA[15:8],  m_apb_PWDATACHK[1]}) &&
                       (^{m_apb_PWDATA[23:16], m_apb_PWDATACHK[2]}) &&
                       (^{m_apb_PWDATA[31:24], m_apb_PWDATACHK[3]});
    wire f_prdata_ok = (^{m_apb_PRDATA[7:0],   m_apb_PRDATACHK[0]}) &&
                       (^{m_apb_PRDATA[15:8],  m_apb_PRDATACHK[1]}) &&
                       (^{m_apb_PRDATA[23:16], m_apb_PRDATACHK[2]}) &&
                       (^{m_apb_PRDATA[31:24], m_apb_PRDATACHK[3]});

    // Check Enable terms
    wire f_en_sel   = m_apb_PSEL;
    wire f_en_wr    = m_apb_PSEL && m_apb_PWRITE;
    wire f_en_ready = m_apb_PSEL && m_apb_PENABLE;
    wire f_en_rsp   = f_en_ready && m_apb_PREADY;
    wire f_en_rdata = f_en_rsp && !m_apb_PWRITE;

    // Requester checks the master drives
    always @(posedge clk) begin
        if (rst_n) begin
            ap_pselchk: assert (^{m_apb_PSEL, m_apb_PSELCHK});
            ap_pwakeupchk: assert (^{m_apb_PWAKEUP, m_apb_PWAKEUPCHK});
            if (f_en_sel) begin
                ap_paddrchk:   assert (f_paddr_ok);
                ap_pctrlchk:   assert (^{m_apb_PWRITE, m_apb_PPROT, m_apb_PCTRLCHK});
                ap_penablechk: assert (^{m_apb_PENABLE, m_apb_PENABLECHK});
                ap_pauserchk:  assert (^{m_apb_PAUSER, m_apb_PAUSERCHK});
            end
            if (f_en_wr) begin
                ap_pwdatachk:  assert (f_pwdata_ok);
                ap_pstrbchk:   assert (^{m_apb_PSTRB, m_apb_PSTRBCHK});
                ap_pwuserchk:  assert (^{m_apb_PWUSER, m_apb_PWUSERCHK});
            end
        end
    end

    // Error flags equal the spec condition (no misses, no false alarms)
    wire f_rdata_err = f_en_rdata &&
                       (!f_prdata_ok || !(^{m_apb_PRUSER, m_apb_PRUSERCHK}));
    wire f_ctrl_err  = (f_en_ready && !(^{m_apb_PREADY, m_apb_PREADYCHK})) ||
                       (f_en_rsp && (!(^{m_apb_PSLVERR, m_apb_PSLVERRCHK}) ||
                                     !(^{m_apb_PBUSER, m_apb_PBUSERCHK})));
    always @(posedge clk) begin
        if (rst_n) begin
            ap_flag_rdata: assert (parity_error_rdata == f_rdata_err);
            ap_flag_ctrl:  assert (parity_error_ctrl  == f_ctrl_err);
        end
    end

    // ------------------------------------------------------------------
    // PWAKEUP, IHI 0024E 3.7.2 (issue #102 item 7). The master is the
    // Requester and drives it:
    //   - must stay HIGH until PREADY once it and PSEL are HIGH together;
    //     the master never lowers it during a transfer, so: PSEL -> PWAKEUP;
    //   - recommended HIGH at least one cycle before PSEL: checked on every
    //     PSEL rise (this implementation always meets the recommendation);
    //   - LOW out of reset (glitch-free, from a flop).
    // ------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) ap_pwakeup_with_psel: assert (!m_apb_PSEL || m_apb_PWAKEUP);
        if (f_past_valid > 0 && rst_n && $past(rst_n) && m_apb_PSEL && !$past(m_apb_PSEL))
            ap_pwakeup_leads_psel: assert ($past(m_apb_PWAKEUP));
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_pwakeup: assert (!m_apb_PWAKEUP);
    end

    always @(posedge clk) begin
        if (rst_n) begin
            cp_pwakeup_idle: cover (m_apb_PWAKEUP && !m_apb_PSEL);
            cp_setup: cover (m_apb_PSEL && !m_apb_PENABLE);
            cp_access: cover (m_apb_PSEL && m_apb_PENABLE);
            cp_rdata_err: cover (parity_error_rdata);
            cp_ctrl_err_rsp: cover (f_en_rsp && parity_error_ctrl);
            cp_write_access: cover (f_en_wr && m_apb_PENABLE);
        end
    end

endmodule
