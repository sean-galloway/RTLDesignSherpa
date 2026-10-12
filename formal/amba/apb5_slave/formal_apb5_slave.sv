// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_slave — APB5 slave protocol plus interface parity
// protection (IHI 0024E ch. 5, issue #102 item 1).
//
// Parity properties are restated independently of the RTL (per byte, as
// "payload plus check bit holds an odd number of ones") and checked:
//   - every completer *CHK the slave drives, while its Table 5-1 Check
//     Enable term holds;
//   - each error flag EQUALS the spec-level "an enabled requester check is
//     wrong" condition, so both missed and spurious errors fail the proof.
// AW = 12 and the 4-bit user signals leave a short top byte.

`include "reset_defs.svh"

module formal_apb5_slave #(
    parameter int AW = 12,
    parameter int DW = 32
) (
    input logic clk, input logic rst_n,
    input logic s_apb_PSEL, input logic s_apb_PENABLE,
    input logic [AW-1:0] s_apb_PADDR, input logic s_apb_PWRITE,
    input logic [DW-1:0] s_apb_PWDATA, input logic [DW/8-1:0] s_apb_PSTRB,
    input logic [2:0] s_apb_PPROT,
    input logic [3:0] s_apb_PAUSER, input logic [3:0] s_apb_PWUSER,
    // Requester-driven check signals: free, so the flags see every value
    input logic [1:0] s_apb_PADDRCHK,
    input logic s_apb_PCTRLCHK, input logic s_apb_PSELCHK,
    input logic s_apb_PENABLECHK,
    input logic [DW/8-1:0] s_apb_PWDATACHK,
    input logic s_apb_PSTRBCHK,
    input logic s_apb_PAUSERCHK, input logic s_apb_PWUSERCHK,
    input logic rsp_valid, input logic [DW-1:0] rsp_prdata, input logic rsp_pslverr,
    input logic [3:0] rsp_pruser, input logic [3:0] rsp_pbuser,
    input logic s_apb_PWAKEUP,      // Requester-driven (IHI 0024E 3.7.2)
    input logic s_apb_PWAKEUPCHK
);

    localparam int AUW = 4;
    localparam int WUW = 4;
    localparam int RUW = 4;
    localparam int BUW = 4;

    logic s_apb_PREADY;
    logic [DW-1:0] s_apb_PRDATA;
    logic s_apb_PSLVERR;
    logic [RUW-1:0] s_apb_PRUSER;
    logic [BUW-1:0] s_apb_PBUSER;
    logic [DW/8-1:0] s_apb_PRDATACHK;
    logic s_apb_PREADYCHK, s_apb_PSLVERRCHK;
    logic s_apb_PRUSERCHK, s_apb_PBUSERCHK;
    logic parity_error_wdata, parity_error_ctrl;
    logic cmd_valid;

    apb5_slave #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .DEPTH(2), .ENABLE_PARITY(1),
        .AUSER_WIDTH(AUW), .WUSER_WIDTH(WUW), .RUSER_WIDTH(RUW), .BUSER_WIDTH(BUW)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .s_apb_PSEL(s_apb_PSEL), .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY),
        .s_apb_PADDR(s_apb_PADDR), .s_apb_PWRITE(s_apb_PWRITE),
        .s_apb_PWDATA(s_apb_PWDATA), .s_apb_PSTRB(s_apb_PSTRB),
        .s_apb_PPROT(s_apb_PPROT),
        .s_apb_PAUSER(s_apb_PAUSER), .s_apb_PWUSER(s_apb_PWUSER),
        .s_apb_PRDATA(s_apb_PRDATA), .s_apb_PSLVERR(s_apb_PSLVERR),
        .s_apb_PRUSER(s_apb_PRUSER), .s_apb_PBUSER(s_apb_PBUSER),
        .s_apb_PWAKEUP(s_apb_PWAKEUP),
        .s_apb_PADDRCHK(s_apb_PADDRCHK), .s_apb_PCTRLCHK(s_apb_PCTRLCHK),
        .s_apb_PSELCHK(s_apb_PSELCHK), .s_apb_PENABLECHK(s_apb_PENABLECHK),
        .s_apb_PWDATACHK(s_apb_PWDATACHK), .s_apb_PSTRBCHK(s_apb_PSTRBCHK),
        .s_apb_PAUSERCHK(s_apb_PAUSERCHK), .s_apb_PWUSERCHK(s_apb_PWUSERCHK),
        .s_apb_PRDATACHK(s_apb_PRDATACHK), .s_apb_PREADYCHK(s_apb_PREADYCHK),
        .s_apb_PSLVERRCHK(s_apb_PSLVERRCHK), .s_apb_PWAKEUPCHK(s_apb_PWAKEUPCHK),
        .s_apb_PRUSERCHK(s_apb_PRUSERCHK), .s_apb_PBUSERCHK(s_apb_PBUSERCHK),
        .cmd_valid(cmd_valid), .cmd_ready(1'b1),
        .cmd_paddr(), .cmd_pwrite(), .cmd_pwdata(), .cmd_pstrb(), .cmd_pprot(),
        .cmd_pauser(), .cmd_pwuser(),
        .rsp_valid(rsp_valid), .rsp_ready(),
        .rsp_prdata(rsp_prdata), .rsp_pslverr(rsp_pslverr),
        .rsp_pruser(rsp_pruser), .rsp_pbuser(rsp_pbuser),
        .parity_error_wdata(parity_error_wdata), .parity_error_ctrl(parity_error_ctrl)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Well-formed APB master
    always @(posedge clk) begin
        if (rst_n) assume (!s_apb_PENABLE || s_apb_PSEL);
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) assume (!s_apb_PSEL);
    end

    // Reset
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_pready: assert (!s_apb_PREADY);
    end

    // Note: PREADY timing deferred to simulation verification.

    // ------------------------------------------------------------------
    // Interface parity, IHI 0024E 5.3 / Table 5-1. "Odd" here means the
    // payload slice and its check bit together hold an odd number of ones.
    // ------------------------------------------------------------------
    wire [15:0] f_paddr  = {{(16 - AW){1'b0}}, s_apb_PADDR};
    wire f_paddr_ok  = (^{f_paddr[7:0],  s_apb_PADDRCHK[0]}) &&
                       (^{f_paddr[15:8], s_apb_PADDRCHK[1]});
    wire f_pwdata_ok = (^{s_apb_PWDATA[7:0],   s_apb_PWDATACHK[0]}) &&
                       (^{s_apb_PWDATA[15:8],  s_apb_PWDATACHK[1]}) &&
                       (^{s_apb_PWDATA[23:16], s_apb_PWDATACHK[2]}) &&
                       (^{s_apb_PWDATA[31:24], s_apb_PWDATACHK[3]});
    wire f_prdata_ok = (^{s_apb_PRDATA[7:0],   s_apb_PRDATACHK[0]}) &&
                       (^{s_apb_PRDATA[15:8],  s_apb_PRDATACHK[1]}) &&
                       (^{s_apb_PRDATA[23:16], s_apb_PRDATACHK[2]}) &&
                       (^{s_apb_PRDATA[31:24], s_apb_PRDATACHK[3]});

    // Check Enable terms
    wire f_en_sel   = s_apb_PSEL;
    wire f_en_wr    = s_apb_PSEL && s_apb_PWRITE;
    wire f_en_ready = s_apb_PSEL && s_apb_PENABLE;
    wire f_en_rsp   = f_en_ready && s_apb_PREADY;
    wire f_en_rdata = f_en_rsp && !s_apb_PWRITE;

    // Completer checks the slave drives
    always @(posedge clk) begin
        if (rst_n) begin
            if (f_en_ready) ap_preadychk: assert (^{s_apb_PREADY, s_apb_PREADYCHK});
            if (f_en_rsp) begin
                ap_pslverrchk: assert (^{s_apb_PSLVERR, s_apb_PSLVERRCHK});
                ap_pbuserchk:  assert (^{s_apb_PBUSER, s_apb_PBUSERCHK});
            end
            if (f_en_rdata) begin
                ap_prdatachk:  assert (f_prdata_ok);
                ap_pruserchk:  assert (^{s_apb_PRUSER, s_apb_PRUSERCHK});
            end
        end
    end

    // Error flags equal the spec condition (no misses, no false alarms)
    wire f_wdata_err = f_en_wr &&
                       (!f_pwdata_ok || !(^{s_apb_PSTRB, s_apb_PSTRBCHK}) ||
                        !(^{s_apb_PWUSER, s_apb_PWUSERCHK}));
    wire f_ctrl_err  = (f_en_sel && (!f_paddr_ok ||
                                     !(^{s_apb_PWRITE, s_apb_PPROT, s_apb_PCTRLCHK}) ||
                                     !(^{s_apb_PENABLE, s_apb_PENABLECHK}) ||
                                     !(^{s_apb_PAUSER, s_apb_PAUSERCHK}))) ||
                       !(^{s_apb_PSEL, s_apb_PSELCHK}) ||
                       !(^{s_apb_PWAKEUP, s_apb_PWAKEUPCHK});
    always @(posedge clk) begin
        if (rst_n) begin
            ap_flag_wdata: assert (parity_error_wdata == f_wdata_err);
            ap_flag_ctrl:  assert (parity_error_ctrl  == f_ctrl_err);
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            cp_pready: cover (s_apb_PREADY);
            cp_cmd: cover (cmd_valid);
            cp_read_rsp: cover (f_en_rdata);
            cp_wdata_err: cover (parity_error_wdata);
            cp_ctrl_err: cover (f_en_sel && parity_error_ctrl);
        end
    end

endmodule
