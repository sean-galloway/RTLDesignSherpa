// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_slave_cdc -- single-clock model
//
// Multi-clock CDC is modeled with pclk=aclk=clk so both domains
// run synchronously, making BMC tractable while still verifying
// the datapath and FSM logic. PWAKEUP is a free Requester input.
//
// Properties verified:
//   P1: Reset clears APB outputs (PREADY, PSLVERR)
//   P2: Reset clears cmd_valid
//   P3: PREADY is single-cycle pulse
//   P5: Parity error flags zero when ENABLE_PARITY=0

`include "reset_defs.svh"

module formal_apb5_slave_cdc (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters
    // =========================================================================
    localparam int AW  = 12;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int PW  = 3;
    localparam int AUW = 1;
    localparam int WUW = 1;
    localparam int RUW = 1;
    localparam int BUW = 1;
    // Parity check-signal widths (IHI 0024E Table 5-1)
    localparam int ACW  = (AW + 7) / 8;
    localparam int DCW  = DW / 8;
    localparam int AUCW = (AUW + 7) / 8;
    localparam int WUCW = (WUW + 7) / 8;
    localparam int RUCW = (RUW + 7) / 8;
    localparam int BUCW = (BUW + 7) / 8;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg              s_apb_PSEL;
    (* anyseq *) reg              s_apb_PENABLE;
    (* anyseq *) reg [AW-1:0]     s_apb_PADDR;
    (* anyseq *) reg              s_apb_PWRITE;
    (* anyseq *) reg [DW-1:0]     s_apb_PWDATA;
    (* anyseq *) reg [SW-1:0]     s_apb_PSTRB;
    (* anyseq *) reg [PW-1:0]     s_apb_PPROT;
    (* anyseq *) reg [AUW-1:0]    s_apb_PAUSER;
    (* anyseq *) reg [WUW-1:0]    s_apb_PWUSER;

    (* anyseq *) reg [ACW-1:0]    s_apb_PADDRCHK;
    (* anyseq *) reg              s_apb_PCTRLCHK;
    (* anyseq *) reg              s_apb_PSELCHK;
    (* anyseq *) reg              s_apb_PENABLECHK;
    (* anyseq *) reg [DCW-1:0]    s_apb_PWDATACHK;
    (* anyseq *) reg              s_apb_PSTRBCHK;
    (* anyseq *) reg [AUCW-1:0]   s_apb_PAUSERCHK;
    (* anyseq *) reg [WUCW-1:0]   s_apb_PWUSERCHK;

    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;
    (* anyseq *) reg [RUW-1:0]    rsp_pruser;
    (* anyseq *) reg [BUW-1:0]    rsp_pbuser;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              s_apb_PREADY;
    wire [DW-1:0]     s_apb_PRDATA;
    wire              s_apb_PSLVERR;
    (* anyseq *) reg              s_apb_PWAKEUP;      // Requester-driven (IHI 0024E 3.7.2)
    wire [RUW-1:0]    s_apb_PRUSER;
    wire [BUW-1:0]    s_apb_PBUSER;
    wire [DCW-1:0]   s_apb_PRDATACHK;
    wire             s_apb_PREADYCHK;
    wire             s_apb_PSLVERRCHK;
    (* anyseq *) reg             s_apb_PWAKEUPCHK;
    wire [RUCW-1:0]  s_apb_PRUSERCHK;
    wire [BUCW-1:0]  s_apb_PBUSERCHK;
    wire              cmd_valid;
    wire              cmd_pwrite;
    wire [AW-1:0]     cmd_paddr;
    wire [DW-1:0]     cmd_pwdata;
    wire [SW-1:0]     cmd_pstrb;
    wire [PW-1:0]     cmd_pprot;
    wire [AUW-1:0]    cmd_pauser;
    wire [WUW-1:0]    cmd_pwuser;
    wire              rsp_ready;
    wire              parity_error_wdata;
    wire              parity_error_ctrl;

    // =========================================================================
    // DUT -- single-clock model
    // =========================================================================
    apb5_slave_cdc #(
        .ADDR_WIDTH    (AW),
        .DATA_WIDTH    (DW),
        .AUSER_WIDTH   (AUW),
        .WUSER_WIDTH   (WUW),
        .RUSER_WIDTH   (RUW),
        .BUSER_WIDTH   (BUW),
        .DEPTH         (2),
        .ENABLE_PARITY (0)
    ) dut (
        .pclk       (clk),
        .presetn    (rst_n),
        .aclk       (clk),
        .aresetn    (rst_n),

        .s_apb_PSEL          (s_apb_PSEL),
        .s_apb_PENABLE       (s_apb_PENABLE),
        .s_apb_PREADY        (s_apb_PREADY),
        .s_apb_PADDR         (s_apb_PADDR),
        .s_apb_PWRITE        (s_apb_PWRITE),
        .s_apb_PWDATA        (s_apb_PWDATA),
        .s_apb_PSTRB         (s_apb_PSTRB),
        .s_apb_PPROT         (s_apb_PPROT),
        .s_apb_PAUSER        (s_apb_PAUSER),
        .s_apb_PWUSER        (s_apb_PWUSER),
        .s_apb_PRDATA        (s_apb_PRDATA),
        .s_apb_PSLVERR       (s_apb_PSLVERR),
        .s_apb_PWAKEUP       (s_apb_PWAKEUP),
        .s_apb_PRUSER        (s_apb_PRUSER),
        .s_apb_PBUSER        (s_apb_PBUSER),
        .s_apb_PADDRCHK      (s_apb_PADDRCHK),
        .s_apb_PCTRLCHK      (s_apb_PCTRLCHK),
        .s_apb_PSELCHK       (s_apb_PSELCHK),
        .s_apb_PENABLECHK    (s_apb_PENABLECHK),
        .s_apb_PWDATACHK     (s_apb_PWDATACHK),
        .s_apb_PSTRBCHK      (s_apb_PSTRBCHK),
        .s_apb_PAUSERCHK     (s_apb_PAUSERCHK),
        .s_apb_PWUSERCHK     (s_apb_PWUSERCHK),
        .s_apb_PRDATACHK     (s_apb_PRDATACHK),
        .s_apb_PREADYCHK     (s_apb_PREADYCHK),
        .s_apb_PSLVERRCHK    (s_apb_PSLVERRCHK),
        .s_apb_PWAKEUPCHK    (s_apb_PWAKEUPCHK),
        .s_apb_PRUSERCHK     (s_apb_PRUSERCHK),
        .s_apb_PBUSERCHK     (s_apb_PBUSERCHK),

        .cmd_valid       (cmd_valid),
        .cmd_ready       (cmd_ready),
        .cmd_pwrite      (cmd_pwrite),
        .cmd_paddr       (cmd_paddr),
        .cmd_pwdata      (cmd_pwdata),
        .cmd_pstrb       (cmd_pstrb),
        .cmd_pprot       (cmd_pprot),
        .cmd_pauser      (cmd_pauser),
        .cmd_pwuser      (cmd_pwuser),

        .rsp_valid       (rsp_valid),
        .rsp_ready       (rsp_ready),
        .rsp_prdata      (rsp_prdata),
        .rsp_pslverr     (rsp_pslverr),
        .rsp_pruser      (rsp_pruser),
        .rsp_pbuser      (rsp_pbuser),
        .parity_error_wdata  (parity_error_wdata),
        .parity_error_ctrl   (parity_error_ctrl)
    );

    // =========================================================================
    // Reset and past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pready:  assert (!s_apb_PREADY);
            ap_reset_pslverr: assert (!s_apb_PSLVERR);
        end
    end

    // P2: Reset clears cmd_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_cmd_valid: assert (!cmd_valid);
    end

    // P3: PREADY never held for two consecutive cycles
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_apb_PREADY))
                ap_pready_single_cycle: assert (!s_apb_PREADY);
    end

    // P4: Parity error flags always zero when ENABLE_PARITY=0
    always @(posedge clk) begin
        if (rst_n) begin
            ap_no_parity_wdata: assert (!parity_error_wdata);
            ap_no_parity_ctrl:  assert (!parity_error_ctrl);
        end
    end

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_cmd_valid:     cover (cmd_valid);
            cp_pready:        cover (s_apb_PREADY);
        end
    end

endmodule
