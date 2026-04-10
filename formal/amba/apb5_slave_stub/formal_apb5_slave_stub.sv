// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_slave_stub -- FSM accepting APB5 transactions
//
// Properties verified:
//   P1: Reset clears s_apb_PREADY
//   P2: s_apb_PREADY is single-cycle pulse

`include "reset_defs.svh"

module formal_apb5_slave_stub (
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
    localparam int CPW = AW + DW + SW + PW + AUW + WUW + 1;
    localparam int RPW = DW + RUW + BUW + 1;

    (* anyseq *) reg              s_apb_PSEL;
    (* anyseq *) reg              s_apb_PENABLE;
    (* anyseq *) reg [AW-1:0]     s_apb_PADDR;
    (* anyseq *) reg              s_apb_PWRITE;
    (* anyseq *) reg [DW-1:0]     s_apb_PWDATA;
    (* anyseq *) reg [SW-1:0]     s_apb_PSTRB;
    (* anyseq *) reg [PW-1:0]     s_apb_PPROT;
    (* anyseq *) reg [AUW-1:0]    s_apb_PAUSER;
    (* anyseq *) reg [WUW-1:0]    s_apb_PWUSER;
    (* anyseq *) reg [SW-1:0]     s_apb_PWDATAPARITY;
    (* anyseq *) reg              s_apb_PADDRPARITY;
    (* anyseq *) reg              s_apb_PCTRLPARITY;
    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg [RPW-1:0]    rsp_data;
    (* anyseq *) reg              wakeup_request;

    wire [DW-1:0]     s_apb_PRDATA;
    wire              s_apb_PSLVERR;
    wire              s_apb_PREADY;
    wire              s_apb_PWAKEUP;
    wire [RUW-1:0]    s_apb_PRUSER;
    wire [BUW-1:0]    s_apb_PBUSER;
    wire [SW-1:0]     s_apb_PRDATAPARITY;
    wire              s_apb_PREADYPARITY;
    wire              s_apb_PSLVERRPARITY;
    wire              cmd_valid;
    wire [CPW-1:0]    cmd_data;
    wire              rsp_ready;
    wire              parity_error_wdata;
    wire              parity_error_ctrl;

    apb5_slave_stub #(
        .DEPTH(2),
        .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW),
        .PROT_WIDTH(PW),
        .AUSER_WIDTH(AUW),
        .WUSER_WIDTH(WUW),
        .RUSER_WIDTH(RUW),
        .BUSER_WIDTH(BUW),
        .ENABLE_PARITY(0)
    ) dut (
        .pclk             (clk),
        .presetn          (rst_n),
        .s_apb_PSEL       (s_apb_PSEL),
        .s_apb_PENABLE    (s_apb_PENABLE),
        .s_apb_PADDR      (s_apb_PADDR),
        .s_apb_PWRITE     (s_apb_PWRITE),
        .s_apb_PWDATA     (s_apb_PWDATA),
        .s_apb_PSTRB      (s_apb_PSTRB),
        .s_apb_PPROT      (s_apb_PPROT),
        .s_apb_PAUSER     (s_apb_PAUSER),
        .s_apb_PWUSER     (s_apb_PWUSER),
        .s_apb_PRDATA     (s_apb_PRDATA),
        .s_apb_PSLVERR    (s_apb_PSLVERR),
        .s_apb_PREADY     (s_apb_PREADY),
        .s_apb_PWAKEUP    (s_apb_PWAKEUP),
        .s_apb_PRUSER     (s_apb_PRUSER),
        .s_apb_PBUSER     (s_apb_PBUSER),
        .s_apb_PWDATAPARITY (s_apb_PWDATAPARITY),
        .s_apb_PADDRPARITY  (s_apb_PADDRPARITY),
        .s_apb_PCTRLPARITY  (s_apb_PCTRLPARITY),
        .s_apb_PRDATAPARITY (s_apb_PRDATAPARITY),
        .s_apb_PREADYPARITY (s_apb_PREADYPARITY),
        .s_apb_PSLVERRPARITY(s_apb_PSLVERRPARITY),
        .cmd_valid        (cmd_valid),
        .cmd_ready        (cmd_ready),
        .cmd_data         (cmd_data),
        .rsp_valid        (rsp_valid),
        .rsp_ready        (rsp_ready),
        .rsp_data         (rsp_data),
        .wakeup_request   (wakeup_request),
        .parity_error_wdata(parity_error_wdata),
        .parity_error_ctrl (parity_error_ctrl)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pready:   assert (!s_apb_PREADY);
            ap_reset_pslverr:  assert (!s_apb_PSLVERR);
        end
    end

    // P2: PREADY pulses
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_apb_PREADY))
                ap_pready_pulse: assert (!s_apb_PREADY);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_cmd:      cover (cmd_valid);
            cp_pready:   cover (s_apb_PREADY);
            cp_full_xact:cover (cmd_valid && rsp_valid);
        end
    end

endmodule
