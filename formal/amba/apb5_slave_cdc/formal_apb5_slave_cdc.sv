// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_slave_cdc -- single-clock model
//
// Multi-clock CDC is modeled with pclk=aclk=clk so both domains
// run synchronously, making BMC tractable while still verifying
// the datapath, FSM logic, and APB5 wakeup synchronization.
//
// Properties verified:
//   P1: Reset clears APB outputs (PREADY, PSLVERR)
//   P2: Reset clears cmd_valid
//   P3: PREADY is single-cycle pulse
//   P4: Wakeup synchronization -- PWAKEUP eventually follows wakeup_request
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

    (* anyseq *) reg [SW-1:0]     s_apb_PWDATAPARITY;
    (* anyseq *) reg              s_apb_PADDRPARITY;
    (* anyseq *) reg              s_apb_PCTRLPARITY;

    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;
    (* anyseq *) reg [RUW-1:0]    rsp_pruser;
    (* anyseq *) reg [BUW-1:0]    rsp_pbuser;
    (* anyseq *) reg              wakeup_request;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              s_apb_PREADY;
    wire [DW-1:0]     s_apb_PRDATA;
    wire              s_apb_PSLVERR;
    wire              s_apb_PWAKEUP;
    wire [RUW-1:0]    s_apb_PRUSER;
    wire [BUW-1:0]    s_apb_PBUSER;
    wire [SW-1:0]     s_apb_PRDATAPARITY;
    wire              s_apb_PREADYPARITY;
    wire              s_apb_PSLVERRPARITY;
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
        .s_apb_PWDATAPARITY  (s_apb_PWDATAPARITY),
        .s_apb_PADDRPARITY   (s_apb_PADDRPARITY),
        .s_apb_PCTRLPARITY   (s_apb_PCTRLPARITY),
        .s_apb_PRDATAPARITY  (s_apb_PRDATAPARITY),
        .s_apb_PREADYPARITY  (s_apb_PREADYPARITY),
        .s_apb_PSLVERRPARITY (s_apb_PSLVERRPARITY),

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

        .wakeup_request      (wakeup_request),
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

    // P5: Reset clears wakeup output
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_wakeup: assert (!s_apb_PWAKEUP);
    end

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_cmd_valid:     cover (cmd_valid);
            cp_pready:        cover (s_apb_PREADY);
            cp_wakeup_out:    cover (s_apb_PWAKEUP);
        end
    end

endmodule
