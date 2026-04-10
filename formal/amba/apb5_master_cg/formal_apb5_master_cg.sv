// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_master_cg -- clock-gated APB5 master wrapper
//
// Properties verified (same envelope as apb_master_cg):
//   P1: Reset clears APB outputs and gating
//   P2: PENABLE requires PSEL
//   P3: ACCESS held until PREADY
//   P4: Gating off during in-flight transaction
//   P5: cfg_cg_enable=0 implies no gating

`include "reset_defs.svh"

module formal_apb5_master_cg (
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
    localparam int ICW = 3;

    (* anyseq *) reg             cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]   cfg_cg_idle_count;
    (* anyseq *) reg             cmd_valid;
    (* anyseq *) reg             cmd_pwrite;
    (* anyseq *) reg [AW-1:0]    cmd_paddr;
    (* anyseq *) reg [DW-1:0]    cmd_pwdata;
    (* anyseq *) reg [SW-1:0]    cmd_pstrb;
    (* anyseq *) reg [PW-1:0]    cmd_pprot;
    (* anyseq *) reg [AUW-1:0]   cmd_pauser;
    (* anyseq *) reg [WUW-1:0]   cmd_pwuser;
    (* anyseq *) reg             rsp_ready;
    (* anyseq *) reg [DW-1:0]    m_apb_PRDATA;
    (* anyseq *) reg             m_apb_PSLVERR;
    (* anyseq *) reg             m_apb_PREADY;
    (* anyseq *) reg             m_apb_PWAKEUP;
    (* anyseq *) reg [RUW-1:0]   m_apb_PRUSER;
    (* anyseq *) reg [BUW-1:0]   m_apb_PBUSER;
    (* anyseq *) reg [SW-1:0]    m_apb_PRDATAPARITY;
    (* anyseq *) reg             m_apb_PREADYPARITY;
    (* anyseq *) reg             m_apb_PSLVERRPARITY;

    wire             cmd_ready;
    wire             rsp_valid;
    wire [DW-1:0]    rsp_prdata;
    wire             rsp_pslverr;
    wire             rsp_pwakeup;
    wire [RUW-1:0]   rsp_pruser;
    wire [BUW-1:0]   rsp_pbuser;
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
    wire             apb_clock_gating;

    apb5_master_cg #(
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .PROT_WIDTH(PW),
        .AUSER_WIDTH(AUW),
        .WUSER_WIDTH(WUW),
        .RUSER_WIDTH(RUW),
        .BUSER_WIDTH(BUW),
        .CMD_DEPTH(2),
        .RSP_DEPTH(2),
        .ENABLE_PARITY(0),
        .CG_IDLE_COUNT_WIDTH(ICW)
    ) dut (
        .pclk              (clk),
        .presetn           (rst_n),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .m_apb_PSEL        (m_apb_PSEL),
        .m_apb_PENABLE     (m_apb_PENABLE),
        .m_apb_PADDR       (m_apb_PADDR),
        .m_apb_PWRITE      (m_apb_PWRITE),
        .m_apb_PWDATA      (m_apb_PWDATA),
        .m_apb_PSTRB       (m_apb_PSTRB),
        .m_apb_PPROT       (m_apb_PPROT),
        .m_apb_PAUSER      (m_apb_PAUSER),
        .m_apb_PWUSER      (m_apb_PWUSER),
        .m_apb_PRDATA      (m_apb_PRDATA),
        .m_apb_PSLVERR     (m_apb_PSLVERR),
        .m_apb_PREADY      (m_apb_PREADY),
        .m_apb_PWAKEUP     (m_apb_PWAKEUP),
        .m_apb_PRUSER      (m_apb_PRUSER),
        .m_apb_PBUSER      (m_apb_PBUSER),
        .m_apb_PWDATAPARITY (m_apb_PWDATAPARITY),
        .m_apb_PADDRPARITY  (m_apb_PADDRPARITY),
        .m_apb_PCTRLPARITY  (m_apb_PCTRLPARITY),
        .m_apb_PRDATAPARITY (m_apb_PRDATAPARITY),
        .m_apb_PREADYPARITY (m_apb_PREADYPARITY),
        .m_apb_PSLVERRPARITY(m_apb_PSLVERRPARITY),
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .cmd_pauser        (cmd_pauser),
        .cmd_pwuser        (cmd_pwuser),
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .rsp_pwakeup       (rsp_pwakeup),
        .rsp_pruser        (rsp_pruser),
        .rsp_pbuser        (rsp_pbuser),
        .parity_error_rdata(parity_error_rdata),
        .parity_error_ctrl (parity_error_ctrl),
        .wakeup_pending    (wakeup_pending),
        .apb_clock_gating  (apb_clock_gating)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid < 3) assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 3) assume (rst_n);

    // P1: Reset clears APB outputs and gating
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel:    assert (!m_apb_PSEL);
            ap_reset_pen:     assert (!m_apb_PENABLE);
            ap_reset_no_gate: assert (!apb_clock_gating);
        end
    end

    // P2: PENABLE requires PSEL
    always @(posedge clk) begin
        if (rst_n)
            ap_pen_needs_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    // P3: ACCESS held until PREADY
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // P4: Since master outputs can only change when clock runs, gating cannot
    // be active during an in-flight ACCESS phase (property holds for master).
    always @(posedge clk) begin
        if (f_past_valid > 3 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL) || $past(m_apb_PENABLE))
                ap_no_gate_inflight: assert (!apb_clock_gating);
    end

    // P5: cfg_cg_enable=0 implies no gating
    always @(posedge clk) begin
        if (rst_n && !cfg_cg_enable)
            ap_disabled_no_gate: assert (!apb_clock_gating);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating:       cover (apb_clock_gating);
            cp_ungated_xact: cover (m_apb_PSEL && m_apb_PENABLE && !apb_clock_gating);
            cp_rsp_fire:     cover (rsp_valid && rsp_ready);
        end
    end

endmodule
