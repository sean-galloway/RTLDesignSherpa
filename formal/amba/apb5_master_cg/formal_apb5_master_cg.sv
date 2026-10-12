// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_master_cg -- clock-gated APB5 master wrapper
//
// Properties verified (same envelope as apb4_master_cg):
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
    // Parity check-signal widths (IHI 0024E Table 5-1)
    localparam int ACW  = (AW + 7) / 8;
    localparam int DCW  = DW / 8;
    localparam int AUCW = (AUW + 7) / 8;
    localparam int WUCW = (WUW + 7) / 8;
    localparam int RUCW = (RUW + 7) / 8;
    localparam int BUCW = (BUW + 7) / 8;
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
    wire             m_apb_PWAKEUP;        // Requester output (IHI 0024E 3.7.2)
    (* anyseq *) reg [RUW-1:0]   m_apb_PRUSER;
    (* anyseq *) reg [BUW-1:0]   m_apb_PBUSER;
    (* anyseq *) reg [DCW-1:0]    m_apb_PRDATACHK;
    (* anyseq *) reg              m_apb_PREADYCHK;
    (* anyseq *) reg              m_apb_PSLVERRCHK;
    wire              m_apb_PWAKEUPCHK;
    (* anyseq *) reg [RUCW-1:0]   m_apb_PRUSERCHK;
    (* anyseq *) reg [BUCW-1:0]   m_apb_PBUSERCHK;

    wire             cmd_ready;
    wire             rsp_valid;
    wire [DW-1:0]    rsp_prdata;
    wire             rsp_pslverr;
    wire [RUW-1:0]   rsp_pruser;
    wire [BUW-1:0]   rsp_pbuser;
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
    wire             cg_gating;

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
        .rsp_pruser        (rsp_pruser),
        .rsp_pbuser        (rsp_pbuser),
        .parity_error_rdata(parity_error_rdata),
        .parity_error_ctrl (parity_error_ctrl),
        .cg_gating  (cg_gating)
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
            ap_reset_no_gate: assert (!cg_gating);
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
            // TWO registered stages sit between bus activity and the gate:
            // the wrapper registers its own wake term (r_wakeup <= ... PSEL ||
            // PENABLE ...), and amba_clock_gate_ctrl registers it again
            // (r_wakeup <= user_valid || axi_valid). So activity at clock N
            // cannot reach the gate decision before N+2, and this checked N+1.
            // The comment above always said "2 cycles"; the code disagreed with
            // it, and the proof failed at step 6 on a design behaving as
            // intended. Same bounded-wake shape the wb4 _cg blocks assert.
            if ($past(m_apb_PSEL, 2) || $past(m_apb_PENABLE, 2))
                ap_no_gate_inflight: assert (!cg_gating);
    end

    // P5: cfg_cg_enable=0 implies no gating
    always @(posedge clk) begin
        if (rst_n && !cfg_cg_enable)
            ap_disabled_no_gate: assert (!cg_gating);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating:       cover (cg_gating);
            cp_ungated_xact: cover (m_apb_PSEL && m_apb_PENABLE && !cg_gating);
            cp_rsp_fire:     cover (rsp_valid && rsp_ready);
        end
    end

endmodule
