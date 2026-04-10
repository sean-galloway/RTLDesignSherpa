// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_master_cg -- clock-gated apb_master wrapper
//
// Properties verified:
//   P1: Reset clears APB outputs
//   P2: PENABLE implies PSEL
//   P3: ACCESS held until PREADY (not gated during in-flight transaction)
//   P4: When a transaction is in progress (PSEL or PENABLE asserted), gating is OFF
//   P5: When cfg_cg_enable=0, apb_clock_gating must be 0 (no gating)
//
// Key CG wrapper check:
//   The wakeup source is (cmd_valid || rsp_valid || PSEL || PENABLE). The register
//   r_wakeup delays this by 1 cycle, and amba_clock_gate_ctrl delays internally
//   by 1 more cycle. But the idle-countdown ensures gating only activates after
//   a quiescent period, so in-flight transactions are protected.

`include "reset_defs.svh"

module formal_apb_master_cg (
    input logic clk,
    input logic rst_n
);

    localparam int AW  = 12;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int PW  = 3;
    localparam int ICW = 3;

    (* anyseq *) reg             cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]   cfg_cg_idle_count;
    (* anyseq *) reg             cmd_valid;
    (* anyseq *) reg             cmd_pwrite;
    (* anyseq *) reg [AW-1:0]    cmd_paddr;
    (* anyseq *) reg [DW-1:0]    cmd_pwdata;
    (* anyseq *) reg [SW-1:0]    cmd_pstrb;
    (* anyseq *) reg [PW-1:0]    cmd_pprot;
    (* anyseq *) reg             rsp_ready;
    (* anyseq *) reg [DW-1:0]    m_apb_PRDATA;
    (* anyseq *) reg             m_apb_PSLVERR;
    (* anyseq *) reg             m_apb_PREADY;

    wire             cmd_ready;
    wire             rsp_valid;
    wire [DW-1:0]    rsp_prdata;
    wire             rsp_pslverr;
    wire             m_apb_PSEL, m_apb_PENABLE, m_apb_PWRITE;
    wire [AW-1:0]    m_apb_PADDR;
    wire [DW-1:0]    m_apb_PWDATA;
    wire [SW-1:0]    m_apb_PSTRB;
    wire [PW-1:0]    m_apb_PPROT;
    wire             apb_clock_gating;

    apb_master_cg #(
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .PROT_WIDTH(PW),
        .CMD_DEPTH(2),
        .RSP_DEPTH(2),
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
        .m_apb_PRDATA      (m_apb_PRDATA),
        .m_apb_PSLVERR     (m_apb_PSLVERR),
        .m_apb_PREADY      (m_apb_PREADY),
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .apb_clock_gating  (apb_clock_gating)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel:     assert (!m_apb_PSEL);
            ap_reset_pen:      assert (!m_apb_PENABLE);
            ap_reset_no_gate:  assert (!apb_clock_gating);
        end
    end

    // P2: PENABLE implies PSEL
    always @(posedge clk) begin
        if (rst_n)
            ap_pen_needs_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    // P3: ACCESS held until PREADY (clock gating must not break this)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // P4: Gating never active during ACCESS phase (PENABLE asserted)
    // Because PSEL/PENABLE feed wakeup, gating cannot happen mid-transaction.
    // Check delayed: 2 cycles after PENABLE seen, gating should still be off.
    always @(posedge clk) begin
        if (f_past_valid > 2 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL) || $past(m_apb_PENABLE))
                ap_no_gate_inflight: assert (!apb_clock_gating);
    end

    // P5: When cfg_cg_enable is deasserted, gating must be 0
    always @(posedge clk) begin
        if (rst_n && !cfg_cg_enable)
            ap_disabled_no_gate: assert (!apb_clock_gating);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating:       cover (apb_clock_gating);
            cp_ungated_xact: cover (m_apb_PSEL && m_apb_PENABLE && !apb_clock_gating);
            cp_cmd_fire:     cover (cmd_valid && cmd_ready);
            cp_rsp_fire:     cover (rsp_valid && rsp_ready);
        end
    end

endmodule
