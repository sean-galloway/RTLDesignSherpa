// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_xbar_2to1 — 2-master, 1-slave APB crossbar
// Properties: reset clears outputs, arbitration one-hot,
// APB protocol, mutual exclusion

`include "reset_defs.svh"

module formal_apb_xbar_2to1 #(
    parameter int AW = 12,
    parameter int DW = 32,
    parameter int SW = DW / 8
) (
    input logic clk,
    input logic rst_n,

    input logic                  m0_apb_PSEL,
    input logic                  m0_apb_PENABLE,
    input logic [AW-1:0]         m0_apb_PADDR,
    input logic                  m0_apb_PWRITE,
    input logic [DW-1:0]         m0_apb_PWDATA,
    input logic [SW-1:0]         m0_apb_PSTRB,
    input logic [2:0]            m0_apb_PPROT,

    input logic                  m1_apb_PSEL,
    input logic                  m1_apb_PENABLE,
    input logic [AW-1:0]         m1_apb_PADDR,
    input logic                  m1_apb_PWRITE,
    input logic [DW-1:0]         m1_apb_PWDATA,
    input logic [SW-1:0]         m1_apb_PSTRB,
    input logic [2:0]            m1_apb_PPROT,

    input logic [DW-1:0]         s0_apb_PRDATA,
    input logic                  s0_apb_PSLVERR,
    input logic                  s0_apb_PREADY
);

    logic [DW-1:0] m0_apb_PRDATA, m1_apb_PRDATA;
    logic           m0_apb_PSLVERR, m1_apb_PSLVERR;
    logic           m0_apb_PREADY, m1_apb_PREADY;

    logic           s0_apb_PSEL;
    logic           s0_apb_PENABLE;
    logic [AW-1:0]  s0_apb_PADDR;
    logic           s0_apb_PWRITE;
    logic [DW-1:0]  s0_apb_PWDATA;
    logic [SW-1:0]  s0_apb_PSTRB;
    logic [2:0]     s0_apb_PPROT;

    apb_xbar_2to1 #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
        .BASE_ADDR({AW{1'b0}})
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .m0_apb_PSEL(m0_apb_PSEL), .m0_apb_PENABLE(m0_apb_PENABLE),
        .m0_apb_PADDR(m0_apb_PADDR), .m0_apb_PWRITE(m0_apb_PWRITE),
        .m0_apb_PWDATA(m0_apb_PWDATA), .m0_apb_PSTRB(m0_apb_PSTRB),
        .m0_apb_PPROT(m0_apb_PPROT),
        .m0_apb_PRDATA(m0_apb_PRDATA), .m0_apb_PSLVERR(m0_apb_PSLVERR),
        .m0_apb_PREADY(m0_apb_PREADY),
        .m1_apb_PSEL(m1_apb_PSEL), .m1_apb_PENABLE(m1_apb_PENABLE),
        .m1_apb_PADDR(m1_apb_PADDR), .m1_apb_PWRITE(m1_apb_PWRITE),
        .m1_apb_PWDATA(m1_apb_PWDATA), .m1_apb_PSTRB(m1_apb_PSTRB),
        .m1_apb_PPROT(m1_apb_PPROT),
        .m1_apb_PRDATA(m1_apb_PRDATA), .m1_apb_PSLVERR(m1_apb_PSLVERR),
        .m1_apb_PREADY(m1_apb_PREADY),
        .s0_apb_PSEL(s0_apb_PSEL), .s0_apb_PENABLE(s0_apb_PENABLE),
        .s0_apb_PADDR(s0_apb_PADDR), .s0_apb_PWRITE(s0_apb_PWRITE),
        .s0_apb_PWDATA(s0_apb_PWDATA), .s0_apb_PSTRB(s0_apb_PSTRB),
        .s0_apb_PPROT(s0_apb_PPROT),
        .s0_apb_PRDATA(s0_apb_PRDATA), .s0_apb_PSLVERR(s0_apb_PSLVERR),
        .s0_apb_PREADY(s0_apb_PREADY)
    );

    // -------------------------------------------------------------------------
    // Past-valid counter and reset
    // -------------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // -------------------------------------------------------------------------
    // Assumptions: well-formed APB masters
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!m0_apb_PENABLE || m0_apb_PSEL);
            assume (!m1_apb_PENABLE || m1_apb_PSEL);
        end
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            assume (!m0_apb_PSEL);
            assume (!m1_apb_PSEL);
        end
    end

    // -------------------------------------------------------------------------
    // Property 1: Reset clears master-side outputs
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_rst_m0_pready:  assert (!m0_apb_PREADY);
            ap_rst_m0_pslverr: assert (!m0_apb_PSLVERR);
            ap_rst_m1_pready:  assert (!m1_apb_PREADY);
            ap_rst_m1_pslverr: assert (!m1_apb_PSLVERR);
        end
    end

    // -------------------------------------------------------------------------
    // Property 2: Reset clears slave-side outputs
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_rst_s0_psel:    assert (!s0_apb_PSEL);
            ap_rst_s0_penable: assert (!s0_apb_PENABLE);
        end
    end

    // -------------------------------------------------------------------------
    // Property 3: Arbitration mutual exclusion
    // Both masters cannot have PREADY simultaneously (single slave).
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_mutual_excl_pready: assert (!(m0_apb_PREADY && m1_apb_PREADY));
        end
    end

    // -------------------------------------------------------------------------
    // Property 4: APB protocol on slave side
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_s_penable_needs_psel: assert (!s0_apb_PENABLE || s0_apb_PSEL);
        end
    end

    // -------------------------------------------------------------------------
    // Property 5: Arbiter grant one-hot
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_grant_onehot: assert ($countones(dut.s0_arb_grant) <= 1);
        end
    end

    // -------------------------------------------------------------------------
    // Cover: transactions from both masters
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            cp_m0_pready:  cover (m0_apb_PREADY);
            cp_m1_pready:  cover (m1_apb_PREADY);
            cp_s0_psel:    cover (s0_apb_PSEL);
        end
    end

endmodule
