// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_xbar_2to4 — 2-master, 4-slave APB crossbar
// Properties: reset clears outputs, arbitration one-hot,
// APB protocol, mutual exclusion

`include "reset_defs.svh"

module formal_apb_xbar_2to4 #(
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

    input logic [DW-1:0]         s0_apb_PRDATA, s1_apb_PRDATA,
    input logic [DW-1:0]         s2_apb_PRDATA, s3_apb_PRDATA,
    input logic                  s0_apb_PSLVERR, s1_apb_PSLVERR,
    input logic                  s2_apb_PSLVERR, s3_apb_PSLVERR,
    input logic                  s0_apb_PREADY, s1_apb_PREADY,
    input logic                  s2_apb_PREADY, s3_apb_PREADY
);

    logic [DW-1:0] m0_apb_PRDATA, m1_apb_PRDATA;
    logic           m0_apb_PSLVERR, m1_apb_PSLVERR;
    logic           m0_apb_PREADY, m1_apb_PREADY;

    logic           s0_apb_PSEL, s1_apb_PSEL, s2_apb_PSEL, s3_apb_PSEL;
    logic           s0_apb_PENABLE, s1_apb_PENABLE, s2_apb_PENABLE, s3_apb_PENABLE;
    logic [AW-1:0]  s0_apb_PADDR, s1_apb_PADDR, s2_apb_PADDR, s3_apb_PADDR;
    logic           s0_apb_PWRITE, s1_apb_PWRITE, s2_apb_PWRITE, s3_apb_PWRITE;
    logic [DW-1:0]  s0_apb_PWDATA, s1_apb_PWDATA, s2_apb_PWDATA, s3_apb_PWDATA;
    logic [SW-1:0]  s0_apb_PSTRB, s1_apb_PSTRB, s2_apb_PSTRB, s3_apb_PSTRB;
    logic [2:0]     s0_apb_PPROT, s1_apb_PPROT, s2_apb_PPROT, s3_apb_PPROT;

    apb_xbar_2to4 #(
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
        .s0_apb_PREADY(s0_apb_PREADY),
        .s1_apb_PSEL(s1_apb_PSEL), .s1_apb_PENABLE(s1_apb_PENABLE),
        .s1_apb_PADDR(s1_apb_PADDR), .s1_apb_PWRITE(s1_apb_PWRITE),
        .s1_apb_PWDATA(s1_apb_PWDATA), .s1_apb_PSTRB(s1_apb_PSTRB),
        .s1_apb_PPROT(s1_apb_PPROT),
        .s1_apb_PRDATA(s1_apb_PRDATA), .s1_apb_PSLVERR(s1_apb_PSLVERR),
        .s1_apb_PREADY(s1_apb_PREADY),
        .s2_apb_PSEL(s2_apb_PSEL), .s2_apb_PENABLE(s2_apb_PENABLE),
        .s2_apb_PADDR(s2_apb_PADDR), .s2_apb_PWRITE(s2_apb_PWRITE),
        .s2_apb_PWDATA(s2_apb_PWDATA), .s2_apb_PSTRB(s2_apb_PSTRB),
        .s2_apb_PPROT(s2_apb_PPROT),
        .s2_apb_PRDATA(s2_apb_PRDATA), .s2_apb_PSLVERR(s2_apb_PSLVERR),
        .s2_apb_PREADY(s2_apb_PREADY),
        .s3_apb_PSEL(s3_apb_PSEL), .s3_apb_PENABLE(s3_apb_PENABLE),
        .s3_apb_PADDR(s3_apb_PADDR), .s3_apb_PWRITE(s3_apb_PWRITE),
        .s3_apb_PWDATA(s3_apb_PWDATA), .s3_apb_PSTRB(s3_apb_PSTRB),
        .s3_apb_PPROT(s3_apb_PPROT),
        .s3_apb_PRDATA(s3_apb_PRDATA), .s3_apb_PSLVERR(s3_apb_PSLVERR),
        .s3_apb_PREADY(s3_apb_PREADY)
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
            ap_rst_s0_psel: assert (!s0_apb_PSEL);
            ap_rst_s1_psel: assert (!s1_apb_PSEL);
            ap_rst_s2_psel: assert (!s2_apb_PSEL);
            ap_rst_s3_psel: assert (!s3_apb_PSEL);
            ap_rst_s0_pen:  assert (!s0_apb_PENABLE);
            ap_rst_s1_pen:  assert (!s1_apb_PENABLE);
            ap_rst_s2_pen:  assert (!s2_apb_PENABLE);
            ap_rst_s3_pen:  assert (!s3_apb_PENABLE);
        end
    end

    // -------------------------------------------------------------------------
    // Property 3: APB protocol on slave side - PENABLE requires PSEL
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_s0_pen_psel: assert (!s0_apb_PENABLE || s0_apb_PSEL);
            ap_s1_pen_psel: assert (!s1_apb_PENABLE || s1_apb_PSEL);
            ap_s2_pen_psel: assert (!s2_apb_PENABLE || s2_apb_PSEL);
            ap_s3_pen_psel: assert (!s3_apb_PENABLE || s3_apb_PSEL);
        end
    end

    // -------------------------------------------------------------------------
    // Property 4: Arbiter grant one-hot per slave
    // Each slave's arbiter should grant at most one master at a time.
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            ap_s0_grant_onehot: assert ($countones(dut.s0_arb_grant) <= 1);
            ap_s1_grant_onehot: assert ($countones(dut.s1_arb_grant) <= 1);
            ap_s2_grant_onehot: assert ($countones(dut.s2_arb_grant) <= 1);
            ap_s3_grant_onehot: assert ($countones(dut.s3_arb_grant) <= 1);
        end
    end

    // -------------------------------------------------------------------------
    // Cover: transactions from both masters to different slaves
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            cp_m0_pready:  cover (m0_apb_PREADY);
            cp_m1_pready:  cover (m1_apb_PREADY);
            cp_s0_psel:    cover (s0_apb_PSEL);
            cp_s1_psel:    cover (s1_apb_PSEL);
            cp_s2_psel:    cover (s2_apb_PSEL);
            cp_s3_psel:    cover (s3_apb_PSEL);
            // Concurrent activity on different slaves
            cp_concurrent: cover (s0_apb_PSEL && s1_apb_PSEL);
        end
    end

endmodule
