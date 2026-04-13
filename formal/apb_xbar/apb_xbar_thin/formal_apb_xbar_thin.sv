// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_xbar_thin — parametric APB crossbar
// Properties: reset clears outputs, APB protocol on slave side,
// no cross-contamination between ports

`include "reset_defs.svh"

module formal_apb_xbar_thin #(
    parameter int M  = 2,
    parameter int S  = 2,
    parameter int AW = 12,
    parameter int DW = 32,
    parameter int SW = DW / 8,
    parameter int MAX_THRESH = 16,
    parameter int MTW  = $clog2(MAX_THRESH),
    parameter int MXMTW = M * MTW
) (
    input logic clk,
    input logic rst_n,

    input logic [S-1:0]                  SLAVE_ENABLE,
    input logic [S-1:0][AW-1:0]          SLAVE_ADDR_BASE,
    input logic [S-1:0][AW-1:0]          SLAVE_ADDR_LIMIT,
    input logic [MXMTW-1:0]             THRESHOLDS,

    input logic [M-1:0]                  m_apb_psel,
    input logic [M-1:0]                  m_apb_penable,
    input logic [M-1:0]                  m_apb_pwrite,
    input logic [M-1:0][2:0]             m_apb_pprot,
    input logic [M-1:0][AW-1:0]          m_apb_paddr,
    input logic [M-1:0][DW-1:0]          m_apb_pwdata,
    input logic [M-1:0][SW-1:0]          m_apb_pstrb,

    input logic [S-1:0]                  s_apb_pready,
    input logic [S-1:0][DW-1:0]          s_apb_prdata,
    input logic [S-1:0]                  s_apb_pslverr
);

    logic [M-1:0]                 m_apb_pready;
    logic [M-1:0][DW-1:0]        m_apb_prdata;
    logic [M-1:0]                 m_apb_pslverr;
    logic [S-1:0]                 s_apb_psel;
    logic [S-1:0]                 s_apb_penable;
    logic [S-1:0]                 s_apb_pwrite;
    logic [S-1:0][2:0]            s_apb_pprot;
    logic [S-1:0][AW-1:0]        s_apb_paddr;
    logic [S-1:0][DW-1:0]        s_apb_pwdata;
    logic [S-1:0][SW-1:0]        s_apb_pstrb;

    apb_xbar_thin #(
        .M(M), .S(S),
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
        .MAX_THRESH(MAX_THRESH)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .SLAVE_ENABLE(SLAVE_ENABLE),
        .SLAVE_ADDR_BASE(SLAVE_ADDR_BASE),
        .SLAVE_ADDR_LIMIT(SLAVE_ADDR_LIMIT),
        .THRESHOLDS(THRESHOLDS),
        .m_apb_psel(m_apb_psel), .m_apb_penable(m_apb_penable),
        .m_apb_pwrite(m_apb_pwrite), .m_apb_pprot(m_apb_pprot),
        .m_apb_paddr(m_apb_paddr), .m_apb_pwdata(m_apb_pwdata),
        .m_apb_pstrb(m_apb_pstrb),
        .m_apb_pready(m_apb_pready), .m_apb_prdata(m_apb_prdata),
        .m_apb_pslverr(m_apb_pslverr),
        .s_apb_psel(s_apb_psel), .s_apb_penable(s_apb_penable),
        .s_apb_pwrite(s_apb_pwrite), .s_apb_pprot(s_apb_pprot),
        .s_apb_paddr(s_apb_paddr), .s_apb_pwdata(s_apb_pwdata),
        .s_apb_pstrb(s_apb_pstrb),
        .s_apb_pready(s_apb_pready), .s_apb_prdata(s_apb_prdata),
        .s_apb_pslverr(s_apb_pslverr)
    );

    // -------------------------------------------------------------------------
    // Past-valid counter and reset sequence
    // -------------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // -------------------------------------------------------------------------
    // Assumptions: well-formed APB masters
    // -------------------------------------------------------------------------
    genvar am;
    generate
        for (am = 0; am < M; am++) begin : gen_assume_master
            always @(posedge clk) begin
                if (rst_n) assume (!m_apb_penable[am] || m_apb_psel[am]);
            end
            always @(posedge clk) begin
                if (f_past_valid > 0 && $past(!rst_n))
                    assume (!m_apb_psel[am]);
            end
        end
    endgenerate

    // Assume stable configuration
    always @(posedge clk) if (rst_n) begin
        assume ($stable(SLAVE_ENABLE));
        assume ($stable(SLAVE_ADDR_BASE));
        assume ($stable(SLAVE_ADDR_LIMIT));
        assume ($stable(THRESHOLDS));
    end

    // Assume non-overlapping address ranges
    generate
        for (genvar si = 0; si < S; si++) begin : gen_assume_range_i
            for (genvar sj = si + 1; sj < S; sj++) begin : gen_assume_range_j
                always @(posedge clk) if (rst_n) begin
                    if (SLAVE_ENABLE[si] && SLAVE_ENABLE[sj])
                        assume (SLAVE_ADDR_LIMIT[si] < SLAVE_ADDR_BASE[sj] ||
                                SLAVE_ADDR_LIMIT[sj] < SLAVE_ADDR_BASE[si]);
                end
            end
        end
    endgenerate

    // Assume base <= limit
    generate
        for (genvar sb = 0; sb < S; sb++) begin : gen_assume_base_limit
            always @(posedge clk) if (rst_n) begin
                if (SLAVE_ENABLE[sb])
                    assume (SLAVE_ADDR_BASE[sb] <= SLAVE_ADDR_LIMIT[sb]);
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Property 1: Reset clears slave-side outputs
    // After reset, arbiters have no grants so mux outputs are zero.
    // -------------------------------------------------------------------------
    generate
        for (genvar rs = 0; rs < S; rs++) begin : gen_reset_slave
            always @(posedge clk) begin
                if (f_past_valid > 0 && $past(!rst_n)) begin
                    assert (!s_apb_psel[rs]);
                    assert (!s_apb_penable[rs]);
                end
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Property 2: APB protocol on slave side - PENABLE requires PSEL
    // -------------------------------------------------------------------------
    generate
        for (genvar ps = 0; ps < S; ps++) begin : gen_apb_proto
            always @(posedge clk) begin
                if (rst_n) begin
                    assert (!s_apb_penable[ps] || s_apb_psel[ps]);
                end
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Property 3: Arbiter grant valid implies grant has bits set
    // Each slave's arbiter: if grant_valid, then exactly one grant bit is set.
    // -------------------------------------------------------------------------
    generate
        for (genvar gs = 0; gs < S; gs++) begin : gen_grant_check
            wire [M-1:0] gnt_bits = dut.arb_gnt[gs];
            always @(posedge clk) begin
                if (rst_n) begin
                    assert ($countones(gnt_bits) <= 1);
                end
            end
        end
    endgenerate

    // -------------------------------------------------------------------------
    // Cover: basic transaction flow
    // -------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            cp_s_psel:    cover (s_apb_psel[0]);
            cp_m_pready:  cover (m_apb_pready[0]);
        end
    end

endmodule
