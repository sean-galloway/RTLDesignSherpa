// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_master — APB5 protocol compliance (parity disabled)

`include "reset_defs.svh"

module formal_apb5_master #(
    parameter int AW = 16,
    parameter int DW = 32
) (
    input logic clk, input logic rst_n,
    input logic cmd_valid, input logic rsp_ready,
    input logic m_apb_PREADY, input logic [DW-1:0] m_apb_PRDATA,
    input logic m_apb_PSLVERR
);

    localparam int SW = DW / 8;
    localparam int PW = 3;
    localparam int AUW = 4;
    localparam int WUW = 4;
    localparam int RUW = 4;
    localparam int BUW = 4;

    logic m_apb_PSEL, m_apb_PENABLE, m_apb_PWRITE;
    logic [AW-1:0] m_apb_PADDR;
    logic [DW-1:0] m_apb_PWDATA;
    logic [SW-1:0] m_apb_PSTRB;
    logic [PW-1:0] m_apb_PPROT;
    logic cmd_ready, rsp_valid;

    apb5_master #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .CMD_DEPTH(2), .RSP_DEPTH(2),
        .ENABLE_PARITY(0)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready),
        .cmd_paddr({AW{1'b0}}), .cmd_pwrite(1'b0),
        .cmd_pwdata({DW{1'b0}}), .cmd_pstrb({SW{1'b0}}),
        .cmd_pprot(3'b0), .cmd_pauser({AUW{1'b0}}), .cmd_pwuser({WUW{1'b0}}),
        .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
        .rsp_prdata(), .rsp_pslverr(), .rsp_pruser(), .rsp_pbuser(),
        .m_apb_PSEL(m_apb_PSEL), .m_apb_PENABLE(m_apb_PENABLE),
        .m_apb_PADDR(m_apb_PADDR), .m_apb_PWRITE(m_apb_PWRITE),
        .m_apb_PWDATA(m_apb_PWDATA), .m_apb_PSTRB(m_apb_PSTRB),
        .m_apb_PPROT(m_apb_PPROT),
        .m_apb_PAUSER(), .m_apb_PWUSER(),
        .m_apb_PREADY(m_apb_PREADY), .m_apb_PRDATA(m_apb_PRDATA),
        .m_apb_PSLVERR(m_apb_PSLVERR),
        .m_apb_PRUSER({RUW{1'b0}}), .m_apb_PBUSER({BUW{1'b0}}),
        .m_apb_PWAKEUP(1'b0)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Same APB protocol properties as apb_master
    always @(posedge clk) begin
        if (rst_n) ap_pen_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel: assert (!m_apb_PSEL);
            ap_reset_pen: assert (!m_apb_PENABLE);
        end
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && !m_apb_PENABLE))
                ap_psel_continues: assert (m_apb_PSEL);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    always @(posedge clk) begin
        if (rst_n) begin
            cp_setup: cover (m_apb_PSEL && !m_apb_PENABLE);
            cp_access: cover (m_apb_PSEL && m_apb_PENABLE);
        end
    end

endmodule
