// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_master — APB protocol compliance on output ports

`include "reset_defs.svh"

module formal_apb_master #(
    parameter int AW = 16,
    parameter int DW = 32
) (
    input logic clk,
    input logic rst_n,
    input logic cmd_valid,
    input logic rsp_ready,
    input logic m_apb_PREADY,
    input logic [DW-1:0] m_apb_PRDATA,
    input logic m_apb_PSLVERR
);

    localparam int SW = DW / 8;
    localparam int PW = 3;

    // Command inputs — free (solver explores)
    logic [AW-1:0] cmd_paddr;
    logic          cmd_pwrite;
    logic [DW-1:0] cmd_pwdata;
    logic [SW-1:0] cmd_pstrb;
    logic [PW-1:0] cmd_pprot;

    // DUT outputs
    logic          cmd_ready;
    logic          m_apb_PSEL, m_apb_PENABLE, m_apb_PWRITE;
    logic [AW-1:0] m_apb_PADDR;
    logic [DW-1:0] m_apb_PWDATA;
    logic [SW-1:0] m_apb_PSTRB;
    logic [PW-1:0] m_apb_PPROT;
    logic          rsp_valid;
    logic [DW-1:0] rsp_prdata;
    logic          rsp_pslverr;

    apb_master #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .CMD_DEPTH(2), .RSP_DEPTH(2)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready),
        .cmd_paddr(cmd_paddr), .cmd_pwrite(cmd_pwrite),
        .cmd_pwdata(cmd_pwdata), .cmd_pstrb(cmd_pstrb), .cmd_pprot(cmd_pprot),
        .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
        .rsp_prdata(rsp_prdata), .rsp_pslverr(rsp_pslverr),
        .m_apb_PSEL(m_apb_PSEL), .m_apb_PENABLE(m_apb_PENABLE),
        .m_apb_PADDR(m_apb_PADDR), .m_apb_PWRITE(m_apb_PWRITE),
        .m_apb_PWDATA(m_apb_PWDATA), .m_apb_PSTRB(m_apb_PSTRB),
        .m_apb_PPROT(m_apb_PPROT),
        .m_apb_PREADY(m_apb_PREADY), .m_apb_PRDATA(m_apb_PRDATA),
        .m_apb_PSLVERR(m_apb_PSLVERR)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // PENABLE never without PSEL
    always @(posedge clk) begin
        if (rst_n)
            ap_pen_needs_psel: assert (!m_apb_PENABLE || m_apb_PSEL);
    end

    // Reset clears APB outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_psel: assert (!m_apb_PSEL);
            ap_reset_pen: assert (!m_apb_PENABLE);
        end
    end

    // SETUP → ACCESS or SETUP hold: PSEL stays asserted
    // (IDLE can show PSEL=1 for 1 cycle before SETUP, so 2 PSEL+!PENABLE cycles possible)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && !m_apb_PENABLE))
                ap_psel_continues: assert (m_apb_PSEL);
    end

    // Address stable during ACCESS phase (PENABLE held)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PENABLE) && m_apb_PENABLE)
                ap_addr_stable: assert (m_apb_PADDR == $past(m_apb_PADDR));
    end

    // PWRITE stable during ACCESS phase
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PENABLE) && m_apb_PENABLE)
                ap_pwrite_stable: assert (m_apb_PWRITE == $past(m_apb_PWRITE));
    end

    // ACCESS held until PREADY
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_apb_PSEL && m_apb_PENABLE && !m_apb_PREADY))
                ap_access_hold: assert (m_apb_PSEL && m_apb_PENABLE);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_setup: cover (m_apb_PSEL && !m_apb_PENABLE);
            cp_access: cover (m_apb_PSEL && m_apb_PENABLE);
            cp_complete: cover (m_apb_PSEL && m_apb_PENABLE && m_apb_PREADY);
        end
    end

endmodule
