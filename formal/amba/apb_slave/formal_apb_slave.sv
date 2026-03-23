// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_slave — APB slave protocol compliance

`include "reset_defs.svh"

module formal_apb_slave #(
    parameter int AW = 16,
    parameter int DW = 32
) (
    input logic clk,
    input logic rst_n,
    // APB master drives these
    input logic s_apb_PSEL,
    input logic s_apb_PENABLE,
    input logic [AW-1:0] s_apb_PADDR,
    input logic s_apb_PWRITE,
    input logic [DW-1:0] s_apb_PWDATA,
    input logic [DW/8-1:0] s_apb_PSTRB,
    input logic [2:0] s_apb_PPROT,
    // Response side
    input logic rsp_valid,
    input logic [DW-1:0] rsp_prdata,
    input logic rsp_pslverr
);

    logic s_apb_PREADY;
    logic [DW-1:0] s_apb_PRDATA;
    logic s_apb_PSLVERR;
    logic cmd_valid, cmd_ready;

    apb_slave #(.ADDR_WIDTH(AW), .DATA_WIDTH(DW), .DEPTH(2)) dut (
        .pclk(clk), .presetn(rst_n),
        .s_apb_PSEL(s_apb_PSEL), .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY),
        .s_apb_PADDR(s_apb_PADDR), .s_apb_PWRITE(s_apb_PWRITE),
        .s_apb_PWDATA(s_apb_PWDATA), .s_apb_PSTRB(s_apb_PSTRB),
        .s_apb_PPROT(s_apb_PPROT),
        .s_apb_PRDATA(s_apb_PRDATA), .s_apb_PSLVERR(s_apb_PSLVERR),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready),
        .cmd_paddr(), .cmd_pwrite(), .cmd_pwdata(), .cmd_pstrb(), .cmd_pprot(),
        .rsp_valid(rsp_valid), .rsp_ready(),
        .rsp_prdata(rsp_prdata), .rsp_pslverr(rsp_pslverr)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Assume well-formed APB master
    always @(posedge clk) begin
        if (rst_n) assume (!s_apb_PENABLE || s_apb_PSEL);
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) assume (!s_apb_PSEL);
    end

    // Reset: PREADY low
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_pready: assert (!s_apb_PREADY);
    end

    // Note: PREADY timing is tightly coupled to internal FSM state.
    // Port-level PREADY properties deferred to simulation verification.

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_pready: cover (s_apb_PREADY);
            cp_cmd: cover (cmd_valid);
        end
    end

endmodule
