// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_slave — APB5 slave protocol (parity disabled)

`include "reset_defs.svh"

module formal_apb5_slave #(
    parameter int AW = 16,
    parameter int DW = 32
) (
    input logic clk, input logic rst_n,
    input logic s_apb_PSEL, input logic s_apb_PENABLE,
    input logic [AW-1:0] s_apb_PADDR, input logic s_apb_PWRITE,
    input logic [DW-1:0] s_apb_PWDATA, input logic [DW/8-1:0] s_apb_PSTRB,
    input logic [2:0] s_apb_PPROT,
    input logic rsp_valid, input logic [DW-1:0] rsp_prdata, input logic rsp_pslverr
);

    localparam int AUW = 4;
    localparam int WUW = 4;
    localparam int RUW = 4;
    localparam int BUW = 4;

    logic s_apb_PREADY;
    logic [DW-1:0] s_apb_PRDATA;
    logic s_apb_PSLVERR;
    logic cmd_valid;

    apb5_slave #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .DEPTH(2), .ENABLE_PARITY(0)
    ) dut (
        .pclk(clk), .presetn(rst_n),
        .s_apb_PSEL(s_apb_PSEL), .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY),
        .s_apb_PADDR(s_apb_PADDR), .s_apb_PWRITE(s_apb_PWRITE),
        .s_apb_PWDATA(s_apb_PWDATA), .s_apb_PSTRB(s_apb_PSTRB),
        .s_apb_PPROT(s_apb_PPROT),
        .s_apb_PAUSER({AUW{1'b0}}), .s_apb_PWUSER({WUW{1'b0}}),
        .s_apb_PRDATA(s_apb_PRDATA), .s_apb_PSLVERR(s_apb_PSLVERR),
        .s_apb_PRUSER(), .s_apb_PBUSER(),
        .s_apb_PWAKEUP(),
        .cmd_valid(cmd_valid), .cmd_ready(1'b1),
        .cmd_paddr(), .cmd_pwrite(), .cmd_pwdata(), .cmd_pstrb(), .cmd_pprot(),
        .cmd_pauser(), .cmd_pwuser(),
        .rsp_valid(rsp_valid), .rsp_ready(),
        .rsp_prdata(rsp_prdata), .rsp_pslverr(rsp_pslverr),
        .rsp_pruser({RUW{1'b0}}), .rsp_pbuser({BUW{1'b0}})
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Well-formed APB master
    always @(posedge clk) begin
        if (rst_n) assume (!s_apb_PENABLE || s_apb_PSEL);
    end
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) assume (!s_apb_PSEL);
    end

    // Reset
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_pready: assert (!s_apb_PREADY);
    end

    // Note: PREADY timing deferred to simulation verification.

    always @(posedge clk) begin
        if (rst_n) begin
            cp_pready: cover (s_apb_PREADY);
            cp_cmd: cover (cmd_valid);
        end
    end

endmodule
