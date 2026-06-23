// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// TB shim around ddr2_lpddr2_csr_slave for unit testing.
//
// The slave's hwif_in struct port can't be driven from cocotb without a
// shim — verilator does not expose nested struct fields as flat signals
// at the toplevel. This wrapper ties hwif_in.*.next to 0 so the regblock
// only sees default values, exposes the APB ports flat at the top, and
// drops the hwif_out struct.
//
// The full integration test (F1f) will drive hwif_in via the config_block
// and will exercise status / obs_words readback there.

`timescale 1ns / 1ps

module ddr2_lpddr2_csr_slave_tb
    import ddr2_lpddr2_csr_pkg::*;
#(
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int APB_STRB_WIDTH = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH = 3
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,
    input  logic                          pclk,
    input  logic                          presetn,

    input  logic                          s_apb_PSEL,
    input  logic                          s_apb_PENABLE,
    output logic                          s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_PADDR,
    input  logic                          s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_apb_PRDATA,
    output logic                          s_apb_PSLVERR
);

    ddr2_lpddr2_csr__in_t   hwif_in_tied;
    ddr2_lpddr2_csr__out_t  hwif_out_unused;

    // Tie every .next to 0 so the regblock sees stable hwif_in.
    // Use a struct literal with default zero fill (bare 0 on packed
    // struct LHS is not accepted by the simulator).
    assign hwif_in_tied = '{default:'0};

    ddr2_lpddr2_csr_slave #(
        .APB_ADDR_WIDTH (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH (APB_DATA_WIDTH)
    ) u_dut (
        .mc_clk         (mc_clk),
        .mc_rst_n       (mc_rst_n),
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (s_apb_PSEL),
        .s_apb_PENABLE  (s_apb_PENABLE),
        .s_apb_PREADY   (s_apb_PREADY),
        .s_apb_PADDR    (s_apb_PADDR),
        .s_apb_PWRITE   (s_apb_PWRITE),
        .s_apb_PWDATA   (s_apb_PWDATA),
        .s_apb_PSTRB    (s_apb_PSTRB),
        .s_apb_PPROT    (s_apb_PPROT),
        .s_apb_PRDATA   (s_apb_PRDATA),
        .s_apb_PSLVERR  (s_apb_PSLVERR),
        .hwif_out       (hwif_out_unused),
        .hwif_in        (hwif_in_tied)
    );

endmodule : ddr2_lpddr2_csr_slave_tb
