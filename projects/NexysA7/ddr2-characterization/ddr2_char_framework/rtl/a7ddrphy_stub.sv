// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: a7ddrphy (STUB)
// Purpose: Port-shape black box for the LiteDRAM a7ddrphy, used by the
//          RTL simulator (cannot model the OSERDESE2 / ISERDESE2 /
//          IDELAYE2 IOB serdes stack). The Vivado build swaps in the
//          REAL generated body:
//            flows-ours-uart/rtl-vivado/a7ddrphy/a7ddrphy_generated.v
//          (regenerate via flows-ours-uart/bin/elaborate_a7ddrphy.py).
//
// The port list MUST match a7ddrphy_generated.v EXACTLY (names + widths)
// so ddr2_char_top instantiates the same module for both sim and synth:
//   - DFI 4-phase (dfi_p0..p3), 13b addr, 32b wrdata/phase, 4b mask
//   - calibration CSR bus (adr[9:0]/we/dat_w[31:0]/dat_r[31:0])
//   - clocks sys / sys2x / sys4x / sys4x_dqs (+ their resets)
//   - ddram pads (x16, banks 34/35 pinout applied in the XDC)
// Fixed widths (no params) — the generated body is fully elaborated.
//
// Sim behavior: outputs driven to benign constants. Real DDR2 traffic +
// leveling only happen on hardware with the generated PHY.

`timescale 1ns / 1ps

module a7ddrphy (
    // DDR2 pads
    output logic [12:0] ddram_a,
    output logic [2:0]  ddram_ba,
    output logic        ddram_ras_n,
    output logic        ddram_cas_n,
    output logic        ddram_we_n,
    output logic [1:0]  ddram_dm,
    inout  wire  [15:0] ddram_dq,
    inout  wire  [1:0]  ddram_dqs_p,
    inout  wire  [1:0]  ddram_dqs_n,
    output logic        ddram_clk_p,
    output logic        ddram_clk_n,
    output logic        ddram_cke,
    output logic        ddram_odt,
    output logic        ddram_cs_n,

    // Clocks / resets
    input  logic sys_clk,
    input  logic sys_rst,
    input  logic sys2x_clk,
    input  logic sys2x_rst,
    input  logic sys4x_clk,
    input  logic sys4x_rst,
    input  logic sys4x_dqs_clk,
    input  logic sys4x_dqs_rst,

    // DFI phase 0
    input  logic [12:0] dfi_p0_address,
    input  logic [2:0]  dfi_p0_bank,
    input  logic        dfi_p0_cas_n,
    input  logic        dfi_p0_cs_n,
    input  logic        dfi_p0_ras_n,
    input  logic        dfi_p0_we_n,
    input  logic        dfi_p0_cke,
    input  logic        dfi_p0_odt,
    input  logic        dfi_p0_reset_n,
    input  logic        dfi_p0_act_n,
    input  logic [31:0] dfi_p0_wrdata,
    input  logic        dfi_p0_wrdata_en,
    input  logic [3:0]  dfi_p0_wrdata_mask,
    input  logic        dfi_p0_rddata_en,
    output logic [31:0] dfi_p0_rddata,
    output logic        dfi_p0_rddata_valid,
    // DFI phase 1
    input  logic [12:0] dfi_p1_address,
    input  logic [2:0]  dfi_p1_bank,
    input  logic        dfi_p1_cas_n,
    input  logic        dfi_p1_cs_n,
    input  logic        dfi_p1_ras_n,
    input  logic        dfi_p1_we_n,
    input  logic        dfi_p1_cke,
    input  logic        dfi_p1_odt,
    input  logic        dfi_p1_reset_n,
    input  logic        dfi_p1_act_n,
    input  logic [31:0] dfi_p1_wrdata,
    input  logic        dfi_p1_wrdata_en,
    input  logic [3:0]  dfi_p1_wrdata_mask,
    input  logic        dfi_p1_rddata_en,
    output logic [31:0] dfi_p1_rddata,
    output logic        dfi_p1_rddata_valid,
    // DFI phase 2
    input  logic [12:0] dfi_p2_address,
    input  logic [2:0]  dfi_p2_bank,
    input  logic        dfi_p2_cas_n,
    input  logic        dfi_p2_cs_n,
    input  logic        dfi_p2_ras_n,
    input  logic        dfi_p2_we_n,
    input  logic        dfi_p2_cke,
    input  logic        dfi_p2_odt,
    input  logic        dfi_p2_reset_n,
    input  logic        dfi_p2_act_n,
    input  logic [31:0] dfi_p2_wrdata,
    input  logic        dfi_p2_wrdata_en,
    input  logic [3:0]  dfi_p2_wrdata_mask,
    input  logic        dfi_p2_rddata_en,
    output logic [31:0] dfi_p2_rddata,
    output logic        dfi_p2_rddata_valid,
    // DFI phase 3
    input  logic [12:0] dfi_p3_address,
    input  logic [2:0]  dfi_p3_bank,
    input  logic        dfi_p3_cas_n,
    input  logic        dfi_p3_cs_n,
    input  logic        dfi_p3_ras_n,
    input  logic        dfi_p3_we_n,
    input  logic        dfi_p3_cke,
    input  logic        dfi_p3_odt,
    input  logic        dfi_p3_reset_n,
    input  logic        dfi_p3_act_n,
    input  logic [31:0] dfi_p3_wrdata,
    input  logic        dfi_p3_wrdata_en,
    input  logic [3:0]  dfi_p3_wrdata_mask,
    input  logic        dfi_p3_rddata_en,
    output logic [31:0] dfi_p3_rddata,
    output logic        dfi_p3_rddata_valid,

    // Calibration CSR bus (32-bit) — 13 leveling knobs; see
    // rtl-vivado/a7ddrphy/a7ddrphy_csr_map.txt
    input  logic [9:0]  adr,
    input  logic        we,
    input  logic [31:0] dat_w,
    output logic [31:0] dat_r
);

    // Black-box: drive all outputs to benign constants for lint/sim.
    assign ddram_a     = '0;
    assign ddram_ba    = '0;
    assign ddram_ras_n = 1'b1;
    assign ddram_cas_n = 1'b1;
    assign ddram_we_n  = 1'b1;
    assign ddram_dm    = '0;
    assign ddram_dq    = 'z;
    assign ddram_dqs_p = 'z;
    assign ddram_dqs_n = 'z;
    assign ddram_clk_p = 1'b0;
    assign ddram_clk_n = 1'b1;
    assign ddram_cke   = 1'b0;
    assign ddram_odt   = 1'b0;
    assign ddram_cs_n  = 1'b1;

    assign dfi_p0_rddata = '0;  assign dfi_p0_rddata_valid = 1'b0;
    assign dfi_p1_rddata = '0;  assign dfi_p1_rddata_valid = 1'b0;
    assign dfi_p2_rddata = '0;  assign dfi_p2_rddata_valid = 1'b0;
    assign dfi_p3_rddata = '0;  assign dfi_p3_rddata_valid = 1'b0;

    assign dat_r = '0;

    // Keep unused inputs quiet for verilator.
    /* verilator lint_off UNUSED */
    wire _unused = &{1'b0,
        sys_clk, sys_rst, sys2x_clk, sys2x_rst, sys4x_clk, sys4x_rst,
        sys4x_dqs_clk, sys4x_dqs_rst,
        dfi_p0_address, dfi_p0_bank, dfi_p0_cas_n, dfi_p0_cs_n, dfi_p0_ras_n,
        dfi_p0_we_n, dfi_p0_cke, dfi_p0_odt, dfi_p0_reset_n, dfi_p0_act_n,
        dfi_p0_wrdata, dfi_p0_wrdata_en, dfi_p0_wrdata_mask, dfi_p0_rddata_en,
        dfi_p1_address, dfi_p1_bank, dfi_p1_cas_n, dfi_p1_cs_n, dfi_p1_ras_n,
        dfi_p1_we_n, dfi_p1_cke, dfi_p1_odt, dfi_p1_reset_n, dfi_p1_act_n,
        dfi_p1_wrdata, dfi_p1_wrdata_en, dfi_p1_wrdata_mask, dfi_p1_rddata_en,
        dfi_p2_address, dfi_p2_bank, dfi_p2_cas_n, dfi_p2_cs_n, dfi_p2_ras_n,
        dfi_p2_we_n, dfi_p2_cke, dfi_p2_odt, dfi_p2_reset_n, dfi_p2_act_n,
        dfi_p2_wrdata, dfi_p2_wrdata_en, dfi_p2_wrdata_mask, dfi_p2_rddata_en,
        dfi_p3_address, dfi_p3_bank, dfi_p3_cas_n, dfi_p3_cs_n, dfi_p3_ras_n,
        dfi_p3_we_n, dfi_p3_cke, dfi_p3_odt, dfi_p3_reset_n, dfi_p3_act_n,
        dfi_p3_wrdata, dfi_p3_wrdata_en, dfi_p3_wrdata_mask, dfi_p3_rddata_en,
        adr, we, dat_w};
    /* verilator lint_on UNUSED */

endmodule : a7ddrphy
