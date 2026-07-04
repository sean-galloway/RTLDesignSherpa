// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: a7ddrphy (VERILATOR / SIM stub declaration only)
// Purpose: Blackbox declaration of LiteDRAM's Artix-7 DDR PHY so the
//          harness can be linted and simulated without pulling in
//          the actual LiteX/Migen-generated Verilog body.
//
// The REAL a7ddrphy body is produced by LiteDRAM at Vivado build time
// (see bin/gen_a7ddrphy.py). It is a large machine-generated Verilog
// file (~4000 lines) built from Migen sources under
//   https://github.com/enjoy-digital/litedram/blob/master/litedram/
//   phy/a7ddrphy.py
// It instantiates OSERDESE2/ISERDESE2 for the DQ/DQS byte lanes,
// IDELAYE2 for read-training taps, IOBUFDS_DIFF_OUT for the DDR
// differential clock and DQS, and a small state machine for
// read/write leveling.
//
// This stub deliberately has an empty body:
//   * verilator sees the module declaration and treats it as a blackbox
//     (linting still catches port-mismatch errors at the instance side)
//   * Vivado build scripts EXCLUDE this file and pull the generated
//     a7ddrphy.v from rtl-vivado/ instead
//
// Port list is the per-phase (nphases=2 for DFI_RATE=2) DFI interface
// that LiteDRAM emits, plus the DDR2 pad-side signals for the Micron
// MT47H64M16HR-25E (x16 single-rank on Nexys A7).
//
// NB: LiteDRAM's convention names them dfi_p{N}_<sig>, not dfi_<sig>_p{N},
// and rddata / rddata_valid are OUTPUTS of the PHY (to the controller).

`timescale 1ns / 1ps

/* verilator lint_off DECLFILENAME */
module a7ddrphy #(
    parameter int NPHASES        = 2,       // DFI phases (DFI_RATE)
    parameter int DFI_ADDR_W     = 14,      // DDR2 row/col address width
    parameter int DFI_BANK_W     = 3,       // 8 banks
    parameter int DFI_DATA_W     = 128,     // per-phase DQ + burst; = 2*x16*BL/2
                                            // (see LiteDRAM sdram_module for
                                            //  the exact derivation — 128 is
                                            //  the observed value for 800 Mbps
                                            //  x16 with nphases=2, BL=4)
    parameter int DFI_STRB_W     = DFI_DATA_W / 8,
    parameter int DDR2_DQ_W      = 16,
    parameter int DDR2_DM_W      = 2,       // DDR2 has one DM per byte lane
    parameter int DDR2_DQS_W     = 2        // one DQS pair per byte lane
) (
    // ------------------------------------------------------------------
    // Clocks & resets (typical LiteDRAM naming)
    // ------------------------------------------------------------------
    input  logic                     sys_clk,      // ~100 MHz, controller clk
    input  logic                     sys_rst,      // sync active-high reset
    input  logic                     sys4x_clk,    // 400 MHz for OSERDES
    input  logic                     sys4x_180_clk,// 400 MHz phase-shifted
    input  logic                     iodelay_ref_clk, // 200 MHz IDELAYCTRL ref

    // ------------------------------------------------------------------
    // DFI master side (per-phase; controller drives, PHY consumes)
    // ------------------------------------------------------------------
    // Phase 0
    input  logic [DFI_ADDR_W-1:0]    dfi_p0_address,
    input  logic [DFI_BANK_W-1:0]    dfi_p0_bank,
    input  logic                     dfi_p0_ras_n,
    input  logic                     dfi_p0_cas_n,
    input  logic                     dfi_p0_we_n,
    input  logic                     dfi_p0_cs_n,
    input  logic                     dfi_p0_cke,
    input  logic                     dfi_p0_odt,
    input  logic                     dfi_p0_reset_n,
    input  logic                     dfi_p0_wrdata_en,
    input  logic [63:0]              dfi_p0_wrdata,
    input  logic [7:0]               dfi_p0_wrdata_mask,
    input  logic                     dfi_p0_rddata_en,
    output logic [63:0]              dfi_p0_rddata,
    output logic                     dfi_p0_rddata_valid,

    // Phase 1
    input  logic [DFI_ADDR_W-1:0]    dfi_p1_address,
    input  logic [DFI_BANK_W-1:0]    dfi_p1_bank,
    input  logic                     dfi_p1_ras_n,
    input  logic                     dfi_p1_cas_n,
    input  logic                     dfi_p1_we_n,
    input  logic                     dfi_p1_cs_n,
    input  logic                     dfi_p1_cke,
    input  logic                     dfi_p1_odt,
    input  logic                     dfi_p1_reset_n,
    input  logic                     dfi_p1_wrdata_en,
    input  logic [63:0]              dfi_p1_wrdata,
    input  logic [7:0]               dfi_p1_wrdata_mask,
    input  logic                     dfi_p1_rddata_en,
    output logic [63:0]              dfi_p1_rddata,
    output logic                     dfi_p1_rddata_valid,

    // ------------------------------------------------------------------
    // DDR2 pad side — routed straight to FPGA IOBs at ddr2_char_top
    // ------------------------------------------------------------------
    output logic [DFI_ADDR_W-1:0]    ddram_a,
    output logic [DFI_BANK_W-1:0]    ddram_ba,
    output logic                     ddram_ras_n,
    output logic                     ddram_cas_n,
    output logic                     ddram_we_n,
    output logic                     ddram_cs_n,
    output logic                     ddram_cke,
    output logic                     ddram_odt,
    output logic [DDR2_DM_W-1:0]     ddram_dm,
    inout  wire  [DDR2_DQ_W-1:0]     ddram_dq,
    inout  wire  [DDR2_DQS_W-1:0]    ddram_dqs_p,
    inout  wire  [DDR2_DQS_W-1:0]    ddram_dqs_n,
    output logic                     ddram_clk_p,
    output logic                     ddram_clk_n
);
    // ------------------------------------------------------------------
    // BLACKBOX BODY.
    //
    // Vivado build: this file is EXCLUDED from the synthesis fileset.
    //   The real a7ddrphy.v (LiteDRAM-generated) is included instead.
    //
    // Lint (verilator and cocotb sim): driving outputs low keeps lint
    //   quiet. Downstream logic reads all-zero which is safe -- no DFI
    //   init handshake ever completes, so the harness sits in reset.
    //   That is the expected behaviour of a lint-only build.
    // ------------------------------------------------------------------
    assign dfi_p0_rddata       = '0;
    assign dfi_p0_rddata_valid = 1'b0;
    assign dfi_p1_rddata       = '0;
    assign dfi_p1_rddata_valid = 1'b0;

    assign ddram_a             = '0;
    assign ddram_ba            = '0;
    assign ddram_ras_n         = 1'b1;
    assign ddram_cas_n         = 1'b1;
    assign ddram_we_n          = 1'b1;
    assign ddram_cs_n          = 1'b1;
    assign ddram_cke           = 1'b0;
    assign ddram_odt           = 1'b0;
    assign ddram_dm            = '0;
    assign ddram_clk_p         = 1'b0;
    assign ddram_clk_n         = 1'b1;

    // ddram_dq / ddram_dqs_* are `inout`; leave floating in the stub.
    // The real PHY drives / releases based on wrdata_en / rddata_en.

    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        sys_clk, sys_rst, sys4x_clk, sys4x_180_clk, iodelay_ref_clk,
        dfi_p0_address, dfi_p0_bank, dfi_p0_ras_n, dfi_p0_cas_n, dfi_p0_we_n,
        dfi_p0_cs_n, dfi_p0_cke, dfi_p0_odt, dfi_p0_reset_n,
        dfi_p0_wrdata_en, dfi_p0_wrdata, dfi_p0_wrdata_mask, dfi_p0_rddata_en,
        dfi_p1_address, dfi_p1_bank, dfi_p1_ras_n, dfi_p1_cas_n, dfi_p1_we_n,
        dfi_p1_cs_n, dfi_p1_cke, dfi_p1_odt, dfi_p1_reset_n,
        dfi_p1_wrdata_en, dfi_p1_wrdata, dfi_p1_wrdata_mask, dfi_p1_rddata_en,
        ddram_dq, ddram_dqs_p, ddram_dqs_n,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : a7ddrphy
/* verilator lint_on DECLFILENAME */
