// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_v21_flat_to_a7ddrphy
// Purpose: Bridge our DDR2/LPDDR2 controller's DFI v2.1 output (flat
//          address/bank + per-phase ctrl/data buses) to LiteDRAM's
//          a7ddrphy (per-phase everything).
//
// The two representations of "DFI 2-phase" differ only in whether
// address / bank are shared across phases:
//
//   Ours (DFI v2.1, single-command-per-DRAM-cycle):
//     dfi_address_o        [ADDR-1:0]      one bus, valid on
//     dfi_bank_o           [BANK-1:0]      the phase that has cs_n low
//     dfi_cas_n_o[1:0]     -- one bit per phase
//     dfi_ras_n_o[1:0]
//     dfi_we_n_o [1:0]
//     dfi_cs_n_o [1:0]
//     dfi_wrdata_o [128-1:0]   -- {p1.wrdata, p0.wrdata}
//     dfi_wrdata_mask_o [16-1:0]
//     dfi_wrdata_en_o [1:0]
//     dfi_rddata_i [128-1:0]   -- {p1.rddata, p0.rddata}
//     dfi_rddata_en_o [1:0]
//     dfi_rddata_valid_i [1:0]
//
//   LiteDRAM (per-phase everything): dfi_p0_*, dfi_p1_*.
//
// The adapter broadcasts the shared address/bank to both phases and
// concatenates/splits the per-phase data buses. Purely combinational.
// Any real design change to per-phase addresses lands in the DFI cmd
// formatter, not here.

`timescale 1ns / 1ps

module dfi_v21_flat_to_a7ddrphy #(
    parameter int DFI_ADDR_W  = 14,   // width the PHY expects (row/col)
    parameter int DFI_BANK_W  = 3,
    parameter int PHASE_DATA  = 64,   // per-phase data width
    parameter int PHASE_STRB  = PHASE_DATA / 8
) (
    // ------------------------------------------------------------------
    // Flat DFI side (from ddr2_lpddr2_top / ddr2_char_harness).
    // Address width comes in wider than PHY expects — we take the low bits.
    // ------------------------------------------------------------------
    input  logic [31:0]                  dfi_address_flat,
    input  logic [2:0]                   dfi_bank_flat,
    input  logic [1:0]                   dfi_cas_n_flat,
    input  logic [1:0]                   dfi_ras_n_flat,
    input  logic [1:0]                   dfi_we_n_flat,
    input  logic [1:0]                   dfi_cs_n_flat,
    input  logic [1:0]                   dfi_cke_flat,
    input  logic [1:0]                   dfi_odt_flat,
    input  logic [2*PHASE_DATA-1:0]      dfi_wrdata_flat,
    input  logic [2*PHASE_STRB-1:0]      dfi_wrdata_mask_flat,
    input  logic [1:0]                   dfi_wrdata_en_flat,
    input  logic [1:0]                   dfi_rddata_en_flat,
    output logic [2*PHASE_DATA-1:0]      dfi_rddata_flat,
    output logic [1:0]                   dfi_rddata_valid_flat,
    input  logic                         dfi_init_complete_flat,
    output logic                         dfi_init_start_flat,

    // These are the reset-n / cke pair the PHY expects. Our controller
    // does not expose a separate dfi_reset_n; keep the PHY-side pin
    // asserted (out of reset) whenever cke is asserted.
    // (Passed through the top-level tie-off if the harness ever grows
    //  a separate dfi_reset_n path.)

    // ------------------------------------------------------------------
    // Per-phase DFI (to a7ddrphy).
    // ------------------------------------------------------------------
    output logic [DFI_ADDR_W-1:0]        dfi_p0_address,
    output logic [DFI_BANK_W-1:0]        dfi_p0_bank,
    output logic                         dfi_p0_ras_n,
    output logic                         dfi_p0_cas_n,
    output logic                         dfi_p0_we_n,
    output logic                         dfi_p0_cs_n,
    output logic                         dfi_p0_cke,
    output logic                         dfi_p0_odt,
    output logic                         dfi_p0_reset_n,
    output logic                         dfi_p0_wrdata_en,
    output logic [PHASE_DATA-1:0]        dfi_p0_wrdata,
    output logic [PHASE_STRB-1:0]        dfi_p0_wrdata_mask,
    output logic                         dfi_p0_rddata_en,
    input  logic [PHASE_DATA-1:0]        dfi_p0_rddata,
    input  logic                         dfi_p0_rddata_valid,

    output logic [DFI_ADDR_W-1:0]        dfi_p1_address,
    output logic [DFI_BANK_W-1:0]        dfi_p1_bank,
    output logic                         dfi_p1_ras_n,
    output logic                         dfi_p1_cas_n,
    output logic                         dfi_p1_we_n,
    output logic                         dfi_p1_cs_n,
    output logic                         dfi_p1_cke,
    output logic                         dfi_p1_odt,
    output logic                         dfi_p1_reset_n,
    output logic                         dfi_p1_wrdata_en,
    output logic [PHASE_DATA-1:0]        dfi_p1_wrdata,
    output logic [PHASE_STRB-1:0]        dfi_p1_wrdata_mask,
    output logic                         dfi_p1_rddata_en,
    input  logic [PHASE_DATA-1:0]        dfi_p1_rddata,
    input  logic                         dfi_p1_rddata_valid
);

    // Broadcast address/bank to both phases; the phase with cs_n=0
    // is the one that gets latched by the PHY on that DRAM cycle.
    assign dfi_p0_address = dfi_address_flat[DFI_ADDR_W-1:0];
    assign dfi_p1_address = dfi_address_flat[DFI_ADDR_W-1:0];
    assign dfi_p0_bank    = dfi_bank_flat;
    assign dfi_p1_bank    = dfi_bank_flat;

    // Per-phase control lanes.
    assign dfi_p0_cas_n = dfi_cas_n_flat[0];
    assign dfi_p1_cas_n = dfi_cas_n_flat[1];
    assign dfi_p0_ras_n = dfi_ras_n_flat[0];
    assign dfi_p1_ras_n = dfi_ras_n_flat[1];
    assign dfi_p0_we_n  = dfi_we_n_flat[0];
    assign dfi_p1_we_n  = dfi_we_n_flat[1];
    assign dfi_p0_cs_n  = dfi_cs_n_flat[0];
    assign dfi_p1_cs_n  = dfi_cs_n_flat[1];
    assign dfi_p0_cke   = dfi_cke_flat[0];
    assign dfi_p1_cke   = dfi_cke_flat[1];
    assign dfi_p0_odt   = dfi_odt_flat[0];
    assign dfi_p1_odt   = dfi_odt_flat[1];

    // No separate dfi_reset_n on our controller — tie high (out of
    // reset) whenever cke is high on the same phase.
    assign dfi_p0_reset_n = dfi_cke_flat[0];
    assign dfi_p1_reset_n = dfi_cke_flat[1];

    // Wr data / mask / en per phase.
    assign dfi_p0_wrdata      = dfi_wrdata_flat[PHASE_DATA-1:0];
    assign dfi_p1_wrdata      = dfi_wrdata_flat[2*PHASE_DATA-1 -: PHASE_DATA];
    assign dfi_p0_wrdata_mask = dfi_wrdata_mask_flat[PHASE_STRB-1:0];
    assign dfi_p1_wrdata_mask = dfi_wrdata_mask_flat[2*PHASE_STRB-1 -: PHASE_STRB];
    assign dfi_p0_wrdata_en   = dfi_wrdata_en_flat[0];
    assign dfi_p1_wrdata_en   = dfi_wrdata_en_flat[1];

    // Rd data en per phase; return path packs both phases into the flat.
    assign dfi_p0_rddata_en   = dfi_rddata_en_flat[0];
    assign dfi_p1_rddata_en   = dfi_rddata_en_flat[1];
    assign dfi_rddata_flat        = {dfi_p1_rddata, dfi_p0_rddata};
    assign dfi_rddata_valid_flat  = {dfi_p1_rddata_valid, dfi_p0_rddata_valid};

    // Init handshake: our controller has dfi_init_start (out) and
    // dfi_init_complete (in). a7ddrphy exposes these as top-level
    // signals from its calibration FSM; wire them through as-is.
    assign dfi_init_start_flat = 1'b1;   // start immediately on release-of-reset;
                                          // a7ddrphy runs its cal FSM and pulses
                                          // dfi_init_complete when done.
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        dfi_address_flat[31:DFI_ADDR_W],
        dfi_init_complete_flat,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : dfi_v21_flat_to_a7ddrphy
