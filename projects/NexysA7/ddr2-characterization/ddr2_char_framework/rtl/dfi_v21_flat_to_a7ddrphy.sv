// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_v21_flat_to_a7ddrphy
// Purpose: Bridge our DDR2/LPDDR2 controller's flat DFI v2.1 output to the
//          LiteDRAM a7ddrphy's per-phase DFI (dfi_p0..p3).
//
// The controller emits a phase-PACKED flat bus at DFI_RATE = NPHASES:
//   dfi_address_o      [DFI_ADDR_W*NPHASES]   phase p = [p*DFI_ADDR_W +: DFI_ADDR_W]
//   dfi_bank_o         [DFI_BANK_W*NPHASES]
//   dfi_cas_n_o        [NPHASES]              one bit per phase
//   dfi_ras_n_o        [NPHASES]
//   dfi_we_n_o         [NPHASES]
//   dfi_cs_n_o         [NPHASES]
//   dfi_cke_o          [NPHASES]
//   dfi_odt_o          [NPHASES]
//   dfi_wrdata_o       [PHASE_DATA*NPHASES]   {p3,p2,p1,p0}
//   dfi_wrdata_mask_o  [PHASE_STRB*NPHASES]
//   dfi_wrdata_en_o    [NPHASES]
//   dfi_rddata_i       [PHASE_DATA*NPHASES]
//   dfi_rddata_en_o    [NPHASES]
//   dfi_rddata_valid_i [NPHASES]
//
// a7ddrphy wants each phase broken out (dfi_p0_*, ..., dfi_p3_*). This is a
// purely combinational per-phase SLICE — no broadcasting. Commands ride
// phase 0 (the DFI cmd formatter NOPs phases 1..NPHASES-1), but the slice is
// faithful either way; the PHY latches the command on the phase whose cs_n
// is low. DDR2 has no reset_n / act_n JEDEC pins, so those per-phase DFI
// signals are tied inactive (reset_n = out-of-reset, act_n = 1).
//
// NPHASES is fixed at 4 to match the Artix-7 a7ddrphy (nphases=4, 4:1).

`timescale 1ns / 1ps

module dfi_v21_flat_to_a7ddrphy #(
    parameter int DFI_ADDR_W  = 13,     // row-address bits (ROW_WIDTH)
    parameter int DFI_BANK_W  = 3,
    parameter int PHASE_DATA  = 32,     // per-phase DFI data (= 2 x DQ width)
    parameter int NPHASES     = 4,      // fixed 4 for a7ddrphy
    parameter int PHASE_STRB  = PHASE_DATA / 8
) (
    // ------------------------------------------------------------------
    // Flat (phase-packed) DFI side — from pumice_top / char macro.
    // ------------------------------------------------------------------
    input  logic [DFI_ADDR_W*NPHASES-1:0]  dfi_address_flat,
    input  logic [DFI_BANK_W*NPHASES-1:0]  dfi_bank_flat,
    input  logic [NPHASES-1:0]             dfi_cas_n_flat,
    input  logic [NPHASES-1:0]             dfi_ras_n_flat,
    input  logic [NPHASES-1:0]             dfi_we_n_flat,
    input  logic [NPHASES-1:0]             dfi_cs_n_flat,
    input  logic [NPHASES-1:0]             dfi_cke_flat,
    input  logic [NPHASES-1:0]             dfi_odt_flat,
    input  logic [PHASE_DATA*NPHASES-1:0]  dfi_wrdata_flat,
    input  logic [PHASE_STRB*NPHASES-1:0]  dfi_wrdata_mask_flat,
    input  logic [NPHASES-1:0]             dfi_wrdata_en_flat,
    input  logic [NPHASES-1:0]             dfi_rddata_en_flat,
    output logic [PHASE_DATA*NPHASES-1:0]  dfi_rddata_flat,
    output logic [NPHASES-1:0]             dfi_rddata_valid_flat,

    // ------------------------------------------------------------------
    // Per-phase DFI (to a7ddrphy).
    // ------------------------------------------------------------------
    output logic [DFI_ADDR_W-1:0] dfi_p0_address, dfi_p1_address,
                                  dfi_p2_address, dfi_p3_address,
    output logic [DFI_BANK_W-1:0] dfi_p0_bank, dfi_p1_bank,
                                  dfi_p2_bank, dfi_p3_bank,
    output logic dfi_p0_ras_n, dfi_p1_ras_n, dfi_p2_ras_n, dfi_p3_ras_n,
    output logic dfi_p0_cas_n, dfi_p1_cas_n, dfi_p2_cas_n, dfi_p3_cas_n,
    output logic dfi_p0_we_n,  dfi_p1_we_n,  dfi_p2_we_n,  dfi_p3_we_n,
    output logic dfi_p0_cs_n,  dfi_p1_cs_n,  dfi_p2_cs_n,  dfi_p3_cs_n,
    output logic dfi_p0_cke,   dfi_p1_cke,   dfi_p2_cke,   dfi_p3_cke,
    output logic dfi_p0_odt,   dfi_p1_odt,   dfi_p2_odt,   dfi_p3_odt,
    output logic dfi_p0_reset_n, dfi_p1_reset_n, dfi_p2_reset_n, dfi_p3_reset_n,
    output logic dfi_p0_act_n, dfi_p1_act_n, dfi_p2_act_n, dfi_p3_act_n,
    output logic dfi_p0_wrdata_en, dfi_p1_wrdata_en,
                 dfi_p2_wrdata_en, dfi_p3_wrdata_en,
    output logic [PHASE_DATA-1:0] dfi_p0_wrdata, dfi_p1_wrdata,
                                  dfi_p2_wrdata, dfi_p3_wrdata,
    output logic [PHASE_STRB-1:0] dfi_p0_wrdata_mask, dfi_p1_wrdata_mask,
                                  dfi_p2_wrdata_mask, dfi_p3_wrdata_mask,
    output logic dfi_p0_rddata_en, dfi_p1_rddata_en,
                 dfi_p2_rddata_en, dfi_p3_rddata_en,
    input  logic [PHASE_DATA-1:0] dfi_p0_rddata, dfi_p1_rddata,
                                  dfi_p2_rddata, dfi_p3_rddata,
    input  logic dfi_p0_rddata_valid, dfi_p1_rddata_valid,
                 dfi_p2_rddata_valid, dfi_p3_rddata_valid
);

    // Per-phase command/data slices.
    `define DFI_PHASE_SLICE(P) \
        assign dfi_p``P``_address    = dfi_address_flat[P*DFI_ADDR_W +: DFI_ADDR_W]; \
        assign dfi_p``P``_bank       = dfi_bank_flat  [P*DFI_BANK_W +: DFI_BANK_W]; \
        assign dfi_p``P``_cas_n      = dfi_cas_n_flat [P]; \
        assign dfi_p``P``_ras_n      = dfi_ras_n_flat [P]; \
        assign dfi_p``P``_we_n       = dfi_we_n_flat  [P]; \
        assign dfi_p``P``_cs_n       = dfi_cs_n_flat  [P]; \
        assign dfi_p``P``_cke        = dfi_cke_flat   [P]; \
        assign dfi_p``P``_odt        = dfi_odt_flat   [P]; \
        assign dfi_p``P``_reset_n    = dfi_cke_flat   [P]; /* DDR2: no reset pin */ \
        assign dfi_p``P``_act_n      = 1'b1;               /* DDR2: no act_n */ \
        assign dfi_p``P``_wrdata     = dfi_wrdata_flat [P*PHASE_DATA +: PHASE_DATA]; \
        assign dfi_p``P``_wrdata_mask= dfi_wrdata_mask_flat[P*PHASE_STRB +: PHASE_STRB]; \
        assign dfi_p``P``_wrdata_en  = dfi_wrdata_en_flat[P]; \
        assign dfi_p``P``_rddata_en  = dfi_rddata_en_flat[P];

    `DFI_PHASE_SLICE(0)
    `DFI_PHASE_SLICE(1)
    `DFI_PHASE_SLICE(2)
    `DFI_PHASE_SLICE(3)
    `undef DFI_PHASE_SLICE

    // Read return: pack per-phase rddata / valid back into the flat bus.
    assign dfi_rddata_flat = {dfi_p3_rddata, dfi_p2_rddata,
                              dfi_p1_rddata, dfi_p0_rddata};
    assign dfi_rddata_valid_flat = {dfi_p3_rddata_valid, dfi_p2_rddata_valid,
                                    dfi_p1_rddata_valid, dfi_p0_rddata_valid};

endmodule : dfi_v21_flat_to_a7ddrphy
