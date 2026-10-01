// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dfi_flat_to_k7ddrphy
// Purpose: Bridge scoria's phase-PACKED flat DFI bus to LiteDRAM's K7DDRPHY
//          per-phase DFI (dfi_p0..p3). Purely combinational per-phase slicing
//          -- no broadcasting, no retiming, no state.
//
// The DDR3 sibling of pumice's dfi_v21_flat_to_a7ddrphy, and it differs in
// exactly two ways. Both are DDR3-vs-DDR2 facts, not style:
//
//   1. reset_n IS A REAL PIN. DDR2 has no RESET#, so pumice ties the per-phase
//      dfi_reset_n to CKE. DDR3 has one, DFI has carried it since v2.1 for
//      DDR3 (gated on memory type, not version), and scoria presents it as
//      dfi_reset_n_o (scoria TASK-005). It is driven, not synthesised here.
//   2. ALL FOUR PHASES ARE LIVE. litedram asserts
//      `not (memtype == "DDR3" and nphases == 2)`, so DDR3 on S7DDRPHY is 1:4
//      only -- there is no 2-phase configuration to NOP the upper phases for,
//      and pumice's CTRL_PHASES generate has no counterpart here.
//
// act_n stays tied inactive: ACT_n is a DDR4 pin. LiteDRAM's port shell carries
// it for all memory types and the PHY ignores it for DDR3.
//
// PHASE_DATA IS 2 x THE DQ WIDTH, and getting this wrong is the trap this
// module sits on top of. A DFI phase carries TWO device transfers because DDR3
// is double data rate: litedram's s7ddrphy sets `dfi_databits = 2*databits`
// and packs transfer n into `phases[n//2]` half `n%2`, so four phases carry
// eight transfers -- BL8 in one sys cycle, 256 bits for a 32-bit bus. The
// board proof's own generated header agrees: SDRAM_PHY_DATABITS 32,
// SDRAM_PHY_DFI_DATABITS 64. scoria must be built DRAM_BEAT_WIDTH=64 /
// DRAM_DEVICE_WIDTH=32; a beat of 32 produces a 128-bit DFI word that this PHY
// cannot consume, which is the shape every scoria suite ran until 2026-10-01.
//
// Commands ride whichever phase the formatter placed them on -- the PHY latches
// on the phase whose cs_n is low -- so the slice is faithful either way and
// carries no assumption that commands sit on phase 0.

`timescale 1ns / 1ps

module dfi_flat_to_k7ddrphy #(
    parameter int DFI_ADDR_W = 15,          // ROW_WIDTH (MT41J256M16: 15)
    parameter int DFI_BANK_W = 3,           // 8 banks
    parameter int NPHASES    = 4,           // DDR3 on S7DDRPHY is 1:4 only
    parameter int PHASE_DATA = 64,          // = 2 x DQ width (DDR3 DDR)
    parameter int PHASE_STRB = PHASE_DATA / 8
) (
    // ---- flat (phase-packed) side: from scoria_top / the char macro -------
    input  logic [DFI_ADDR_W*NPHASES-1:0] dfi_address_flat,
    input  logic [DFI_BANK_W*NPHASES-1:0] dfi_bank_flat,
    input  logic [NPHASES-1:0]            dfi_cas_n_flat,
    input  logic [NPHASES-1:0]            dfi_ras_n_flat,
    input  logic [NPHASES-1:0]            dfi_we_n_flat,
    input  logic [NPHASES-1:0]            dfi_cs_n_flat,
    input  logic [NPHASES-1:0]            dfi_cke_flat,
    input  logic [NPHASES-1:0]            dfi_odt_flat,
    // ONE reset_n for the device, fanned to every phase. scoria drives a single
    // dfi_reset_n_o rather than a per-phase vector, which is right: RESET# is a
    // device-global pin and the PHY serialises it like any other control bit.
    input  logic                          dfi_reset_n,
    input  logic [PHASE_DATA*NPHASES-1:0] dfi_wrdata_flat,
    input  logic [PHASE_STRB*NPHASES-1:0] dfi_wrdata_mask_flat,
    input  logic [NPHASES-1:0]            dfi_wrdata_en_flat,
    input  logic [NPHASES-1:0]            dfi_rddata_en_flat,
    output logic [PHASE_DATA*NPHASES-1:0] dfi_rddata_flat,
    output logic [NPHASES-1:0]            dfi_rddata_valid_flat,

    // ---- per-phase side: to k7ddrphy --------------------------------------
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
    output logic dfi_p0_reset_n, dfi_p1_reset_n,
                 dfi_p2_reset_n, dfi_p3_reset_n,
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

    // Elaboration guards. NPHASES is fixed by the PHY and PHASE_DATA by the
    // DQ width; a mismatch here is the silent misframing described above, so
    // it is caught before it simulates rather than on a board.
    initial begin
        // DDR3 on S7DDRPHY is 1:4 only -- litedram asserts
        // `not (memtype == "DDR3" and nphases == 2)`.
        assert (NPHASES == 4) else
            $fatal(1, "dfi_flat_to_k7ddrphy: NPHASES=%0d, must be 4", NPHASES);
        // PHASE_DATA is 2 x the DQ width, so it is an even number of bytes.
        assert (PHASE_DATA % 16 == 0) else
            $fatal(1, "dfi_flat_to_k7ddrphy: PHASE_DATA=%0d, must be 2 x the DQ width", PHASE_DATA);
    end

    `define DFI_PHASE_SLICE(P)                                                 \
        assign dfi_p``P``_address     = dfi_address_flat[P*DFI_ADDR_W +: DFI_ADDR_W]; \
        assign dfi_p``P``_bank        = dfi_bank_flat   [P*DFI_BANK_W +: DFI_BANK_W]; \
        assign dfi_p``P``_cas_n       = dfi_cas_n_flat  [P];                   \
        assign dfi_p``P``_ras_n       = dfi_ras_n_flat  [P];                   \
        assign dfi_p``P``_we_n        = dfi_we_n_flat   [P];                   \
        assign dfi_p``P``_cs_n        = dfi_cs_n_flat   [P];                   \
        assign dfi_p``P``_cke         = dfi_cke_flat    [P];                   \
        assign dfi_p``P``_odt         = dfi_odt_flat    [P];                   \
        assign dfi_p``P``_reset_n     = dfi_reset_n;  /* DDR3: a real pin */   \
        assign dfi_p``P``_act_n       = 1'b1;         /* ACT_n is DDR4 */      \
        assign dfi_p``P``_wrdata      = dfi_wrdata_flat[P*PHASE_DATA +: PHASE_DATA]; \
        assign dfi_p``P``_wrdata_mask = dfi_wrdata_mask_flat[P*PHASE_STRB +: PHASE_STRB]; \
        assign dfi_p``P``_wrdata_en   = dfi_wrdata_en_flat[P];                 \
        assign dfi_p``P``_rddata_en   = dfi_rddata_en_flat[P];

    `DFI_PHASE_SLICE(0)
    `DFI_PHASE_SLICE(1)
    `DFI_PHASE_SLICE(2)
    `DFI_PHASE_SLICE(3)
    `undef DFI_PHASE_SLICE

    // Read return: repack the per-phase buses into the flat one, phase 0 in the
    // low bits -- the same order the write side slices, so a write and a read
    // of the same address cannot disagree about phase order.
    assign dfi_rddata_flat       = {dfi_p3_rddata, dfi_p2_rddata,
                                    dfi_p1_rddata, dfi_p0_rddata};
    assign dfi_rddata_valid_flat = {dfi_p3_rddata_valid, dfi_p2_rddata_valid,
                                    dfi_p1_rddata_valid, dfi_p0_rddata_valid};

endmodule : dfi_flat_to_k7ddrphy
