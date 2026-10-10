// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_pkg
// Purpose: DDR2/LPDDR2-only extensions on top of the family common package
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_has/
//   projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/
//
// Phase 2 (2026-10-10, mem-ctrl-ip reorg): the family-shared types
// (memtype_e, dram_op_e, bank_state_e, page_policy_e, decoded_addr_t, and
// the op-helper functions) moved to common-ip/rtl/includes/mc_common_pkg.sv
// per family doc 01 (common-ip/docs/01_mem_ctrl_pkg.md) and the knob
// inventory common-ip/docs/mc_common_pkg_knobs.md. This package keeps only
// what is pumice-specific. The legacy 1-bit PHY_TIMING.memtype CSR values
// are preserved; the hwif->family-enum mapping lives at the cast site in
// pumice_top.sv.
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

package pumice_pkg;

    import mc_common_pkg::*;
    export mc_common_pkg::*;

    //=========================================================================
    // Address-Map Scheme
    //=========================================================================
    // NOTE: the LIVE addr_mapper no longer uses this enum — it is driven by the
    // single ADDR_MAP.bank_lsb knob (+ hash), and the "schemes" are just settings
    // of it (see rtl/fub/addr_mapper.sv). The enum is retained ONLY because the
    // retired macro/ OLD/ modules (pumice_core_macro, axi_frontend_macro,
    // pumice_config_block) still reference the type in their regression sentinels.

    typedef enum logic [1:0] {
        ADDR_MAP_ROW_MAJOR       = 2'h0,
        ADDR_MAP_BANK_INTERLEAVE = 2'h1,
        ADDR_MAP_XOR_HASH        = 2'h2,
        ADDR_MAP_RSVD            = 2'h3
    } addr_map_scheme_e;

    //=========================================================================
    // ODT Rule (multi-rank)
    //=========================================================================
    // See HAS §3.6 / MAS §2.16.

    typedef enum logic [1:0] {
        ODT_RULE_DEFAULT      = 2'h0,   // Use build-time default
        ODT_RULE_JEDEC_DDR2   = 2'h1,
        ODT_RULE_JEDEC_LPDDR2 = 2'h2,
        ODT_RULE_OFF          = 2'h3    // Forced when NUM_RANKS == 1
    } odt_rule_e;

endpackage : pumice_pkg
