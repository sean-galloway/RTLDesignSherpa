// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_pkg
// Purpose: DDR4/LPDDR4 alias for the family common package
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_has/
//
// Phase 2 (2026-10-10, mem-ctrl-ip reorg): andesite_pkg carried the FAMILY
// design (family doc 01, Table 1.0) from creation — its header deferred the
// family migration to andesite RTL bring-up per that doc's conditions. The
// conditions are met (Phase 2 is the migration) and andesite's exact
// encodings are now the family encodings in
// common-ip/rtl/includes/mc_common_pkg.sv (knob inventory common-ip/docs/
// mc_common_pkg_knobs.md). This package remains as the import/export shim so
// andesite RTL is untouched. The legacy 1-bit PHY_TIMING.memtype CSR values
// (0=DDR4/1=LPDDR4 per andesite's RDL) are preserved; the hwif->family-enum
// mapping lives at the cast site in andesite_top.sv.
//
// Derived from scoria_pkg (DDR3/LPDDR3).
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

package andesite_pkg;

    import mc_common_pkg::*;
    export mc_common_pkg::*;

endpackage : andesite_pkg
