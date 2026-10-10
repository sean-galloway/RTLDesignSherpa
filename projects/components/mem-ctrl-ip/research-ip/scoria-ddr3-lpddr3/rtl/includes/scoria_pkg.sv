// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scoria_pkg
// Purpose: DDR3/LPDDR3 alias for the family common package
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/scoria_has/
//
// Phase 2 (2026-10-10, mem-ctrl-ip reorg): scoria's header anticipated this
// migration — "a shared mem_ctrl_pkg becomes worth the migration when the
// DDR4/LPDDR4 controller starts, and both move together." Both moved. All
// scoria_pkg content was family-shared and now lives in
// common-ip/rtl/includes/mc_common_pkg.sv (family doc 01, Table 1.0; knob
// inventory common-ip/docs/mc_common_pkg_knobs.md). This package remains as
// the import/export shim so scoria RTL's `import scoria_pkg::*;` lines are
// untouched. The legacy 1-bit PHY_TIMING.memtype CSR values are preserved;
// the hwif->family-enum mapping lives at the cast site in scoria_top.sv.
//
// Derived from pumice_pkg (DDR2/LPDDR2).
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

package scoria_pkg;

    import mc_common_pkg::*;
    export mc_common_pkg::*;

endpackage : scoria_pkg
