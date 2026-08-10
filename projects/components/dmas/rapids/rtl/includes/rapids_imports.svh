// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_imports
// Purpose: Rapids Imports module
//
// Documentation: projects/components/includes/PRD.md
// Subsystem: includes
//
// Author: sean galloway
// Created: 2025-10-18

// Package imports are guarded so that in a shared compilation scope each
// package is wildcard-imported exactly once. This matters because rapids_pkg
// and stream_pkg (pulled in via the shared apb4todescr kick block on the
// characterization harness) export colliding enum-label names (RD_IDLE, CH_*,
// ...); importing either wildcard more than once into the same scope makes
// those labels ambiguous under Vivado. The guard keeps a single canonical
// import. Any symbol a RAPIDS module needs from a package that a *different*
// import header may have claimed the guard for first must be referenced
// fully-qualified (e.g. monitor_amba4_pkg::AXI_ERR_RESP_SLVERR) rather than
// relying on the wildcard.
`ifndef MONITOR_PKG_IMPORTED
`define MONITOR_PKG_IMPORTED
// Import monitor packages for MonBus types
// monitor_common_pkg provides: PktTypeError, PktTypeCompletion, PROTOCOL_CORE, etc.
// monitor_amba4_pkg provides: AXI_ERR_RESP_SLVERR, AXI_ERR_RESP_DECERR, etc.
// monitor_arbiter_pkg provides: CORE_ERR_*, CORE_COMPL_*, CORE_PERF_* for ctrlrd/ctrlwr engines
import monitor_common_pkg::*;
import monitor_amba4_pkg::*;
import monitor_arbiter_pkg::*;
// NOTE: `import monitor_pkg::*;` intentionally omitted -- its helper
// functions (get_packet_type etc.) duplicate monitor_common_pkg's, and
// Vivado flags the duplicates as ambiguous under wildcard imports.
`endif // MONITOR_PKG_IMPORTED

// Include guard for RAPIDS package
`ifndef RAPIDS_PKG_IMPORTED
`define RAPIDS_PKG_IMPORTED
// Import RAPIDS package once globally
import rapids_pkg::*;
`endif // RAPIDS_PKG_IMPORTED
