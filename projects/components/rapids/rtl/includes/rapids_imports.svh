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

`ifndef MONITOR_PKG_IMPORTED
`define MONITOR_PKG_IMPORTED
// Import monitor packages for MonBus types
// monitor_common_pkg provides: PktTypeError, PktTypeCompletion, PROTOCOL_CORE, etc.
// monitor_amba4_pkg provides: AXI_ERR_RESP_SLVERR, AXI_ERR_RESP_DECERR, etc.
// monitor_arbiter_pkg provides: CORE_ERR_*, CORE_COMPL_*, CORE_PERF_* for ctrlrd/ctrlwr engines
// monitor_pkg provides: monitor_packet_t, helper functions
import monitor_common_pkg::*;
import monitor_amba4_pkg::*;
import monitor_arbiter_pkg::*;
import monitor_pkg::*;
`endif // MONITOR_PKG_IMPORTED

// Include guard for RAPIDS package
`ifndef RAPIDS_PKG_IMPORTED
`define RAPIDS_PKG_IMPORTED
// Import RAPIDS package once globally
import rapids_pkg::*;
`endif // RAPIDS_PKG_IMPORTED
