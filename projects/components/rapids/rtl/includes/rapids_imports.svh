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
// Import monitor package once globally
import monitor_pkg::*;
`endif // MONITOR_PKG_IMPORTED

// Include guard for RAPIDS package
`ifndef RAPIDS_PKG_IMPORTED
`define RAPIDS_PKG_IMPORTED
// Import RAPIDS package once globally
import rapids_pkg::*;
`endif // RAPIDS_PKG_IMPORTED
