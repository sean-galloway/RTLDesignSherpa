// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_imports
// Purpose: Stream Imports module
//
// Documentation: projects/components/includes/PRD.md
// Subsystem: includes
//
// Author: sean galloway
// Created: 2025-10-18

`ifndef MONITOR_PKG_IMPORTED
`define MONITOR_PKG_IMPORTED
// Import the monitor packages STREAM needs (not the full monitor_pkg).
// monitor_arbiter_pkg is required here because STREAM modules use its
// CORE_ERR_* and CORE_COMPL_* enum constants for MonBus event reporting.
// Compiling both imports in the shared header ensures every consumer
// module sees the constants without needing its own `import` line.
import monitor_common_pkg::*;
import monitor_arbiter_pkg::*;
`endif // MONITOR_PKG_IMPORTED

// Include guard for STREAM package
`ifndef STREAM_PKG_IMPORTED
`define STREAM_PKG_IMPORTED
// Import STREAM package once globally
import stream_pkg::*;
`endif // STREAM_PKG_IMPORTED
