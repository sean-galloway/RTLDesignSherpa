// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_imports
// Purpose: Monitor Imports module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`ifndef MONITOR_PKG_IMPORTED
`define MONITOR_PKG_IMPORTED

// Import all monitor packages for complete access to types and enum members
// Due to SystemVerilog package import semantics, enum member values need
// direct package import - they don't get re-exported via typedef.
import monitor_common_pkg::*;   // Common types, PROTOCOL_*, PktType*, transaction states
import monitor_amba4_pkg::*;    // AXI4/APB/AXIS event codes (APB_ERR_*, AXI_ERR_*, etc.)
import monitor_amba5_pkg::*;    // AXI5/APB5/AXIS5 extended event codes
import monitor_arbiter_pkg::*;  // ARB/CORE event codes
import monitor_pkg::*;          // Unified wrapper with helper functions

`endif // MONITOR_PKG_IMPORTED
