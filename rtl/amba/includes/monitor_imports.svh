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
// monitor_pkg::* is intentionally NOT wildcard-imported. It's a pure
// facade that re-declares the same symbols (monitor_packet_t,
// create_monitor_packet, get_packet_type, ...) as wrapper typedefs and
// function forwarders. Verilator tolerated the resulting double-visible
// names; Vivado's stricter elaborator rejects them with Synth 8-8958
// ("X is visible via multiple package imports"). Every symbol
// monitor_pkg exposes is reachable through the four sub-package imports
// above, so dropping the wildcard import costs nothing. If a downstream
// file genuinely needs a monitor_pkg-only helper, fully qualify the
// call (`monitor_pkg::foo(...)`) rather than restoring this import.

`endif // MONITOR_PKG_IMPORTED
