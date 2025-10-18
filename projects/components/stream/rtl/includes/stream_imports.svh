//////////////////////////////////////////////////////////////////////////////////
// Company:  Cornami, Inc.
//           Copyright (c) 2025 by Cornami, Inc. All rights reserved.
//
// Engineer: STREAM RTL v1.0 - Common Imports Header
//
// File Name     : stream_imports.svh
// Project Name  : STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
// Target Devices: ASIC/FPGA
// Tool versions : Verilator compatible
// Description   : STREAM Common Imports Header
//                 - Global import of monitor and STREAM packages
//                 - Include guards to prevent multiple imports
//                 - Central location for all package dependencies
//
//////////////////////////////////////////////////////////////////////////////////

// Include guard for monitor package
`ifndef MONITOR_PKG_IMPORTED
`define MONITOR_PKG_IMPORTED
// Import monitor package once globally
import monitor_pkg::*;
`endif // MONITOR_PKG_IMPORTED

// Include guard for STREAM package
`ifndef STREAM_PKG_IMPORTED
`define STREAM_PKG_IMPORTED
// Import STREAM package once globally
import stream_pkg::*;
`endif // STREAM_PKG_IMPORTED
