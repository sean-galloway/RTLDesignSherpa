//////////////////////////////////////////////////////////////////////////////////
// Company:  Cornami, Inc.
//           Copyright (c) 2025 by Cornami, Inc. All rights reserved.
//
// Engineer: RAPIDS RTL v3.0 - Common Imports Header
//
// File Name     : rapids_imports.svh
// Project Name  : Next Generation RAPIDS
// Target Devices: ASIC/FPGA
// Tool versions : Verilator compatible
// Description   : RAPIDS Common Imports Header
//                 - Global import of monitor and RAPIDS packages
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

// Include guard for RAPIDS package
`ifndef RAPIDS_PKG_IMPORTED
`define RAPIDS_PKG_IMPORTED
// Import RAPIDS package once globally
import rapids_pkg::*;
`endif // RAPIDS_PKG_IMPORTED
